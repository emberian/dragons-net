# SPDX-License-Identifier: AGPL-3.0-or-later
"""What the native lanes share: running `dn-compiler` and the Pancake compiler, the rule that any
diagnostic fails, the namespace of exported symbols, linking with the hardening flags and reading
them back off the binary, the phrases the documents have to carry, and the report every lane
writes.

A check that refuses raises `LaneError`. `lane_main` ends the lane with that one reason and status
1; any other exception is a defect of the lane itself and keeps its traceback.
"""
from __future__ import annotations

import argparse
from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass, field
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
NATIVE = ROOT / "native"
DN_COMPILER = ROOT / ".lake/build/bin/dn-compiler"
RECORD = ROOT / "backend/bootstrap-record.json"
# Hardening the linked binaries: position-independent with full RELRO, fortified library
# calls, stack protection and control-flow protection. The generated assembly is
# position-independent, so nothing here needs a fixed load address.
HARDENING = ["-O2", "-Wall", "-Wextra", "-Werror", "-fPIE", "-pie",
             "-Wl,-z,relro,-z,now", "-Wl,-z,noexecstack",
             "-D_FORTIFY_SOURCE=3", "-fstack-protector-strong", "-fstack-clash-protection",
             "-fcf-protection=full", "-Wformat=2"]
# The runtime every host links against.
RUNTIME = [NATIVE / "cake_runtime.c", NATIVE / "cake_runtime.h", NATIVE / "host.h"]
# Global symbols the Cake runtime defines in every generated assembly file.
RUNTIME_SYMBOLS = {"cake_bitmaps_buffer_begin", "cake_bitmaps_buffer_end",
                   "cake_codebuffer_begin", "cake_codebuffer_end", "cake_text_begin",
                   "cml_heap", "cml_main", "cml_stack", "cml_stackend"}
# Must stay equal to Checked.exportPrefix; a test holds the two together.
EXPORT_PREFIX = "dn_"


class LaneError(Exception):
    """A check refused what it checks, or could not be made."""


class Diagnostics(LaneError):
    """The Pancake compiler printed a diagnostic, which the lanes treat as a failure."""


def digest(path: Path | str) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def cc() -> str:
    return os.environ.get("CC", "cc")


def loud(command: list[str], *, timeout: int, what: str, stdin: str | None = None) -> str:
    """Run a step and, when it fails, say what it printed rather than only its status."""
    done = subprocess.run(command, input=stdin, capture_output=True, text=True, timeout=timeout,
                          check=False)
    if done.returncode:
        raise LaneError(f"{what} failed with status {done.returncode}:\n{done.stdout}{done.stderr}")
    return done.stdout


def emit(*args: str, stdin: str | None = None, timeout: int = 600,
         compiler: Path = DN_COMPILER) -> str:
    """What `dn-compiler ARGS` prints."""
    return loud([str(compiler), *args], stdin=stdin, timeout=timeout, what=f"dn-compiler {args[0]}")


def pancake(cake: str, source: Path, *, explore: bool = False, warnings: bool = True,
            timeout: int = 300) -> bytes:
    """What the Pancake compiler prints for `source`. A warning (a redeclared variable, say) leaves
    the exit status at zero, so any diagnostic fails; with `warnings` off, for a source whose
    warnings are beside what is asked of it, only the status does, and nothing is silenced."""
    options = ["--explore"] if explore else []
    with source.open("rb") as inp:
        done = subprocess.run([cake, "--pancake", *options, "--main_return=true"], stdin=inp,
                              capture_output=True, timeout=timeout, check=False)
    if done.returncode or (warnings and done.stderr):
        raise Diagnostics(f"{source.name} compiled with diagnostics (status {done.returncode}):\n"
                          f"{done.stderr.decode(errors='replace')}")
    return done.stdout


def check_symbols(assembly: Path) -> None:
    """An exported name becomes a global C symbol. Anything outside the runtime's own set has to
    stay in this project's namespace, or it can displace a libc function of the host it is linked
    into."""
    obj = assembly.with_suffix(".o")
    loud([cc(), "-c", str(assembly), "-o", str(obj)], timeout=60, what=f"assembling {assembly.name}")
    listing = loud(["nm", "--defined-only", "--extern-only", str(obj)], timeout=60,
                   what=f"reading symbols of {obj.name}")
    symbols = {line.split()[-1] for line in listing.splitlines() if line.strip()}
    if not symbols & RUNTIME_SYMBOLS:
        raise LaneError(f"{obj.name} carries no runtime symbol; the check is looking at nothing")
    stray = sorted(s for s in symbols - RUNTIME_SYMBOLS if not s.startswith(EXPORT_PREFIX))
    if stray:
        raise LaneError(f"{assembly.name} exports symbols outside the project namespace: {stray}")


def assemble(cake: str, source: Path, *, timeout: int = 300) -> Path:
    """Compile `source` to assembly beside it, with no diagnostic and no stray export."""
    assembly = source.with_suffix(".S")
    assembly.write_bytes(pancake(cake, source, timeout=timeout))
    check_symbols(assembly)
    return assembly


def hardened(binary: Path) -> None:
    """The linked binary must carry the protections it was built with, read off the file."""
    name = binary.name
    header = loud(["readelf", "-hdl", str(binary)], timeout=60, what=f"reading {name}")
    symbols = loud(["nm", "-u", str(binary)], timeout=60, what=f"reading symbols of {name}")
    if "DYN (" not in header:
        raise LaneError(f"{name} is not position-independent")
    if "BIND_NOW" not in header:
        raise LaneError(f"{name} was linked without BIND_NOW")
    if "GNU_RELRO" not in header:
        raise LaneError(f"{name} has no read-only-after-relocation segment")
    if "TEXTREL" in header:
        raise LaneError(f"{name} needs text relocations")
    stack = [line for line in header.splitlines() if "GNU_STACK" in line]
    if not stack or "RWE" in stack[0]:
        raise LaneError(f"{name} does not declare a non-executable stack")
    if "__stack_chk_fail" not in symbols:
        raise LaneError(f"{name} was built without stack protection")
    if not any(check in symbols for check in ("_chk@", "_chk")):
        raise LaneError(f"{name} was built without fortified library calls")


def compile_object(source: Path, obj: Path, *, includes: Iterable[Path] = ()) -> Path:
    """One C file, compiled with the hardening flags, to be linked many times."""
    loud([cc(), *HARDENING, "-g", *(f"-I{d}" for d in (NATIVE, *includes)), "-c", str(source),
          "-o", str(obj)], timeout=120, what=f"compiling {source.name}")
    return obj


def link(binary: Path, sources: Iterable[Path], *, includes: Iterable[Path] = (),
         timeout: int = 120, check: bool = True) -> Path:
    """Link with the hardening flags and debug information; `check` reads the protections back
    off the binary, which a lane linking the same host many times needs to do once."""
    loud([cc(), *HARDENING, "-g", *(f"-I{d}" for d in (NATIVE, *includes)), *map(str, sources),
          "-o", str(binary)], timeout=timeout, what=f"linking {binary.name}")
    if check:
        hardened(binary)
    return binary


def require_quoted(quotes: Mapping[str, Iterable[str]]) -> None:
    """The documents quote what this run measured: each file has to carry each phrase."""
    for name, phrases in quotes.items():
        text = (ROOT / name).read_text()
        for phrase in phrases:
            if phrase not in text:
                raise LaneError(f"{name} does not say {phrase!r}")


def require_platform(parser: argparse.ArgumentParser) -> None:
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        parser.error("the native lanes run on Linux x86-64")


def given_cake(parser: argparse.ArgumentParser, name: str | None) -> str:
    """The compiler named by --cake or CAKE; there is no interpreted fallback."""
    cake = shutil.which(name or "")
    if not cake:
        parser.error("provide --cake or CAKE")
    return cake


def release_cake() -> str:
    """The pinned release compiler, installed from its archive if it is not there yet."""
    return loud([sys.executable, str(ROOT / "scripts/bootstrap_tool.py"), "cake"], timeout=7200,
                what="installing the release compiler").strip()


def bootstrapped() -> str:
    """The compiler built from the patched source, if it is the one the record describes."""
    record = json.loads(RECORD.read_text())
    cake = ROOT / record["cake_path"]
    if not cake.is_file():
        raise LaneError(f"{cake} has not been built here; see backend/README.md")
    if digest(cake) != record["cake_sha256"]:
        raise LaneError(f"{cake} is not the compiler {RECORD.name} records")
    return str(cake)


@dataclass
class Report:
    """What a lane found. `lane_main` adds what every report carries: the status, the platform,
    the digests of the Pancake compiler, of `dn-compiler` when it printed what was checked, and of
    the host sources, and how long the run took."""
    status: str
    cake: str | None
    hosts: list[Path] = field(default_factory=list)
    body: dict[str, Any] = field(default_factory=dict)
    printed_by_dn_compiler: bool = True


def lane_main(name: str, out: Path, run: Callable[[], Report]) -> None:
    """Run a lane. The last report goes first, so a failed run leaves none behind; a refusal ends
    the lane with `DN NAME: reason`."""
    started = time.monotonic()
    out.mkdir(parents=True, exist_ok=True)
    path = out / "report.json"
    path.unlink(missing_ok=True)
    try:
        report = run()
    except LaneError as error:
        raise SystemExit(f"DN {name}: {error}") from None
    head = {"status": report.status, "platform": platform.platform(),
            "cake_sha256": digest(report.cake) if report.cake else None,
            "dn_compiler_sha256": digest(DN_COMPILER) if report.printed_by_dn_compiler else None,
            "host_sha256": {str(p.relative_to(ROOT)): digest(p) for p in report.hosts},
            "seconds": round(time.monotonic() - started, 1)}
    path.write_text(json.dumps({**head, **report.body}, indent=2) + "\n")
    print(path.read_text(), end="")
