#!/usr/bin/env python3
"""Obtain a digest-pinned Linux x86-64 tool from tools.lock.json and print its path.

Archives are stored under .deps/archives by digest and verified on every use, so a cached
archive cannot differ from the lock. Each tool is unpacked, or built from its pinned source,
once under .deps/tools.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DEPS = ROOT / ".deps"
MARKER = "archive.sha256"
BUILT = ("lean4export", "nanoda")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fetch(pin: dict[str, str]) -> Path:
    """Return the archive of a pin, downloading it first when it is not stored yet."""
    archive = DEPS / "archives" / pin["sha256"]
    if not archive.exists():
        archive.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=archive.parent) as temp:
            partial = Path(temp) / "download"
            subprocess.run(["curl", "--proto", "=https", "--tlsv1.2", "--fail", "--location", "--retry", "3",
                            "--silent", "--show-error", "--output", str(partial), pin["url"]], check=True)
            partial.rename(archive)
    if digest(archive) != pin["sha256"]:
        archive.unlink()
        raise SystemExit(f"digest mismatch for {pin['url']}")
    return archive


def unpack(pin: dict[str, str], archive: Path, target: Path) -> None:
    with tempfile.TemporaryDirectory(dir=target.parent) as temp:
        content = Path(temp) / "content"
        content.mkdir()
        if pin["url"].endswith(".tar.zst"):
            with subprocess.Popen(["zstd", "--decompress", "--stdout", str(archive)],
                                  stdout=subprocess.PIPE) as zstd:
                if zstd.stdout is None:
                    raise SystemExit("cannot read zstd output")
                with tarfile.open(fileobj=zstd.stdout, mode="r|") as tar:
                    tar.extractall(content, filter="data")
            if zstd.returncode:
                raise SystemExit(f"cannot decompress {archive}")
        else:
            with tarfile.open(archive) as tar:
                tar.extractall(content, filter="data")
        (content / MARKER).write_text(pin["sha256"] + "\n")
        os.rename(content, target)


def build(name: str, lock: dict[str, dict[str, str]], archive: Path, target: Path) -> None:
    """Build a tool from its source and keep only the binary. The build runs in the user's cache
    directory, outside the repository and the shared temporary directory, so that no configuration
    found there (.cargo, a Cargo workspace) takes part."""
    pin = lock[name]
    cache = Path(os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache").resolve()
    if cache == ROOT or ROOT in cache.parents:
        raise SystemExit(f"{cache} is inside the repository; tools are built outside it")
    cache.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="dn-tool-", dir=cache) as temp:
        unpack(pin, archive, Path(temp) / "source")
        (source,) = [p for p in (Path(temp) / "source").iterdir() if p.is_dir()]
        if name == "lean4export":
            toolchain = f"leanprover/lean4:{lock['lean']['version']}"
            if (source / "lean-toolchain").read_text().strip() != toolchain:
                raise SystemExit(f"lean4export {pin['version']} is not pinned to {toolchain}")
            command = [str(lean_home(lock) / "bin" / "lake"), "build", "lean4export"]
            env = {**os.environ, "LAKE_ARTIFACT_CACHE": "false"}
        else:
            cargo = shutil.which("cargo")
            if cargo is None:
                raise SystemExit("building nanoda needs cargo (rustup) on PATH")
            shutil.copy(ROOT / "rust-toolchain.toml", source)
            command = [cargo, "build", "--release", "--locked"]
            env = {k: v for k, v in os.environ.items() if k != "RUSTUP_TOOLCHAIN"}
            env["CARGO_TARGET_DIR"] = str(source / "target")
        subprocess.run(command, cwd=source, env=env, check=True, stdout=sys.stderr)
        with tempfile.TemporaryDirectory(dir=target.parent) as staging:
            content = Path(staging) / "content"
            content.mkdir()
            shutil.copy2(source / pin["binary"], content)
            (content / MARKER).write_text(pin["sha256"] + "\n")
            os.rename(content, target)


def install(name: str, lock: dict[str, dict[str, str]]) -> Path:
    pin = lock[name]
    target = DEPS / "tools" / f"{name}-{pin['version']}"
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        if name in BUILT:
            build(name, lock, fetch(pin), target)
        else:
            unpack(pin, fetch(pin), target)
    elif (target / MARKER).read_text().strip() != pin["sha256"]:
        raise SystemExit(f"{target} does not match the lock; remove it")
    return target


def lean_home(lock: dict[str, dict[str, str]]) -> Path:
    """The verified Lean toolchain, which must be the one lean-toolchain names."""
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    if toolchain != f"leanprover/lean4:{lock['lean']['version']}":
        raise SystemExit(f"lean-toolchain names {toolchain}, but the lock pins {lock['lean']['version']}")
    (home,) = [p for p in install("lean", lock).iterdir() if p.is_dir()]
    return home


def main() -> None:
    lock = json.loads((ROOT / "tools.lock.json").read_text())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tool", choices=sorted(name for name in lock if name != "format"))
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        parser.error("the pinned tools target Linux x86-64")
    tracked = subprocess.run(["git", "--icase-pathspecs", "ls-files", "--", ".deps"], cwd=ROOT, text=True,
                             capture_output=True, check=True).stdout
    if tracked:
        raise SystemExit(".deps is tracked by git; pinned tools must come from their archives")
    pin = lock[args.tool]
    target = install(args.tool, lock)
    if args.tool == "cake":
        source = target / "cake-x64-64"
        subprocess.run(["make", "-C", str(source), "cake", "LDFLAGS=-Wl,-z,noexecstack"],
                       check=True, stdout=sys.stderr)
        print(source / "cake")
    elif args.tool == "elan":
        subprocess.run([str(target / "elan-init"), "-y", "--no-modify-path", "--default-toolchain", "none"],
                       check=True, stdout=sys.stderr)
    elif args.tool == "lean":
        home = lean_home(lock)
        toolchain = f"leanprover/lean4:{pin['version']}"
        installed = subprocess.run(["elan", "toolchain", "list"], capture_output=True, text=True,
                                   check=True).stdout.split()
        if toolchain not in installed:
            subprocess.run(["elan", "toolchain", "link", toolchain, str(home)], check=True, stdout=sys.stderr)
        prefix = subprocess.run(["lean", f"+{toolchain}", "--print-prefix"], capture_output=True, text=True,
                                check=True).stdout.strip()
        if Path(prefix).resolve() != home.resolve():
            raise SystemExit(f"elan resolves {toolchain} to {prefix}, not the verified {home}")
        print(home)
    elif args.tool in BUILT:
        print(target / Path(pin["binary"]).name)
    else:
        print(target / pin["binary"])


if __name__ == "__main__":
    main()
