#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Obtain a digest-pinned Linux x86-64 tool from tools.lock.json and print its path.

Archives are stored under .deps/archives by digest and verified on every use, so a cached
archive cannot differ from the lock. Each tool is unpacked, or built from its pinned source,
once under .deps/tools.
"""
from __future__ import annotations

import argparse
import functools
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
MANIFEST = "tree.sha256"
BUILT = ("lean4export", "nanoda", "cake", "polyml", "abnfgen", "lazyfs", "libfiu")
# Built tools kept as the whole tree their build installs, because the binary alone is not
# usable: Poly/ML needs its libraries and the basis library it loads at run time.
INSTALLED = ("polyml",)
# Built tools kept as these files of their source tree, side by side under the names given:
# LazyFS with the cache library it loads from beside itself; libfiu as its library, under the
# name a program links with and the one it loads, its headers and the preload that enables
# points of failure from outside.
KEPT = {"lazyfs": {"lazyfs": "lazyfs/build/lazyfs", "libpcache.so.0": "libs/libpcache/build/libpcache.so.0"},
        "libfiu": {"libfiu.so": "libfiu/libfiu.so.1.2", "libfiu.so.0": "libfiu/libfiu.so.1.2",
                   "fiu.h": "libfiu/fiu.h", "fiu-local.h": "libfiu/fiu-local.h",
                   "fiu-control.h": "libfiu/fiu-control.h",
                   "fiu_run_preload.so": "preload/run/fiu_run_preload.so"}}


def jobs() -> int:
    """How many build jobs to run: `DN_BUILD_JOBS`, or the cores this process may use.

    `os.cpu_count()` reports the machine's cores, not the ones a container or a taskset
    allows, and a build that ignores the limit competes with itself.
    """
    requested = os.environ.get("DN_BUILD_JOBS")
    if requested and requested.isdigit() and int(requested) > 0:
        return int(requested)
    return len(os.sched_getaffinity(0))


def digest(path: Path) -> str:
    """Content hash, read in chunks: some pinned archives and shared libraries are large."""
    total = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            total.update(chunk)
    return total.hexdigest()


@functools.cache
def tree_digest(path: Path) -> str:
    """One digest over an unpacked tool: every entry's kind, name, mode and content.

    The archive is verified once, when it is downloaded; this is what makes a
    stored tree verifiable on every later use, so a tool that was edited or
    truncated after installation is refused instead of executed. The manifest is
    written beside the tool at install time, not derived from the lock, so it
    answers "still what was installed", not "installed from the pinned archive".

    One walk of the Lean toolchain is seconds, and a single run asks for the same
    tool more than once, so the answer is kept.
    """
    total = hashlib.sha256()
    for item in sorted(path.rglob("*"), key=lambda entry: entry.relative_to(path).as_posix()):
        relative = item.relative_to(path).as_posix()
        if relative == MANIFEST:
            continue
        if item.is_symlink():
            total.update(f"l {relative} {item.readlink()}\n".encode())
        elif item.is_dir():
            total.update(f"d {relative}\n".encode())
        else:
            executable = "x" if os.access(item, os.X_OK) else "-"
            total.update(f"f {relative} {executable} {digest(item)}\n".encode())
    return total.hexdigest()


def seal(content: Path, pin: dict[str, str]) -> None:
    """Record what the tool was built from and what it consists of."""
    (content / MARKER).write_text(pin["sha256"] + "\n")
    (content / MANIFEST).write_text(tree_digest(content) + "\n")


def fetch(pin: dict[str, str]) -> Path:
    """Return the archive of a pin, downloading it first when it is not stored yet."""
    archive = DEPS / "archives" / pin["sha256"]
    if not archive.exists():
        archive.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=archive.parent) as temp:
            partial = Path(temp) / "download"
            # Release downloads fail with 5xx for minutes at a time; curl doubles its wait from a
            # second, so eight tries span about four minutes.
            subprocess.run(["curl", "--proto", "=https", "--proto-redir", "=https", "--tlsv1.2",
                            "--fail", "--location", "--retry", "8", "--retry-max-time", "600",
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
        seal(content, pin)
        content.rename(target)


def build(name: str, lock: dict[str, dict[str, str]], archive: Path, target: Path) -> None:
    """Build a tool from its source and keep the binary, or the installed tree. The build runs in
    the user's cache directory, outside the repository and the shared temporary directory, so that
    no configuration found there (.cargo, a Cargo workspace) takes part."""
    pin = lock[name]
    cache = Path(os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache").resolve()
    if cache == ROOT or ROOT in cache.parents:
        raise SystemExit(f"{cache} is inside the repository; tools are built outside it")
    cache.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="dn-tool-", dir=cache) as temp:
        unpack(pin, archive, Path(temp) / "source")
        (source,) = [p for p in (Path(temp) / "source").iterdir() if p.is_dir()]
        prefix = Path(temp) / "prefix"
        if name == "polyml":
            # --prefix is baked into the binary: Poly/ML looks for its basis library below it,
            # so the tree is configured for where it will finally live, not for the scratch
            # directory it is built in. The other two flags decide what the pin means: GMP is
            # detected by default, so the same pinned source would give a different arbitrary
            # precision backend on a machine that has its headers, and `intinf-as-int` is what
            # the prover's own CI builds with.
            configure = ["./configure", f"--prefix={target}", "--without-gmp",
                         "--enable-intinf-as-int"]
            subprocess.run(configure, cwd=source, check=True, stdout=sys.stderr)
            command = ["make", f"-j{jobs()}", "install", f"DESTDIR={prefix}"]
            env = dict(os.environ)
        elif name == "abnfgen":
            # The archive ships a Makefile configured on its author's machine; configure writes
            # one for this one.
            subprocess.run(["./configure"], cwd=source, check=True, stdout=sys.stderr)
            command = ["make", f"-j{jobs()}", "abnfgen"]
            env = dict(os.environ)
        elif name == "lazyfs":
            # Its cache library fetches toml11 and spdlog when it is configured: they are put from
            # their pins where that fetch leaves them, which is also where LazyFS's own build looks
            # for spdlog, and nothing may be fetched. Both are linked with the rpath they are kept
            # with, beside each other.
            cache_lib = source / "libs" / "libpcache"
            for dep, fetched in (("toml11", "toml"), ("spdlog", "spdlog")):
                unpack(lock[dep], fetch(lock[dep]), Path(temp) / dep)
                (tree,) = [p for p in (Path(temp) / dep).iterdir() if p.is_dir()]
                (cache_lib / "build" / "_deps").mkdir(parents=True, exist_ok=True)
                tree.rename(cache_lib / "build" / "_deps" / f"{fetched}-src")
            rpath = ["-DCMAKE_BUILD_WITH_INSTALL_RPATH=ON", "-DCMAKE_INSTALL_RPATH=$ORIGIN"]
            for step in (["cmake", "-S", str(cache_lib), "-B", str(cache_lib / "build"), *rpath,
                          "-DFETCHCONTENT_FULLY_DISCONNECTED=ON"],
                         ["cmake", "--build", str(cache_lib / "build"), f"-j{jobs()}"],
                         ["cmake", "-S", str(source / "lazyfs"), "-B", str(source / "lazyfs" / "build"),
                          *rpath, "-DLAZYFS_BUILD_TESTS=OFF"]):
                subprocess.run(step, cwd=source, check=True, stdout=sys.stderr)
            command = ["cmake", "--build", str(source / "lazyfs" / "build"), f"-j{jobs()}"]
            env = dict(os.environ)
        elif name == "libfiu":
            # The library and the preload that enables points; not the preloads that wrap POSIX
            # calls, which the host's points of failure stand in for.
            subprocess.run(["make", "-C", "libfiu", "libs"], cwd=source, check=True, stdout=sys.stderr)
            command = ["make", "-C", "preload/run", "fiu_run_preload.so"]
            env = dict(os.environ)
        elif name == "cake":
            command = ["make", "-C", str(source), "cake", "LDFLAGS=-Wl,-z,noexecstack"]
            env = dict(os.environ)
        elif name == "lean4export":
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
        # The staging directory is beside the tool, so what is sealed is renamed into place on
        # the same filesystem: a half-installed tool is never left where the next run trusts it.
        with tempfile.TemporaryDirectory(dir=target.parent) as staging:
            content = Path(staging) / "content"
            if name in INSTALLED:
                # `make install` wrote the tree under DESTDIR at the prefix it was configured
                # for, which is where the tool is about to live.
                shutil.copytree(prefix / target.relative_to(target.anchor), content, symlinks=True)
            else:
                content.mkdir()
                # The pin names the binary inside the source tree; only that file is kept, or the
                # files the tool is kept as.
                for kept, built in KEPT.get(name, {Path(pin["binary"]).name: pin["binary"]}).items():
                    shutil.copy2(source / built, content / kept)
            seal(content, pin)
            content.rename(target)


def install(name: str, lock: dict[str, dict[str, str]]) -> Path:
    pin = lock[name]
    target = DEPS / "tools" / f"{name}-{pin['version']}"
    if target.exists():
        if (target / MARKER).read_text().strip() != pin["sha256"]:
            raise SystemExit(f"{target} does not match the lock; remove it")
        if not (target / MANIFEST).exists():
            # Installed before the stored tree was sealed: redo it from the
            # archive, which is still verified by its digest.
            shutil.rmtree(target)
        elif (target / MANIFEST).read_text().strip() != tree_digest(target):
            raise SystemExit(f"{target} has changed since it was installed; remove it")
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        if name in BUILT:
            build(name, lock, fetch(pin), target)
        else:
            unpack(pin, fetch(pin), target)
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
    if args.tool == "elan":
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
    elif args.tool in BUILT and args.tool not in INSTALLED:
        # Only the binary was kept, so the path it had in its source tree is gone.
        print(target / Path(pin["binary"]).name)
    else:
        # A pin with no binary is a source another tool is built with: its unpacked tree.
        print(target / pin.get("binary", "."))


if __name__ == "__main__":
    main()
