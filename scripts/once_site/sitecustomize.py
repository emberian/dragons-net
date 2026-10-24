# SPDX-License-Identifier: AGPL-3.0-or-later
"""Loaded by each Python a check runs under scripts/once.py: a directory imports search is asked
for the names an import looks for, one at a time, instead of being listed whole, so that the trace
holds the modules found and those looked for in vain, and a file no import names is no input. A
finder other than the one of Python 3.12 is left as it is, and lists the directory, which is never
unsound. The sitecustomize this one hides runs after it."""
from importlib import machinery
import importlib.util
import os
import sys


class Probed:
    """A directory's names, each looked up when asked for."""

    def __init__(self, path: str) -> None:
        self.path = path

    def __contains__(self, name: object) -> bool:
        return isinstance(name, str) and os.path.lexists(os.path.join(self.path, name))  # noqa: PTH118


class ProbingFinder(machinery.FileFinder):
    """Python's finder of modules in a directory, its cache of the directory's names `Probed`."""

    def _fill_cache(self) -> None:
        self._path_cache = Probed(self.path)
        self._relaxed_path_cache = Probed(self.path)


def install() -> None:
    if sys.version_info[:2] != (3, 12) or not hasattr(machinery.FileFinder, "_fill_cache"):
        return
    loaders = [(machinery.ExtensionFileLoader, machinery.EXTENSION_SUFFIXES),
               (machinery.SourceFileLoader, machinery.SOURCE_SUFFIXES),
               (machinery.SourcelessFileLoader, machinery.BYTECODE_SUFFIXES)]
    for k, hook in enumerate(sys.path_hooks):
        if getattr(hook, "__qualname__", "").startswith("FileFinder.path_hook."):
            sys.path_hooks[k] = ProbingFinder.path_hook(*loaders)
            sys.path_importer_cache.clear()
            return


def chained() -> None:
    """The sitecustomize further on the path, run as Python would have run it."""
    here = os.path.dirname(os.path.abspath(__file__))  # noqa: PTH100, PTH120
    rest = [p for p in sys.path if os.path.abspath(p or ".") != here]  # noqa: PTH100
    spec = machinery.PathFinder.find_spec("sitecustomize", rest)
    if spec is not None and spec.loader is not None:
        spec.loader.exec_module(importlib.util.module_from_spec(spec))


install()
chained()
