"""
Build the `eth_cryptography_specs._native` CPython extension.

Strategy: compile every Lean-generated `.c.o.export` object into the
extension, dynamically link against Lean's `libleanshared`, and statically
link the small native dependencies available in the active Lean toolchain
(currently libgmp and libuv when present). Wheel repair tools bundle the
Lean shared library for distribution, while local source builds find it via
the runtime library path configured below.

The build runs `lake build` first to (re-)generate the Lean object
files, then hands the full list to setuptools.Extension.
"""
import platform
import subprocess
from glob import glob
from pathlib import Path

from setuptools import setup, Extension
from setuptools.command.build_ext import build_ext


REPO_ROOT = Path(__file__).parent.resolve()
BINDINGS  = REPO_ROOT / "bindings" / "python"
LAKE_IR   = REPO_ROOT / ".lake" / "build" / "ir"
# The shared SSZ package builds outside the root package's object directory.
SSZ_IR    = REPO_ROOT / ".lake" / "packages" / "ssz" / "lean" / ".lake" / "build" / "ir"


def _lean_sysroot() -> Path | None:
    """Active Lean toolchain prefix (`lean --print-prefix`), or `None`
    if no `lean` is on PATH. The sdist build doesn't need Lean — it just
    tars up source files — so we tolerate its absence at metadata time
    and only require it when `LakeThenBuild.run` actually compiles the
    extension."""
    try:
        out = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None
    return Path(out)


def _collect_lean_objects() -> list[str]:
    """Every `.c.o.export` Lake produced for the package and the SSZ codec."""
    objects = glob(str(LAKE_IR / "**" / "*.c.o.export"), recursive=True)
    objects += glob(str(SSZ_IR / "**" / "*.c.o.export"), recursive=True)
    return sorted(objects)


def _lean_runtime_link(sysroot: Path) -> tuple[list[str], list[str], list[str]]:
    """How to bring the Lean runtime into our shared extension. Returns
    `(extra_objects, library_dirs, libraries)` to merge into the `Extension`.

    We dynamically link against `libleanshared` on every platform: the
    static archives Lean ships (`libleanrt.a`, `libInit.a`, `libStd.a`)
    aren't `-fPIC` on Linux and refuse to link into a shared object,
    and using one strategy across platforms keeps the build simple.
    cibuildwheel's `auditwheel` (Linux) / `delocate` (macOS) passes
    bundle the runtime `.so` / `.dylib` into the wheel and patch RPATH,
    so installed wheels are self-contained — the user does NOT need
    elan or any Lean toolchain on their machine. `libgmp.a` /
    `libuv.a` stay as static inputs."""
    gmp_uv = [
        str(p) for p in (sysroot / "lib" / "libgmp.a",
                         sysroot / "lib" / "libuv.a") if p.exists()
    ]
    return gmp_uv, [str(sysroot / "lib" / "lean")], ["leanshared"]


class LakeThenBuild(build_ext):
    """Run `lake build` to (re-)generate the Lean object files before
    handing things to setuptools."""

    def run(self):
        subprocess.check_call(["lake", "build"], cwd=str(REPO_ROOT))
        sysroot = _lean_sysroot()
        if sysroot is None:
            raise RuntimeError(
                "lean toolchain not found on PATH; install elan before "
                "building the C extension"
            )
        # Re-resolve include_dirs and link inputs lazily: at metadata time
        # (e.g. `python -m build --sdist`) Lean may not be installed.
        runtime_objs, library_dirs, libraries = _lean_runtime_link(sysroot)
        for ext in self.extensions:
            if str(sysroot / "include") not in ext.include_dirs:
                ext.include_dirs.append(str(sysroot / "include"))
            ext.extra_objects = _collect_lean_objects() + runtime_objs
            for d in library_dirs:
                if d not in ext.library_dirs:
                    ext.library_dirs.append(d)
                # Also add to runtime_library_dirs so local dev (without
                # auditwheel) finds libleanshared at runtime via RPATH.
                if d not in ext.runtime_library_dirs:
                    ext.runtime_library_dirs.append(d)
            for lib in libraries:
                if lib not in ext.libraries:
                    ext.libraries.append(lib)
        super().run()


def _make_extension() -> Extension:
    extra_link_args: list[str] = []
    libraries: list[str] = []

    if platform.system() == "Darwin":
        # libleancpp is C++ — drag in libc++.
        libraries.append("c++")
    else:
        libraries.append("stdc++")
        # On Linux, Lean's symbols use thread-local storage and pthreads.
        libraries.append("pthread")
        libraries.append("dl")
        libraries.append("m")

    # The Lean-toolchain include dir and `.c.o.export` objects are appended
    # in `LakeThenBuild.run`. We don't resolve them here so that
    # metadata-only invocations (sdist) work without elan installed.
    return Extension(
        name="eth_cryptography_specs._native",
        sources=[
            "bindings/python/module.c",
            "bindings/python/kzg.c",
            "bindings/python/bls.c",
        ],
        include_dirs=["bindings/python"],
        extra_objects=[],
        libraries=libraries,
        extra_link_args=extra_link_args,
    )


setup(
    package_dir={"": "bindings/python"},
    packages=["eth_cryptography_specs", "eth_cryptography_specs.kzg", "eth_cryptography_specs.bls"],
    ext_modules=[_make_extension()],
    cmdclass={"build_ext": LakeThenBuild},
)
