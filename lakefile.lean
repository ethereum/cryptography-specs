import Lake
open Lake DSL System

/-!
Lake build for `EthCryptographySpecs`.

The package is pure Lean — no external C dependencies. Lake produces:

* per-Lean-module `.c.o.export` object files in `.lake/build/ir/`,
* per-module `.olean` files in `.lake/build/lib/lean/`.

The Python C extension under `bindings/python/` is built by `setup.py`
(not Lake): it enumerates the `.c.o.export` files and the Lean
toolchain's static archives and statically links them all into a single
self-contained Python extension.
-/

package «EthCryptographySpecs» where
  moreLeancArgs := #["-fPIC"]

require "leanprover-community" / "mathlib" @ git "v4.29.1"

-- Pin the shared SSZ codec so the wire format has one implementation.
require ssz from git "https://github.com/ethereum/ssz-specs" @
  "a23a2392ffffdd72caefb12f57b7ebd0c9a49de5" / "lean"

@[default_target]
lean_lib «EthCryptographySpecs» where
  precompileModules := true

/-- Proofs about the specification. A separate library (rooted at
`EthCryptographySpecs/Proofs.lean`) so the executable spec never depends
on it. `precompileModules` is off: theorems produce no code, and this
keeps proof object files out of the Python extension link. -/
@[default_target]
lean_lib «Proofs» where
  roots := #[`EthCryptographySpecs.Proofs]
  precompileModules := false

/-- Byte-level regression tests pin the consensus wire order and exact-length rejection. -/
lean_exe xmssSerializationTests where
  root := `Tests.XmssSerialization
