import EthCryptographySpecs.Proofs.Bls
import EthCryptographySpecs.Proofs.Kzg

/-!
# `EthCryptographySpecs.Proofs`

Machine-checked properties of the executable specification. This tree
mirrors the layout of the definitions it proves things about: proofs for
`EthCryptographySpecs.Foo.Bar` live in `EthCryptographySpecs.Proofs.Foo.Bar`.

The proofs are compiled by the `Proofs` Lake library, which the runtime
code does not depend on: nothing here is linked into the Python extension.
-/
