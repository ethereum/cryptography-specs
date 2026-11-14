# Soundness

This document says what the proofs of EthLib establish, and what a user of EthLib trusts on top of them.

No formal verification is absolute.
A proof links a Lean definition to a theorem, and both are assumed to match something outside Lean: the source document the definition implements, the code that actually runs, and what the client needs.
Each of those links is an assumption, and this document names them one by one.
It follows the structure of s2n-bignum's [`SOUNDNESS.md`](https://github.com/awslabs/s2n-bignum/blob/main/SOUNDNESS.md), adapted to a specification library.

This document describes the development tree that declares package version `0.3.0` in `pyproject.toml`.
It does not describe the tags `v0.1.0` and `v0.2.0`, which point to earlier commits.

The prose was reviewed by hand for that package version.
CI fails when `pyproject.toml` declares another version, so each version bump forces a new review of the document and an update of the line above.
The facts that change with the code, such as which theorems still use `native_decide`, are instead generated from the repository by `scripts/soundness_facts.py`.
CI fails when one of them is out of date, so they hold for every commit, not only for one version.

## Ways to use EthLib

Each way of using EthLib trusts a different set of things, so the summary table marks which risks apply to which use.
There are four uses:

- **P**, a Lean proof that imports the specification;
- **R**, a Lean program that runs the specification;
- **B**, a client that calls the Python bindings;
- **V**, a client that tests against the vectors in `tests/`.

## Summary

The risks fall into four gaps, one per link in the chain from source to client.
Gap A asks whether the definition says what the source and the client need.
Gap B asks whether the code that runs matches the definitions.
Gap C asks whether the proof itself is sound.
Gap D asks whether the use of EthLib holds together.

| ID | Risk | Mitigation in place | Applies to |
|----|------|---------------------|------------|
| A1 | A definition does not match its source | Definitions named and shaped after the source; vectors pinned to consensus-specs `v1.7.0-beta.4` and other upstream sources; consistency theorems on the constants | P R B V |
| A2 | A theorem holds only under a hypothesis | Each conditional theorem below lists its hypotheses | P |
| A3 | Timing reveals secret data | None: no constant-time claim | R B |
| A4 | A security theorem idealises a primitive | Each idealisation is listed in A4 | P |
| B1 | The Lean compiler, the C compiler or the Lean runtime is wrong | CI regenerates the vectors on every change, and the slow cases every week, then compares them with the committed ones | R B |
| B2 | Lean core runs code other than its definitions | Lean core is a declared baseline | R B |
| B3 | Elaboration runs native code | None | P |
| B4 | The hand-written C boundary is wrong | The regeneration and comparison of B1 | B |
| B5 | This repository substitutes compiled code | `lake exe check-decls` fails on any new substitution | R B |
| B6 | The build or the published wheel differs from the source | Fresh build per wheel in CI, with a pinned elan. Each wheel runs the vector suites, and carries a build provenance attestation | B |
| C1 | The Lean kernel or its axioms are unsound | None: `lake exe check-decls` checks which axioms a theorem uses, not that the kernel or the axioms are sound | P |
| C2 | A proof trusts compiled code | `lake exe check-decls` fails on any new use; the remaining ones are listed in C2 | P |
| C3 | A declaration reached the environment unchecked | leanchecker replays every declaration into the kernel every week, and on pushes to `master` | P |
| D1 | A client misuses an operation | Docstrings in Lean | R B |
| D2 | A dependency changes | Pinned in `lake-manifest.json` | P R B |
| D3 | The KZG trusted setup is not what it should be | Bytes match the consensus-specs setup | P R B V |
| D4 | The vectors are wrong | They match their pinned upstream sources, and CI checks their pinned digests | V |

The sections after the next one explain each row.

## What the proofs say

Before the risks, here is what is actually proved, primitive by primitive.
The list covers the main theorems and is not yet complete.

Most of these theorems are about correctness: an honest run gives the expected answer, or malformed input is rejected.

Some of them state a security property.
The unforgeability of leanXMSS holds for EthLib's own definitions.
The binding of an EIP-8450 proof of possession follows from it.
The unforgeability of leanSPHINCS holds for EthLib's own definitions too.
The unforgeability of BLS signatures holds for a scheme that EthLib's signing and verification compute.
The accountable safety and the plausible liveness of Casper FFG hold for an abstract model of votes.
The evaluation binding of single KZG proofs reduces to the strong Diffie–Hellman problem.
The binding of the batch check of KZG openings reduces to the same problem, or to a challenge that is a root of a nonzero polynomial.
The binding of the batch check of KZG cells reduces to the bilinear variant of that problem, or to such a root.
That reduction holds in a model of the target group of the pairing.

The binding of the batch check of blobs reduces to a challenge that is a root of a nonzero polynomial, or to recovery of the setup secret.
That reduction holds for algebraic adversaries, with the challenge hash modelled as a random oracle.
No theorem covers the code that runs, the C boundary, or timing.

### XMSS

The correctness theorem is `verify_keyGen_sign` (`Proofs/Xmss/Correctness.lean`).
If `keyGen seed` returns a key pair, and `sign` returns a signature for a message at a leaf index, then `verify` accepts that signature under that public key.
It says nothing about unforgeability.

In the random oracle model, signing fails with probability at most `2 exp(-4000)` (`prEvent_signWith_error_le`, `Proofs/Xmss/SignatureFailure.lean`).
The theorem assumes that the oracle's cache holds no trial input of the two keys that sign when signing starts, as an empty cache does.
It proves that the signer's own calls before each search add none.
The bound covers one signature from such a cache.
An earlier signature under the same key caches the trial inputs of its keys, and in the unforgeability game the adversary's queries can too.
So no theorem bounds the failure of a later signature, or of signing inside the game.

Unforgeability is `Unforgeability.unforgeable` (`Proofs/Xmss/Unforgeability.lean`).
In the random oracle model, an adversary whose experiment makes at most `q >= 1` hash calls forges a signature with probability at most `q / 2^127`.
Its game runs EthLib's `keyGenWith`, `signWith` and `verifyWith`, with the hash `H` a query to the random oracle.
`keyGen`, `sign` and `verify` are the same definitions with Keccak-256 as `H`.

The proof is adapted from leanerVM's, and `Proofs/Xmss/Security/README.md` lists what changed here.
It reasons over EthLib's algorithms.
Its model of the scheme with precomputed keys is a step of the proof, not a second statement.

The game follows the note's section "Security".
The adversary gets the public key, queries `H`, and requests signatures, never at the same leaf index twice.
It wins when its forgery verifies and no request for the forged message returned the forged signature.

The budget `q` counts every hash call of the game, including those of key generation, signing and the final verification.
It bounds every run, including the unlucky ones, so the bound is weaker than `2^-127` per adversary call:

- Key generation alone makes `K = 13,434,881` calls, about `2^23.7`, so the bound is never below about `2^-103.3`.
- A signing request can try up to `2^32` randomizers on each layer before one gives a codeword.
  So each signing request adds more than `2^33` to `q`, and an adversary with `n >= 1` requests gets a bound above `n * 2^-94`.
- An adversary that requests a signature at each of the `2^32` leaf indices has `q > 2^65`.
  So over the key's lifetime, the bound is above `2^-62`, about 62 bits, not 127.

The bound is classical: the adversary queries the oracle as a classical algorithm.
The statement is written with VCVio's oracle computations and probabilities, so their definitions are part of what it says.

### EIP-8450 proof of possession

A proof of possession is a leanXMSS signature, at leaf index 0, of a root that names a BLS key and the leanXMSS key.
Completeness is `isValidPqPossessionProof_sign` (`Consensus/Proofs/PqKeys/Possession.lean`): a key generated from a seed that signs its possession root at leaf 0 gives a proof that the check accepts.
`isValidPqPossessionProofWith_of_index_ne` shows that a proof at any other leaf index fails.

Binding is `possession_binding` (`Consensus/Proofs/PqKeys/PossessionBinding.lean`).
Its game is the leanXMSS game, except that the adversary returns a BLS key and a proof.
It wins when the check accepts the proof for that BLS key and the honest leanXMSS key.
And no signing request for their possession root returned that proof.
Such an adversary turns into a leanXMSS adversary with the same hash calls that wins whenever it wins, so the bound is again `q / 2^127`.
The game checks a proof as the specification does, and `possessionVerdict_eq` shows that the two verdicts agree for every hash.

The theorem says nothing about two BLS keys whose possession roots collide under SHA-256.
A proof that the key holder made for one of them is then valid for the other.
The game does not count that as a win.

### Merkle trees

leanXMSS, leanSPHINCS, the VRF tree and SSZ build their trees on one definition.
Two theorems in `Proofs/Merkle/Binding.lean` describe what a path binds, for every node hash.
The first is `climb_binding`, about two climbs from one position that reach one node.
They are equal, or `findCollision` returns a collision of the node hash at an ancestor of that position.
The second is `climb_binding_node`, about a climb that reaches an honest node but is not the honest climb.
Then `findSecondPreimage` returns a second preimage of an honest ancestor.

Both searches are explicit algorithms, proved to return valid answers.
Each can return nothing: on one climb compared with itself (`findCollision_self`), and on the honest climb (`findSecondPreimage_honest`).
So the statements say something, even though every compressing hash has collisions.

`Proofs/Merkle/RandomOracle.lean` bounds classical searches against an ideal random oracle with `N` outputs and an empty initial cache.
`prEvent_collision_le` bounds a collision among queried inputs by `q^2 / N` for at most `q` hash calls, and private uniform sampling is not counted.
This bound exceeds the standard birthday bound `q(q - 1) / (2N)` by the factor `2q / (q - 1)`: at most 4 for `q >= 2`, and close to 2 for large `q`.
`prEvent_experimentWith_le` applies it to an experiment where the adversary outputs a claim and an extraction then runs on it with the oracle alone.
It bounds a win by `q^2 / N` when every replayed win of the extraction leaves a collision in the cache.

`prEvent_secondPreimage_le` bounds by `q / N` a hit on a target digest fixed before the run, among queried inputs other than one honest input.
The theorem does not tie the target to the digest of the honest input.
Reading it as a second-preimage bound conditions on the honest digest and assumes that the other oracle answers stay independent and uniform.
That conditioning is a modelling step, not a proved one.

The Merkle applications model the tuple `(level, position, left, right)` as the oracle input.
They require an injective encoding of that tuple, for levels and positions inside the encodable range, not a hash that ignores the position.
The bounds run `findCollision` and `findSecondPreimage` themselves, with an oracle query as the node hash.
For paths and leaves fixed before the oracle is sampled, `prEvent_findCollision_queryNode_le` bounds the first search by `(2h)^2 / N`, where `h` is the shorter path length.
For the same fixed inputs, `prEvent_findSecondPreimage_queryNode_le` bounds the second by `Q^2 / N`, with `Q = secondPreimageQueries level path.length`.
Its budget counts every hash call, including repeated honest-node computations:

```text
Q(l, 0) = 0
Q(l, n+1) = 1 + 2*(2^l - 1) + (2^(l+1) - 1) + Q(l+1, n)
```

For a path of length `n` from level `l`, `Q` equals `2^(l+n+2) - 2^(l+2) - 2n`, while the search queries at most `2^(l+n) - 1 + n` distinct inputs.
The honest ancestors depend on oracle answers, so this search uses the birthday bound, not the bound for one fixed target.
The covered-event theorems also allow adaptive surrounding clients, provided their total budget includes the witness queries and honest-tree construction.
These statements do not bound attacks on a concrete hash or quantum queries.

The VRF's `verify_unique`, SSZ's `verifyMerkleProof_binding` and the leanXMSS unforgeability proof use `climb_binding`.
leanXMSS also states `fold_binding` with `climb_binding_node`, which its unforgeability proof does not use.

### SSZ

Four kinds of SSZ theorem say what a root binds, and each one reduces a conflict to a SHA-256 collision.
Each collision is two different 64-byte inputs with one digest, returned by an explicit search.

Branch binding is `verifyMerkleProof_binding` (`Proofs/Ssz/Merkle/Authentication.lean`).
Two accepted branches at one index and root open one leaf, or `findBranchCollision` returns a collision.
It rests on `climb_binding`, above.
`climbBranchM_binding` states the binding of the climb for any node hash.
`findBranchCollision_valid_of_width` states the collision for any hash with 32-byte digests.

Multiproof binding is `verifyMerkleMultiproof_binding` and `verifyMerkleMultiproof_overlap_binding` (`Proofs/Ssz/Merkle/MultiproofBinding.lean`).
Two accepted requests for one root agree on every position they both claim, or `findMessageCollision` returns a collision.
That search tries each input one verifier hashes against each input the other hashes.

Whole-value binding is `hashTreeRoot_binding` (`Proofs/Ssz/Codec/Binding.lean`).
Two values of one type with one root are equal, or `findMessageCollision` returns a collision between the hash inputs of the two root computations.
It has three hypotheses on each value.
The type is well formed, the value fits the type, and the value is `CommitmentSized`: every variable-size count in it is below `2^256`.
A larger count would be truncated in the 256-bit word mixed into the root, and the proof needs the exact count.
`hashTreeRootM_binding` states the same, with the same hypotheses, for any hash with 32-byte digests.
It computes the roots of the all-zero subtrees with that hash too.

Layout separation is `hashTreeRoot_progressiveContainer_layouts_separate` (`Proofs/Ssz/Codec/LayoutSeparation.lean`).
Two legal progressive containers with one root have one layout, or `findMixinCollision` returns the inputs of the two last hashes.
`hashTreeRootM_progressiveContainer_layouts_separate` states the same for any hash with 32-byte digests.
It computes the roots of the all-zero subtrees with that hash too.

No theorem bounds the probability of finding a collision in a multiproof.
Its verifier hashes each pair with `combine` in `foldLevelNodes`, which takes no node hash as an argument, so no experiment runs it against the oracle.

`Proofs/Ssz/RandomOracle.lean` bounds whole-value binding, with the node hash a random oracle.
The merkleization takes its hash in any monad, so the experiment runs the root of the specification with a hasher that queries the oracle.
That hasher also computes the roots of the all-zero subtrees with the oracle, one query per level.
The type is fixed before the run, and an adversary outputs two values of it.
The experiment computes both roots, then hashes every node of both expanded computations again with the oracle.
The adversary wins when the two values differ, fit the well-formed type, are `CommitmentSized`, and have one root.
`collision_of_extract` shows that every win leaves two different cached inputs with one answer.
Its proof finds them with `findMessageCollision`, run with a table that agrees with the cache.
`prEvent_wins_le` bounds a win by `Q^2 / N`, applying `prEvent_experimentWith_le` to `collision_of_extract`, and `prEvent_wins_le_two_pow` states the bound with `N = 2^256`.
`Q` counts every oracle call of the experiment, repeats included.
The extraction makes many: the expanded computations hash every node of the padded tree of each value, one query each.
So `Q` grows with the capacity of the type, not with the length of the values.
A list with a capacity of `2^38` nodes costs about `2^38` queries for each value, so about `2^39` for the two.
For an Electra beacon state the padded trees hold about `2^40.6` nodes for each value, so `Q` is at least about `2^41.6`, and with `Q = 2^42` the bound is `2^-172`.
A rehash that shares the all-zero subtrees would bring `Q` down to the size of the values, and is left for later.
`prEvent_secondValue_le_two_pow` fixes the first value as an honest one: its root is computed in the experiment, with the same oracle.
That is still the birthday bound, not a sharper fixed-target bound.
The bound needs no hypothesis that the cache covers the witnesses, since the experiment queries them itself.
One oracle answers inner nodes and mixed-in words alike, so a collision between any two inputs counts.

`Proofs/Ssz/LayoutRandomOracle.lean` runs layout separation against the same oracle, with the same hasher.
An adversary outputs two types and a value of each, and may pick the types after its queries.
The experiment is the generic one that also gives the experiment for whole values, run with another extraction.
That extraction computes both roots, then the input of each last hash with the oracle, and queries each input again.
The adversary wins when both types are legal progressive containers with different layouts, and the two roots are equal.
`collision_of_extractLayouts` shows that every win leaves two different cached inputs with one answer.
Its proof applies `hashTreeRootM_progressiveContainer_layouts_separate` to a table that agrees with the cache, and takes the inputs that `findMixinCollision` returns.
The extraction queried both inputs again, so the cache holds them, by `cached_of_extractLayouts`.
`prEvent_experimentWith_le` then gives `prEvent_layoutWins_le`, which bounds a win by `Q^2 / N`, and `prEvent_layoutWins_le_two_pow` states it with `N = 2^256`.
The layout extraction expands no padded tree, so `Q` grows with the data and with the depth of each tree, since a zero subtree costs one query per level, not with the capacity of the type.

`Proofs/Ssz/BranchRandomOracle.lean` bounds the binding of `isValidMerkleBranch`, the branch check by depth and index, with the same oracle.
The depth is fixed before the run, and an adversary outputs an index and two leaves, each with a branch.
The extraction climbs the first `depth` nodes of each branch, as `computeMerkleBranchRoot` does.
It climbs with `climbBranchM`, which is `climbBranch` with the node hash as an argument (`climbBranchM_sha256`), and here that hash is the oracle.
The adversary wins when the leaves differ, both branches have `depth` nodes, and both climbs reach one root, computed by the oracle.
`collision_of_extractBranches` shows that every win leaves two different cached inputs with one answer.
Its proof applies `climbBranchM_binding` to a table that agrees with the cache, and takes the messages that `findBranchCollision` returns.
The climbs queried every message they hash, so the cache holds both, by `cached_of_climbBranchM`.
`prEvent_experimentWith_le` then gives `prEvent_branchWins_le`, which bounds a win by `Q^2 / N`, and `prEvent_branchWins_le_two_pow` states it with `N = 2^256`.
`Q` counts the adversary's queries and one query for each branch node that a climb hashes, so the extraction adds at most `2 * depth`.
`experimentWith_extractBranches_queryBound` proves this count.
`prEvent_branchWins_le_of_adversary` states the bound with `Q = q + 2 * depth`, for an adversary that makes at most `q` queries.
Beyond the adversary's own queries, `Q` grows with the depth, not with the `2^depth` leaves.
With SHA-256 in place of the oracle, `branchWins_sha256_iff` shows that a win is two different leaves that `isValidMerkleBranch` accepts at one depth, index and root.
The specification hashes with SHA-256, and the step from SHA-256 to the oracle is the idealisation of A4, not a theorem.

`Consensus/Proofs/DataAvailability/BlobRandomOracle.lean` composes this bound with `verifyBlobSidecarInclusionProof`, the inclusion check of blob sidecars.
The preset and the fork are fixed before the run, and an adversary outputs two blob sidecars.
The extraction roots both commitments, reads the subtree index of the first blob index as the check does, and climbs both proofs.
Every hash is an oracle call, and the climbs take the inclusion proof depth of the preset.
The adversary wins when the sidecars have one index, one body root and different commitments, and both climbs reach that body root.
Only the forks from Deneb and before Gloas put the commitments in the body.
At the other forks the extraction reads no subtree index, so it climbs nothing and no adversary wins; no theorem states this.

`collision_of_extractBlobSidecars` shows that every win leaves two different cached inputs with one answer.
By `hashTreeRootM_bytes48` (`Serialization/Proofs/Ssz/BranchRandomOracle.lean`), the root of a commitment is one hash of its 48 bytes and 16 zero bytes.
So equal roots of two different commitments are two such inputs.
Two different roots that climb to one body root give the inputs that `collision_of_extractBranches` finds.
`prEvent_experimentWith_le` then gives `prEvent_blobWins_le`, which bounds a win by `Q^2 / N`, and `prEvent_blobWins_le_two_pow` states it with `N = 2^256`.
`extractBlobSidecars_queryBound` shows that the extraction makes one query per commitment root and at most `2 * depth` for the climbs.
`experimentWith_extractBlobSidecars_queryBound` adds the adversary's queries, through `experimentWith_queryBound`, which the branch bound shares.
`prEvent_blobWins_le_of_adversary` states the bound with `Q = q + 2 + 2 * depth`, for an adversary that makes at most `q` queries.
At the mainnet depth of 17, `prEvent_blobWins_le_mainnet` bounds a win by `(q + 36)^2 / 2^256`.
Beyond the adversary's own queries, `Q` grows with the depth only, not with the blobs or the body.
With SHA-256 in place of the oracle, `blobWins_sha256_iff` shows that a win is two such sidecars that `verifyBlobSidecarInclusionProof` accepts.
Carrying the bound over to SHA-256 is the idealisation of A4, not a theorem.

These other branch checks also hash with SHA-256, and no theorem composes their proofs with the branch bound:

- The light client checks of bootstraps and updates, from Altair, and of headers, from Capella.
- `verifyKzgCommitmentsInclusionProof`, which data column sidecars and partial data column headers read at Fulu.
- The deposit branch check of `processDeposit`, before Heze.

### leanSPHINCS

The correctness theorem is `verify_keyGen_sign` (`Proofs/Sphincs/Correctness.lean`).
If `keyGen seed` returns a key pair, and `sign` returns a signature for a message, then `verify` accepts that signature under that public key.

The Python suite checks one signature that an independent implementation computed, with its public key, through the bindings.

In the random oracle model, all `2^32` counters of one search miss the code with probability below `exp(-2^18)` (`prEvent_findCounter_none_le`, `Proofs/Sphincs/CodewordSearch.lean`).
The theorem assumes that the oracle's cache holds none of the counters' inputs when the search starts.

In the random oracle model, signing fails with probability at most `3 exp(-2^18)` (`prEvent_signWith_error_le`, `Proofs/Sphincs/SignatureFailure.lean`).
The theorem assumes that the oracle's cache holds no trial input of any key when signing starts, as an empty cache does.
It proves that the signer's own calls before each search add none of that layer's trial inputs.
The bound covers one signature from such a cache.
An earlier signature under the same key caches the trial inputs of its keys, and in the unforgeability game the adversary's queries can too.
So no theorem bounds the failure of a later signature, or of signing inside the game.

Unforgeability is `Unforgeability.Bridge.unforgeable` (`Proofs/Sphincs/Unforgeability.lean`).
Take an adversary whose experiment makes at most `q >= 1` hash calls and at most `2^30` signing requests.
In the random oracle model, it forges a signature with probability at most `q / 2^127`.
Its game runs EthLib's `keyGenWith`, `signWith` and `verifyWith`, with the hash `H` a query to the random oracle.
`keyGen`, `sign` and `verify` are the same definitions with Keccak-256 as `H`.

The proof is a port of leanVM's model of the scheme, and `Proofs/Sphincs/Security/README.md` lists what changed here.
The model comes from the commit that merged [leanVM#662](https://github.com/leanEthereum/leanVM/pull/662), which moves the scheme to the hash layout of FIPS 205.
The model signs the layers of the hypertree from the bottom up, as EthLib does.
The bridge in `Proofs/Sphincs/Unforgeability/Bridge/` connects the model to EthLib's algorithms.
An EthLib forgery is a model forgery of a translated adversary (`forgeAdvantage_le`).
Under every fixed answer of the oracle, a signing request costs the model at most what it costs EthLib (`hashCalls_sign_le`).
So the adversary's budget of `q` hash calls carries over unchanged, and the model's theorem `h26_layered` gives the bound.

### VRF tree

A VRF tree commits to secret outputs under one root, and later opens them one index at a time.
Two theorems in `Proofs/Vrf/Verify.lean` describe it.
`verify_unique` says that two openings that verify at one index under one root give one output, or `findHashCollision` returns a collision of Keccak-256.
That search reads only the index and the two openings.
The theorem holds for every root, including one built to cheat.
`verify_opening` says that the opening of an honest tree verifies, with the output of its secret.

Uniqueness is reduced to a collision, and no theorem bounds the cost of finding one.
In the random oracle model, `prEvent_guess_le` (`Proofs/Vrf/Unpredictability.lean`) bounds the chance of guessing an unopened output.
The secret at the guessed index is uniform, and the adversary sees the root, the hash and the openings at other indices.
It guesses right with probability at most `(1 + 2 Q) / 2^256`, where `Q = q_H + (q_O + 1) 2^33` counts its hash queries and requests.
The theorem fixes the index in advance, and does not cover a secret derived from a seed.
`prEvent_adaptiveGame_le` (`Proofs/Vrf/AdaptiveIndex.lean`) lets the adversary choose the index, with all secrets uniform.
Its bound is `2^32 (1 + 2 Q) / 2^256`, because the proof splits a win by the index named.
`prEvent_seedGame_le` (`Proofs/Vrf/SeedSecrets.lean`) does the same for secrets derived from a uniform seed, as key generation derives them.
One hidden-seed step adds `Q / 2^256` to its bound.
Verification accepts any tree, so a holder that chooses its secrets can bias every output.

The output hashes its index with its secret: `keccak256(PQ_VRF_OUTPUT | LE32(i) | s)`.
`outputHash_binding` (`Proofs/Vrf/Verify.lean`) says that two equal outputs come from one index and one secret, or their two output inputs, which differ, are a Keccak-256 collision.
`verify_index_binding` applies it to two openings that verify at two different indices, under any roots.
So one secret gives different outputs at different indices, unless Keccak-256 collides.
That two such outputs behave as independent values is a random-oracle heuristic, which no theorem states.
A holder can still grind index by index, at about `2^k` hashes per index for a threshold of one in `2^k`.

A selection therefore compares `mixOutput`, the hash of the output with randomness revealed after the root is registered.
`prEvent_selected_le` (`Proofs/Vrf/Selection.lean`) covers a holder that chooses every secret of its tree.
The mix is a random oracle, and the tree hash is Keccak-256 itself.
The holder makes at most `q` mix queries before the randomness is drawn, then opens any index of a set `I` fixed in advance.
The mixed value of its output lands in a target set `S` with probability at most `|I| |S| / 2^256 + q / 2^256`, plus the chance that `findHashCollision` returns a collision with the honest opening at that index.
No theorem bounds that last chance, as for uniqueness.
The theorem says nothing about a holder that registers a root without knowing a tree under it.
That case would need the tree hash as a random oracle too, and an extractor of the tree from the queries.
It says nothing either about randomness that the holder knows at registration, or can bias: the game draws it uniformly and independently of the holder.
The game is EthLib's own.
`selected_iff_mixOutput` shows that, with `mixOutput` in place of the oracle, its event is exactly the protocol's check.

[EIP-8450](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8450.md#cryptographic-helpers) specifies the interface `vrf.Verify` and the property of unique outputs, not the construction.
The index in the output keeps that interface, and changes every output of the construction that EthLib specified before.
The EIP's rationale ([Two keys per validator](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8450.md#two-keys-per-validator)) says that the root fixes one output per index before the validator knows its inputs.
That does not stop a holder from choosing its outputs, so the fork that uses the root must select with the mix.

### BLS12-381

The BLS theorems check the constants, because a wrong digit in a modulus or in the generator would very likely make one of them fail.
`modulus_prime` (`Proofs/Bls/FpZMod.lean` and `Proofs/Bls/FrZMod.lean`) proves that both moduli are prime.
`seven_pow_card_sub_one` and `seven_pow_div_prime_ne_one` (`Proofs/Bls/FrZMod.lean`) prove that `7` generates the multiplicative group of the scalar field; `7` is also the KZG constant `PRIMITIVE_ROOT_OF_UNITY`.
`addOrderOf_toPoint_generator` (`Proofs/Bls/G1Order.lean`) proves that the G1 generator has order `r`.

`pairingBilinear` (`Proofs/Bls/PairingAte.lean`) proves that the pairing is bilinear on the multiples of the generators: `e(a g_1, b g_2) = e(g_1, g_2)^(a b)` for all `a` and `b` in `Fr`.
`orderOf_pairing_generators` (`Proofs/Bls/Nondegenerate.lean`) proves that the pairing of the two generators has order `r`, so it is not 1; the kernel evaluates that pairing.
`PairingLaws.of_bilinear` (`Proofs/Bls/PairingBilinear.lean`) derives `PairingLaws` from one smaller hypothesis, `PairingBilinear`: `e(a g_1, b g_2) = e(g_1, g_2)^(a b)` for all `a` and `b` in `Fr`.
`pairingBilinear` proves `PairingBilinear`.
`PairingLaws` (`Proofs/Bls/PairingLaws.lean`) states the consequence that verification needs, as one structure.
`pairingLaws` (`Proofs/Bls/PairingAte.lean`) proves `PairingLaws`.
Let `P_i` represent `a_i * g_1` and `Q_i` represent `b_i * g_2`, where a representative is any valid point with that group element.
Then the check of the pairs `(P_i, Q_i)` passes exactly when `sum_i a_i * b_i = 0` in `Fr`.
The law holds when the check tests `prod_i e(P_i, Q_i) = 1` for any bilinear map `e` with `e(g_1, g_2) != 1` into a group of order `r`.
`pairingCheck_congr` (`Proofs/Bls/PairingCongr.lean`) proves that the check depends only on the group elements of valid points, so the law can quantify over representatives.
`TargetGroup.ofPairingLaws` (`Proofs/Bls/TargetGroup.lean`) builds a model of the target group from the proved law.
Its target is `Fp12` and its generator is `e(g_1, g_2)`.
In this model, `pairing P Q = e(g_1, g_2)^(a b)` when `P` represents `a * g_1` and `Q` represents `b * g_2`.
An element of the model represents `t` in `Fr` when it is `e(g_1, g_2)^t`.
The BLS signature, consensus, KZG, PeerDAS and EIP-2537 theorems use `pairingLaws` inside their proofs.
Only the lemmas of `Proofs/Bls/PairingLaws.lean`, which derive consequences of the law, take `PairingLaws` as a hypothesis.

`finalExponentiation_eq_pow` (`Proofs/Bls/FinalExponentiation.lean`) proves that the final exponentiation raises every element of `Fp12` to exactly `(p^12 - 1) / r`.
`millerDouble_snd` and `millerAdd_snd` (`Proofs/Bls/MillerLoop.lean`) prove that each step of the Miller loop multiplies by the line through the untwisted points, times `c w^3` for some `c` in `Fp2`.
The doubling step needs `T` finite with `Y ≠ 0`, and the addition step needs `T` finite with an `x` other than that of `Q`.
`finalExponentiation_fp2_mul_w_cube` proves that the final exponentiation sends `c w^3` to 1 when `c ≠ 0`.
`pairing_eq_finalExponentiation_loop` (`Proofs/Bls/MillerChain.lean`) chains these steps over the whole loop.
Take a valid `Q` of order dividing `r`, and a finite `P`.
Then the pairing is the final exponentiation of the conjugate of Miller's algorithm, run on `|x|` and the untwist of `Q`, at `P`.
Miller's algorithm (`Proofs/MillerFunction.lean`) multiplies the values at `P` of the functions `g_{T,S}` of Miller (J. Cryptology 17, 2004, Section 4.1, Definition 5).
`spanSingleton_lineRatioElem` (`Proofs/MillerDivisor.lean`) proves the fractional ideal of each `g_{T,S}`: the ideal of `T` times that of `S`, over that of `T + S`.
`loop_eq_linesValue` (`Proofs/MillerLines.lean`) proves that the loop computes a product of lines over a product of verticals, at every point.
`linesDivisor_lines` proves that the divisors assigned to these factors add up to `s (Q) - (s Q) - (s - 1) (O)`, the divisor of Miller's function `f_{s,Q}` (Lemma 2, equation (7)).
Only the affine part of each divisor is proved, through fractional ideals; no theorem checks the multiplicity at `O`.
`spanSingleton_millerElem` proves that the function has the fractional ideal of `Q` to the power `s`, over that of `s Q`.
`linesElem_mul_eq_of_linesDivisor` (`Proofs/MillerUnique.lean`) proves that two quotients of products of lines with the same divisor are equal, with no constant left.
The units of the coordinate ring are the nonzero constants, and every line has the leading coefficient 1 at `O` for the uniformizer `-x / y`.
`weil_reciprocity` (`Proofs/MillerReciprocity.lean`) proves Weil reciprocity for two quotients of products of lines whose lines share no finite point: `f(div g) = ε g(div f)`.
The sign `ε` is -1 to the product of the multiplicities of `O` in the divisors assigned to the lines.
Each function is taken as 1 at `O`.
`pow_ratioAt_add_left` and `pow_ratioAt_add_right` (`Proofs/MillerAte.lean`) prove the linearity of an ate-type pairing, on any curve and field.
The pairing evaluates a quotient of products of lines at `P`, then raises the value to a power `N`.
Let `pi` be the map `(x, y) -> (x^q, y^q)`, and let the quotient for `Q` have the divisor `sum_j c_j ((pi^j Q) - (O))`.
Let `z^(N n)` be 1 for every nonzero `z`, with `n = sum_j c_j q^j`.
Then the pairing is linear in a point `P` fixed by `pi`, when `N` is even, and linear in `Q`.
`Q` lies in a group that `pi` maps into itself, and where `pi` fixes only `O`.
`frobenius_of_mem` (`Proofs/Bls/AteFrobenius.lean`) applies these results to BLS12-381, where `pi` acts as the BLS parameter `x = -|x|` on the untwist of `G2`.
`eq_zero_of_frobenius_eq` proves that `pi` fixes only `O` there, because `r` does not divide `|x| + 1`.
`frobenius_iterate_seven` proves that `pi^7` acts as `|x|` there, because `r` divides `|x|^7 + |x|`.
`ratioDivisor_lines` proves that Miller's function of `|x|` and a point `Q` of the untwist of `G2` has the divisor `|x| ((Q) - (O)) - ((pi^7 Q) - (O))`.
`pow_ateExponent` proves that `z^(N (|x| - p^7))` is 1 for every nonzero `z` in `Fp12`, with `N = (p^12 - 1) / r`.
`ateValue_add_left` (`Proofs/Bls/PairingAte.lean`) proves that Miller's function of `|x|` and `Q`, at `P` and raised to `N`, is linear in a point `P` that `pi` fixes.
`ateValue_add_right` proves that it is linear in `Q` on the untwist of `G2`.
`pairing_eq_ateValue` proves that the pairing of a valid finite point `P` of `G1` and a valid point `Q` of the subgroup of `G2` is that value raised to `p^6`.
The alt_bn128 section lists the same application to alt_bn128.

The pairing of the two generators equals the value that [draft-irtf-cfrg-pairing-friendly-curves-11](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-11) publishes in Appendix B.
The Python suite checks it through the bindings (`bindings/python/tests/bls/test_pairing.py`), with a few bilinearity checks.
This evidence tests the compiled code against the published value.

`keyValidatePoint_eq_ok_iff` (`Proofs/Bls/KeyValidate.lean`) proves that key validation accepts exactly the encodings of the nonzero points of order `r` in G1.
The G1 and G2 subgroup checks accept exactly the valid points that represent a multiple of the generator.
Every output of the maps to G1 and G2 is a valid point of that subgroup (`Proofs/Bls/MapToCurve.lean`).
`hashToG2_total_inSubgroup` (`Proofs/Bls/CofactorSubgroupLanding.lean`) proves that the hash to G2 succeeds on every input and returns a valid point of that subgroup.
`toPoint_clearCofactor_eq_hEff` (`Proofs/Bls/CofactorEffective.lean`) proves that the cofactor clearing of RFC 9380 Appendix G.3 is the multiplication by the `h_eff` of §8.8.2, on every valid point of the twist.
`hashToG2_eq_hEff_smul` proves that each output of the hash to G2 is `h_eff` times a valid point of the twist.
`expandMessageXmd_eq_spec` (`Proofs/Bls/ExpandMessage.lean`) proves that the message expansion is `expand_message_xmd` of RFC 9380 §5.3.1 with the FIPS 180-4 model of SHA-256.
It covers the shortened DST of §5.3.3.
It assumes a message shorter than 2^61 - 323 bytes and a DST shorter than 2^61 - 17 bytes.
`hashToFieldFp2_eq_spec` proves that the hash to `Fp2` is `hash_to_field` of §5.2 under the same bounds, with each coordinate read in `ZMod p`.
No theorem yet compares the SSWU map or the isogeny with a model of RFC 9380.

`sign_ok` and `popProve_ok` (`Proofs/Bls/Signatures.lean`) prove that BLS signing never fails.
An honest signature, an honest proof of possession and an aggregate of honest signatures verify (`verify_sign`, `popVerify_popProve`, `aggregateVerify_aggregate`, `Proofs/Bls/SignaturesCorrect.lean`).
For the fast aggregate verification on one message, `fastAggregateVerify_aggregate` also assumes that the secret keys do not sum to zero modulo `r`.
Otherwise the aggregate key is the point at infinity, and key validation rejects it.

A key and a message have at most one signature that verifies, byte for byte (`verify_unique`, `Proofs/Bls/SignaturesUnique.lean`).
From a victim's key alone, an attacker builds a second key and a signature that passes the fast aggregate verification for both (`fastAggregateVerify_rogue`).
So each key of that verification needs a verified proof of possession.

`forgeAdvantage_le` (`Proofs/Bls/Security/Reduction.lean`) states unforgeability in the random oracle model.
It follows Theorem 3.2 of [Boneh, Lynn, Shacham](https://hovav.net/ucsd/dist/sigs.pdf), with the simple guessing reduction.
The scheme lives over two abstract groups, with keys `a • g1`, hashes in `G2` and signatures `a • H(m)`.
Its verification is a test of co-Diffie-Hellman tuples, and the theorem assumes that the test is sound.

Let every run of the game make at most `q` hash calls, counting signing and the final verification.
Then a forger wins at most `q` times as often as a named solver of a co-Diffie-Hellman problem.
That problem asks for `(a * c) • g2` from `a • g1`, `a • g2` and `c • g2`.
It is stronger than the co-CDH of the source's §2, which omits `a • g2`.
The source needs it when no computable map from `G1` to `G2` is known.

`forgeAdvantage_blsScheme_le` (`Proofs/Bls/Security/Refinement.lean`) applies the theorem to EthLib.
The groups are the multiples of the generators of G1 and G2, and the test is the pairing check.
The test is sound (`blsScheme_sound`).
`sign_eq` and `verify_iff_isDh` prove that EthLib's `sign` and `verify` compute the scheme.
There `H(m)` is the hash to G2 of `m` under the message tag.
Aggregation and proofs of possession lie outside that game.

A second game (`Proofs/Bls/Security/PopGame.lean`) states unforgeability of aggregates with proofs of possession, after §3.3 of [draft-irtf-cfrg-bls-signature-04](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-3.3).
One key is honest; the adversary chooses the others.
It wins with an aggregate on a message it never asked to be signed, verifying under the sum of keys that include the honest one and all carry valid proofs.
The counts below include the calls of signing, of the honest proof and of verification.
`Pop.forgeAdvantage_le` (`Proofs/Bls/Security/PopBound.lean`) bounds a forger within `q` message and `qK` key hash calls by `q` times a named solver of the same problem, plus `(q + qK - 1) / |F|`.
It assumes the test is sound, every element of `G1` is a multiple of `g1`, and `qK` is at most the characteristic of the scalars.
Without the last, enough copies of the honest key sum to zero.
`Pop.byteForgeAdvantage_le_coCdhAdvantage` (`Proofs/Bls/Security/PopByteGame.lean`) carries the bound to EthLib's bytes.
The forger sees compressed keys, hashes, signatures and proofs, and returns bytes.
It must pass EthLib's proof verification for every key and EthLib's fast aggregate verification, each with the oracle's hash in place of the hash to G2 (`Proofs/Bls/Security/PopRefinement.lean`).
`byteVerify_eq_popVerify` and `byteFastAggregateVerify_hashPoint` show that with the real hashes these checks are `popVerify` and `fastAggregateVerify`, and `popProve_eq` that the honest proof is `popProve`.
The key hash of bytes that decode to a multiple of `g1` is the group oracle on the decoded element; other bytes get independent uniform answers.
The key-call count leaves those other bytes out, since verification never hashes them.
`LightClientForgery.forgeAdvantage_le` (`Consensus/Proofs/LightClient/Unforgeable.lean`) applies the bound to the light client.
One sync committee member is honest; the forger chooses the configuration, the store, the update and the clock, and gives a proof of possession for each signer.
It wins if `validateLightClientUpdate` accepts the update with the honest member's bit set, with the oracle's hash of the signing root, and the honest member never signed that root.
Its advantage is at most the byte bound above.
`validateLightClientUpdate_oracleChecks` shows that with the real hash of the signing root, the game's check is the light client's check with the BLS checks.
The light client theorems of `Authenticate.lean` still take `SignatureChecks.AggregateSound`, because they reason about one accepted update, not a probability.
The game requires a proof of possession that passes PopVerify, §3.3.3, under the key tag.
Ethereum registers a validator key with a deposit signature instead, a signature on a message that holds the key, under the message tag and the deposit domain.
The bound does not cover that form of proof.

`Security.byteForgeAdvantage_le` (`Proofs/Bls/Security/Refinement.lean`) turns a forger on byte encodings into a named group-element forger with at least the same advantage.
The byte forger receives a compressed key and compressed hash and signing answers, and returns arbitrary message and signature bytes.
The game runs EthLib's G2 decompression, signature subgroup check and key validation before the pairing check.
This step needs no pairing law, because the byte check and the group test pair the same group elements.
`encode_publicKey`, `encode_signature` with `sign_eq`, and `byteVerify_hashPoint` connect these operations to EthLib's public key, signing and verification when the oracle uses EthLib's hash.
The bound still models that hash as a random oracle, not as the concrete hash function.

Freshness is by message: a message submitted to signing cannot win with any signature bytes.
`decodeSignature_encode` and `encode_eq_of_decodeSignature` prove both encoding round trips, so two accepted encodings of the same subgroup element cannot differ.
The byte game keeps the group game's uniform scalar distribution, including zero, whose key validation rejects.
EthLib's secret keys exclude zero, and a zero key always loses.
`nonzeroByteForgeAdvantage_eq` (`Proofs/Bls/Security/Refinement.lean`) draws a uniform nonzero key instead.
Against that key, a forger wins exactly `r / (r - 1)` times its byte advantage.
`nonzeroByteForgeAdvantage_le_coCdhAdvantage` carries this factor into the co-CDH bound below.
`Security.byteForgeAdvantage_le_coCdhAdvantage` gives the same `q`-factor co-CDH bound when the decoded forger makes at most `q` hash calls.
`byteForgeAdvantage_le_coCdhAdvantage_of_byteHashCallBound` states the bound with the hash-call bound on the byte forger itself.
`byteHashCallBound_iff` proves that the two bounds are equivalent, because the encoding forwards each query once.

### secp256k1

The secp256k1 theorems are correctness statements.
`card_point` (`Proofs/Secp256k1/Order.lean`) proves that the group has `n` points, so the cofactor is 1.
`decode_eq_ok_iff` (`Proofs/Secp256k1/Encoding.lean`) proves that the decoder accepts exactly the encodings of the points other than `O`.
`verify_sign` (`Proofs/Secp256k1/Ecdsa.lean`) proves that a signature from the signing operation of SEC 1 verifies.
`verify_eq_true_iff` (`Proofs/Secp256k1/Recovery.lean`) states verification against a key in the group of the curve.
It is the verifying operation of SEC 1 v2 §4.1.4.
By it, a signature is valid exactly when `r` and `s` lie in `[1, n - 1]` and the key is a point of the curve other than `O`.
The point `(e / s) G + (r / s) Q` must also be other than `O`, with `x mod n = r`.
`verify_recover` and `recover_of_verify` (`Proofs/Secp256k1/Recovery.lean`) prove that a recovered key verifies the signature, and that every key that verifies one is recovered, when `r + n >= p`.
`recover_eq_ok_iff` states recovery in the group of the curve.
It is the public key recovery of SEC 1 v2 §4.1.6, with `x_R = r` only.
By it, recovery returns `Q` exactly when `r` and `s` lie in `[1, n - 1]` and `R = (r, y)` lies on the curve.
The parity of `y` must be the recovery id.
`Q` must be a point of the curve other than `O`, equal to `(s / r) R - (e / r) G`.
`verify_lowS_unique` (`Proofs/Secp256k1/Malleability.lean`) proves that two low-s signatures with one `r` that verify are equal, under the same bound.
`verify_iff_s_eq_or_neg` assumes the same bound and a valid signature `(r, s)`.
Under them, `(r, s')` verifies under the same key and hash exactly when `s'` is `s` or `n - s`.
`verify_and_isLowS_iff` adds that `s` is low, and then that signature is the only valid low-s one with that `r`.

The probability of forging a signature with a signing oracle has a bound in an idealised model, below, which rests on the discrete logarithm problem and on properties of the hash.
`Proofs/Secp256k1/Security/Game.lean` states the unforgeability game of GenDSA, the abstraction of ECDSA in [Fersch, Kiltz and Poettering](https://doi.org/10.1145/2976749.2978413), Definition 6, in their bijective random oracle model.
There, `verify_neg` shows that `(r, -s)` verifies whenever `(r, s)` does, when opposite points share their encoding, as `x` coordinates do.
So the game counts only messages that were never signed.
`forgeAdvantage_collision_pos` shows that a collision of the message hash wins that game with positive probability.
`Proofs/Secp256k1/Security/KeyOnly.lean` states the key-only game of the source's Definition 4, with no signing oracle.
`forgeAdvantage_toAdversary` proves that it is the chosen-message game of a forger that never asks for a signature.
`keyOnlyAdvantage_le_indep` replaces the bijection by independent uniform answers in that game.
It counts no win once a new answer repeats a cached value in the direction of its query.
The cost is at most `q (q + 1) / 2` over the size of the bijection's domain, for a forger with at most `q` queries to the bijection or its inverse.
That is the step from Game G0 to Game G1 of §4.2 of the source, in the proof of its Theorem 2, whose bound `Q² / 2^L` is at least as large.
The source draws the key from the nonzero scalars; the key-only game here draws it from all scalars, and the key `0` never verifies.
So its advantage is the source's times `(n - 1) / n`, where `n` is the number of scalars.
`keyOnlyIndepAdvantage_eq_outside` (`Proofs/Secp256k1/Security/KeyOnlyOutside.lean`) proves that the advantage with independent answers stays the same when each new forward answer is one query to an outside oracle with no input.
`forward_point_eq_answer_ne_of_mem_support_contextFork` proves that the two runs returned by a replay fork at the new forward query of the forgery's point share that point and got different answers there.
`le_prEvent_isSome_contextFork_keyOnlyOutsideRun` bounds the chance of the fork from below on each fixed key, in the form of Lemma 1 of the source.
`le_prEvent_isSome_contextFork_keyOnlyOutsideRun_uniform` gives the same bound with the key drawn uniformly, as Lemma 1 draws it at random.
Unlike Figure 2 of the source, the fork draws the coins after the fork point again.
`reduce_forward_eq_of_forkIndex_eq_some` (`Proofs/Secp256k1/Security/ForwardCase.lean`) proves that the check of a run with a fork index read the logged answer at that index, so `ψ` maps that answer to the forgery's `t`.
It rests on an invariant of the run: each logged pair stays cached, and while no flag is raised the cache is a partial bijection.
`forward_eq_of_mem_support_contextFork` (`Proofs/Secp256k1/Security/ForwardCase.lean`) gives, for both runs of the fork, the shared point and the two different answers, with `ψ` mapping each answer to the `t` of its forgery.
For a forger with at most `q` queries to the bijection or its inverse on every key, `keyOnlyIndepAdvantage_le_forkIndex_add_notMem` (`Proofs/Secp256k1/Security/KeyOnlyOutside.lean`) bounds its chance to win with independent answers, over a uniform key, by the chance of a fork index plus the chance that the check passes on a point that was not a new forward query.
`prEvent_inverse_le_dlog`, below, bounds the second chance.
`divisionAdvantage` (`Proofs/Secp256k1/Security/DivisionResistance.lean`) states the ψ-relative division resistance of the hash, Definition 5 of the source.
`prEvent_contextFork_div_eq_le_divisionAdvantage` bounds the fork whose two forgeries divide to the same scalar, the abort of line 10 of Figure 9, by `q + 1` times the advantage of the reduction of Figure 10.
The hash is fixed there, while §2.3 of the source draws a key for it, so the bound charges that named reduction and no adversary of division resistance in general.
`prEvent_contextFork_div_ne_le_dlog` (`Proofs/Secp256k1/Security/ForwardSolver.lean`) bounds the other forks by the advantage of the discrete-logarithm solver of Figure 9, which extracts the key from the two forgeries.
`redrawInverse_fst_evalDistEq` (`Proofs/Secp256k1/Security/Redraw.lean`) proves the step of lines 25 to 28 of Figure 7 of the source: a uniform answer that encodes a nonzero multiple of the base point, redrawn as the encoding of `a g` for a uniform nonzero `a`, is still uniform.
It assumes that the base point is nonzero, that `2` is nonzero in the scalars, that the encoding is semi-injective, and that opposite points share their encoding; the encoding is then exactly 2-to-1 on those points.
So it covers ECDSA, not the injective case of Definition 2 (b) of the source.
The redraw takes the test of the image as an argument, with a hypothesis that it agrees with a search of the encodings of the nonzero multiples of the base point; part (a) of Definition 2 asks that this test be efficient, which EthLib does not model.
`prEvent_inverse_le_dlog` (`Proofs/Secp256k1/Security/InverseCase.lean`) bounds, in the key-only run with independent answers and new forward answers asked outside, the chance that the check passes on a point that was not a new forward query.
The event does not require the flag of repeated answers to be clear, so with the fork index of the forward case it covers every run that wins.
The bound is the advantage of a discrete-logarithm solver, which runs the forger once with the same test of the image; this is the step from Game G2 to Game G3 of the source.
The solver's game is the discrete-logarithm game of the oracle framework, which draws the key from all scalars, while Definition 1 of the source draws it from the nonzero scalars.
The two advantages differ by at most `1 / n`, where `n` is the number of scalars; no theorem states it.
`keyOnlyAdvantage_le` (`Proofs/Secp256k1/Security/KeyOnlyBound.lean`) assembles these parts into the bound of Theorem 2 of the source, for a key-only forger with at most `q` queries to the bijection or its inverse on every key.
The bound charges three adversaries built from the forger: the two discrete-logarithm solvers and the reduction to division resistance.
It is a bound on the key-only game only.
`forgeAdvantage_le_noCollisionAdvantage_add_collisionAdvantage` (`Proofs/Secp256k1/Security/Collision.lean`) is the first step of Theorem 1 of the source, from Game G0 to Game G1 of Figure 4.
It charges a forgery on a new message with the hash of a signed one to a finder of collisions built from the forger, which samples the bijection lazily.
The hash is fixed, so the bound charges that named finder and no adversary against collisions in general.
`noCollisionAdvantage_le_programmed` (`Proofs/Secp256k1/Security/Programmed.lean`) is the step from Game G1 to Game G2 of Figure 5, where the signer programs the bijection; it costs the chance of a conflict, two pairs of the cache of the bijection that share a query or an answer.
`prEvent_programmedExperiment_conflict_le` (`Proofs/Secp256k1/Security/Conflict.lean`) bounds that chance, for a forger with at most `q_Π` queries to the bijection or its inverse and `q_S` signing queries on every key, when the base point is nonzero and the encoding semi-injective.
The signer tries up to `fuel` nonces per request where the source's tries one, so the source's `Q_s` programmed pairs become `fuel · q_S`; the check of the forgery may relay one more query, which Definition 4 of the source rules out, so its `Q_Π` becomes `q_Π + 1`.
`keylessExperiment_evalDistEq_programmedExperiment` (`Proofs/Secp256k1/Security/Keyless.lean`) is the step from Game G2 to Game G3 of Figure 5: the game with a signer that reads only the public key has the same law, forgery, check result and final states, when the base point is nonzero.
The source's claim that the forger wins as often in both games does not follow as written: its Game G2 records a pair of the bijection before its checks (line 14), while its Game G3 records one only when a nonce signs (line 40).
The signer without the key here records the pairs of failed nonces too.
`prEvent_keylessExperiment_win_le` (`Proofs/Secp256k1/Security/KeylessForger.lean`) charges a win of that game to two adversaries built from the forger: the key-only forger of Figure 6 of the source, which runs the game with its own bijection oracle, and a solver of the discrete logarithm.
The two checks agree unless the most recent pair at the forgery's point is one that the signer programmed; that case gives the key, and the solver tries each candidate and keeps the one that gives the public key.
Figure 6 of the source signs again at line 30 when the point is programmed, which may fail, so its claim that the key-only forger wins as often as Game G3 does not hold exactly; the bound here charges that case to the named solver instead, which adds one discrete-logarithm term to Theorem 1.
The solver runs the game itself, with a lazy bijection; no theorem states its running time or the forger's.
`forgeAdvantage_le_keyOnly` (`Proofs/Secp256k1/Security/ChosenMessageBound.lean`) assembles these steps into Theorem 1 of the source, for a forger with at most `q_Π` queries to the bijection or its inverse and `q_S` signing queries on every key: its advantage is at most the key-only forger's advantage, plus the advantage of the solver for a programmed point, plus the finder's advantage, plus the bound on a conflict.
`forgeAdvantage_le` (same file) bounds the key-only forger's advantage in turn by `keyOnlyAdvantage_le`, with `q = q_Π`, which gives a bound on the chosen-message game by three solvers of the discrete logarithm, a reduction to division resistance, a finder of collisions, and terms in the sizes of the bijection's domain and of the scalars.
It needs a nonzero base point, `2` nonzero in the scalars, a semi-injective encoding under which opposite points share their encoding, a normal form that keeps or negates `s`, and a test of the image that agrees with the search over the nonzero multiples of the base point; so it covers the case of Definition 2 (b) of the source with opposite points sharing their encoding, as for ECDSA, and not the injective case; the model's ECDSA scheme meets the hypotheses on the scheme by separate lemmas, and no theorem applies the bound to it.
It keeps the departures of its steps from Theorem 1, among them: the signing oracle answers a repeated message from its cache, as RFC 6979 does, the hash is fixed and the bound charges named reductions, no running times are stated, the key is drawn from all scalars, `Q_s` becomes `fuel · q_S` and `Q_Π` becomes `q_Π + 1` in the conflict bound, the signer without the key records the pairs of failed nonces, and the forgery at a programmed point is charged to a solver of the discrete logarithm, one term more than the source's bound.
The bound on a conflict keeps the three terms of the source's proof, in the form of its own module, before the source sums them into `3 Q Q_s / ((q - 1) / 2 - Q)`; no theorem compares the two.
The departures of the key-only bound from Theorem 2 are listed with it, above.
`ecdsa_verify_eq_verify_ecdsaScheme` (`Proofs/Secp256k1/Security/Refinement.lean`) proves that `verify` is the game's verification, with the bijection the identity, for `r` and `s` below `n`.
`exists_signNonce_of_sign` proves that every signature from `sign` is the game's signature for some nonzero nonce; that is correctness of signing, and says nothing about how RFC 6979 draws the nonces.
The game draws the bijection uniformly, so the bound on it applies to EthLib, where the bijection is the identity, only under the heuristic of the source that the identity behaves as a bijective random oracle.
It would also need the pseudorandomness of RFC 6979, which no theorem states, and it ignores the 16-nonce limit and the failure of `sign` when `x_R >= n`.
A forger of transactions only needs a key with the right address, so a bound for them also needs a term for the Keccak-256 hash of the key.
The low-s rule of transactions only restricts the forger, so it needs no term.
The model's encoding, the `x` coordinate as a 256-bit string, meets part (b) of Definition 2 of the source (`ecdsaScheme_semiInjective`), which their Lemma 2 proves.

`ecdh_eq_ok_iff` (`Proofs/Secp256k1/Ecdh.lean`) states ECDH in the group of the curve.
It is the Diffie-Hellman primitive of SEC 1 v2 §3.3.1, with no key derivation function.
By it, ECDH returns a secret exactly when the public key is a point of the curve other than `O` and the private key is nonzero.
The secret is then the `x` of their product, as 32 big-endian bytes.

### ENR "v4" records

`verifyV4_negS` (`Networking/Proofs/Enr/Security.lean`) proves that a record with a 64-byte signature verifies exactly when its copy with `n - s` does, and `negS_ne_of_verifyV4` that the two differ.
`ecdsaForgery_of_forgery` (`Networking/Proofs/Enr/Security.lean`) proves that a forged EIP-778 "v4" record gives a forgery of ECDSA with Keccak-256 on a fresh message.
The security of records then rests on the chosen-message security of that ECDSA, which EthLib assumes and does not prove; the bound on the chosen-message game above is proved only in the bijective random oracle model.

### alt_bn128

The alt_bn128 theorems check the constants and the group law of `G_1`, which the ECADD, ECMUL and ECPAIRING precompiles use.
`modulus_prime` (`Proofs/AltBn128/Field.lean`) proves that the base field modulus `p` and the group order `q` are prime.
`toPoint_add` and `toPoint_mulBits` (`Proofs/AltBn128/Curve.lean`) prove that addition and double and add agree with the group law of `y^2 = x^3 + 3` over `ZMod p`.
`card_point` (`Proofs/AltBn128/Order.lean`) proves that this group has `q` points, so the cofactor is 1.

`instField` (`Proofs/AltBn128/Fp2.lean`) proves that `Fp2` is a field, and `toPoint_add` (`Proofs/AltBn128/Twist.lean`) proves the group law of the twist that holds `G_2`.
`mulBits_order_eq_infinity_iff` proves that the `G_2` subgroup check of ECPAIRING accepts exactly the points `Q` on the twist with `q Q = O`.
`addOrderOf_generator` (`Proofs/AltBn128/G2Order.lean`) proves that the generator `P2` of EIP-197 lies on the twist and has order `q`.
`instField` (`Proofs/AltBn128/Fp12.lean`) proves that `Fp12`, where the pairing lands, is a field with the product of the specification.
`card_eq` proves that it has `p^12` elements, and `irreducible_poly` that `X^12 - 18 X^6 + 82` is irreducible over `ZMod p`.
`finalExponentiation_eq_pow` (`Proofs/AltBn128/FinalExponentiation.lean`) proves that the final exponentiation of the pairing check raises its argument to `(p^12 - 1) / q`.
`slopeLine_eq` and `verticalLine_eq` (`Proofs/AltBn128/Lines.lean`) prove that the lines of the Miller loop, written by their coefficients, are the textbook lines `l w (xt - x1 w^2) - (yt - y1 w^3)` and `xt - x1 w^2` in `Fp12`.
`pairing_eq_finalExponentiation_loop` (`Proofs/AltBn128/MillerChain.lean`) proves that the pairing of `P` and `Q` is the final exponentiation of three values at `P`.
Here `Q` lies on the twist with `q Q = O`, `Q'` is its untwist, and `pi` is the `p`-th power map.
The first value is Miller's algorithm (`Proofs/MillerFunction.lean`) for `6 u + 2` and `Q'`.
The others are the line through `(6 u + 2) Q'` and `pi(Q')`, and the line through their sum and `-pi(pi(Q'))`.
This is the optimal ate pairing of Beuchat et al. (ePrint 2010/354, §2).
`untwist_frobenius` proves that the Frobenius map of the specification is `pi` under the untwist.

`AltBn128.pairingBilinear` (`Proofs/AltBn128/PairingAte.lean`) proves that the pairing is bilinear on the multiples of the generators: `e(a P1, b P2) = e(P1, P2)^(a b)` for all `a` and `b` in `Fr`.
`orderOf_pairing_generators` (`Proofs/AltBn128/Nondegenerate.lean`) proves that the pairing of `P1` and `P2` has order `q`, so it is not 1; the kernel evaluates that pairing.
`pairingCheck_eq_true_iff` (`Proofs/AltBn128/PairingBilinear.lean`) proves that the check passes exactly when the product of the pairings of its pairs is 1.
The pairing law is stated as a structure, `AltBn128.PairingLaws` (`Proofs/AltBn128/PairingLaws.lean`), in the shape of the BLS one.
It states the check of EIP-197: the pairs `(a_i P1, b_i P2)` pass exactly when `sum_i a_i b_i = 0`.
`PairingLaws.of_bilinear` (`Proofs/AltBn128/PairingBilinear.lean`) derives it from one smaller hypothesis, `PairingBilinear`: `e(a P1, b P2) = e(P1, P2)^(a b)` for all `a` and `b` in `Fr`.
`AltBn128.pairingLaws` (`Proofs/AltBn128/PairingAte.lean`) proves `AltBn128.PairingLaws` from it.
`Ate.frobenius_generator` (`Proofs/AltBn128/PairingAte.lean`) proves, by a kernel computation on the twist, that the Frobenius map of the specification sends `P2` to `p P2`.
`Ate.frobenius_of_mem` proves that `pi` acts as `p` on the untwist of `G_2`.
`Ate.eq_zero_of_frobenius_eq` proves that `pi` fixes only `O` there, because `q` does not divide `p - 1`.
`Ate.ratioDivisor_ateLines` proves that the three values of the pairing, with the verticals through the two sums, have the divisor `s ((Q') - (O)) + ((pi Q') - (O)) + ((pi^8 Q') - (O)) - ((pi^9 Q') - (O))`, with `s = 6 u + 2`.
`Ate.pow_ateExponent` proves that `z^(N (s + p + p^8 - p^9))` is 1 for every nonzero `z` in `Fp12`, with `N = (p^12 - 1) / q`.
`Ate.ateValue_add_left` proves that these lines at `P`, raised to `N`, are linear in a point `P` that `pi` fixes.
`Ate.ateValue_add_right` proves that they are linear in `Q'` on the untwist of `G_2`.
`Ate.pairing_eq_ateValue` proves that the pairing of a finite `P` on the curve and a `Q` on the twist whose untwist lies in `G_2` is that value.
`Point2.nsmul_order_eq_zero_iff` (`Proofs/AltBn128/G2Torsion.lean`) proves that every point `Q` with `q Q = O` on the twist is a multiple of `P2`, as EIP-197 says.
`Point2.mulBits_order_eq_infinity_iff_exists` restates it for the subgroup check of ECPAIRING, and `Point.exists_eq_mulBits_generator` (`Proofs/AltBn128/Order.lean`) does the same for `P1`.
`exists_mulBits_generator_of_decodePair` (`Execution/Proofs/Evm/Precompiles/AltBn128/Pairing.lean`) combines them: every pair that ECPAIRING decodes is a pair of multiples of the generators, where the law above holds.
`exists_represents_of_decodePairs` and `exists_represents_of_ecpairing` (`Execution/Proofs/Evm/Precompiles/AltBn128/PairingProduct.lean`) lift this to lists of scalars `a_i` and `b_i` in `ZMod q`, for every successful decoding and every successful call.
`ecpairing_eq_one_iff` and `ecpairing_eq_zero_iff` apply `AltBn128.pairingLaws`, with no hypothesis on the pairing.
On a successful call, they prove that ECPAIRING returns the word 1 exactly when `sum_i a_i * b_i = 0`, and the word 0 otherwise.
`ecpairing_encodePairs` computes the output on the encodings of represented pairs, and `ecpairing_generators`, `ecpairing_generator_neg` and `ecpairing_empty` reach both outputs.

`ecadd_toPoint` and `ecmul_toPoint` (`Execution/Proofs/Evm/Precompiles/AltBn128/Group.lean`) carry this group law to the precompiles.
A call of ECADD that succeeds returns the sum of its two points, and a call of ECMUL returns its point times its 32-byte scalar.
`bytesToG1_eq_ok_iff` (`Execution/Proofs/Evm/Precompiles/AltBn128/Encoding.lean`) proves that the decoder of a point of `G_1` accepts 64 bytes exactly when they are the EIP-196 encoding of a point on the curve.
`bytesToG1_ecadd` and `bytesToG1_ecmul` (`Execution/Proofs/Evm/Precompiles/AltBn128/Group.lean`) prove that the output of a call of ECADD or ECMUL that succeeds decodes to that sum or that product.

`decodePair_eq_ok_iff` (`Execution/Proofs/Evm/Precompiles/AltBn128/Pairing.lean`) proves that a pair of ECPAIRING decodes exactly when its two points decode and `q Q = O` holds for its point `Q` of the twist.
`Point.mulBits_order` (`Proofs/AltBn128/Order.lean`) proves `q P = O` for every point `P` on the curve.
So the curve equation is enough for `G_1`, as EIP-197 says, and the decoder checks the order of the point of the twist only.

### secp256r1

The secp256r1 theorems are correctness statements, like those of secp256k1.
`modulus_prime` (`Proofs/Secp256r1/Field.lean`) proves that both moduli are prime.
`toPoint_add` (`Proofs/Secp256r1/Curve.lean`) proves that the addition of SEC 1 is the group law of the curve.
`card_point` (`Proofs/Secp256r1/Order.lean`) proves that the group has `n` points, so the cofactor is 1.
That proof needs one more fact than the proof for secp256k1: `x^3 - 3 x + b` has no root mod `p`.
The kernel checks it by an inverse of `X^p - X` modulo the cubic.

`verify_sign` (`Proofs/Secp256r1/Ecdsa.lean`) proves that a signature from the signing operation of SEC 1 verifies.
`verify_eq_true_iff` states verification as the verifying operation of SEC 1 v2 §4.1.4, read in the group of the curve.
By it, a signature is valid exactly when the conditions below all hold.
Both `r` and `s` lie in `[1, n - 1]`, and the key is a point of the curve other than `O`.
The point `(e / s) G + (r / s) Q` must also be other than `O`, with `x mod n = r`.
`verify_iff_s_eq_or_neg` describes the signatures that verify next to a valid one.
Take a valid signature `(r, s)` under a key and a message, with `r + n >= p`.
The signatures `(r, s')` that verify under the same key and message are then exactly those with `s' = s` or `s' = n - s`.
For P-256, `p - n` is about `2^126`, so the bound excludes only the values of `r` below it.
No theorem states unforgeability.

### AES

The AES theorems are correctness statements, except the bounds on GHASH over a uniform hash subkey.
No theorem bounds tag forgery or states a security property of the cipher.
`invCipher_cipher` and `ciphInv_ciph` (`Proofs/Aes/Block.lean`) prove that the inverse cipher of FIPS 197 undoes the cipher, for every key schedule and so for every key.
`sbox_eq` proves that each entry of the S-box table equals the inverse in GF(2^8) followed by the affine map of FIPS 197 §5.1.1.
`ciph_eq_spec` proves that AES-128 and AES-256 equal a model of FIPS 197, for every key and every block.
The model follows Algorithms 1 and 2 of FIPS 197 over the state `s[r, c]` of §3.4.
It multiplies bytes as polynomials modulo `m(x)`, and it builds its S-box from the inverse `b^254` and the affine map of §5.1.1.
So the model shares no table and no GF(2^8) arithmetic with the code.
`sbox_eq_spec` proves that each entry of the S-box table equals the S-box of the model.
`getElem_keyExpansion_of_lt` proves that the first `Nk` words of the key schedule are the words of the key.
`getElem_keyExpansion_of_le` proves that each later word follows the recurrence of Algorithm 2, for a key of at least one word.
EthLib has no AES-192, so no theorem covers it.
No theorem compares the inverse cipher with a model of Algorithm 3.
`ciphInv_spec_ciph` proves only that the inverse cipher undoes the cipher of the model.
`ctr_ctr` (`Proofs/Aes/Ctr.lean`) proves that CTR decryption of SP 800-38A returns the plaintext, for every forward cipher and initial counter.
`repeat_inc_injOn` proves that, for `m <= 128`, the first `2^m` counters that the standard increment gives from one block are distinct.
The CTR keystream applies one increment per block, so these are the counters of the first `2^m` blocks of a message, as Appendix B.1 states.
`ctr_block` states that link: block `j` of the output is block `j` of the data XORed with the cipher of the first counter incremented `j` times.
`repeat_inc_two_pow` proves that the counter after `2^m` increments is the first one again.
The Python tests (`bindings/python/tests/aes/test_aes.py`) check FIPS 197 Appendix B and the AES-128 and AES-256 vectors of its 2001 Appendix C.
They also check the CTR examples F.5.1, F.5.2, F.5.5 and F.5.6 of SP 800-38A.

`decrypt_encrypt` (`Proofs/Aes/Gcm.lean`) proves that GCM decryption of SP 800-38D returns the plaintext of an honest ciphertext and tag.
`decrypt_eq_ok` proves that decryption accepts no tag other than the honest one.
`decrypt_eq_ok_iff` proves that decryption returns `p` exactly when `p` encrypts to the given ciphertext and tag.
So every pair that decryption accepts is an honest encryption.
The three hold for every forward cipher.
`residue_mul` (`Proofs/Aes/GaloisField.lean`) proves that the block product of SP 800-38D §6.3, Algorithm 1, is the product of the two blocks read as polynomials over GF(2) modulo `1 + u + u^2 + u^7 + u^128`.
`residue_xorBlock` proves that XOR is their sum, and `residue_injective` that two different blocks have two different residues.
`residue_ghash` proves that GHASH of `X_1 ... X_m` is `X_1 H^m + ... + X_m H` on residues, the form that §6.4 states.
`irreducible_modulus` (`Proofs/Aes/Field.lean`) proves that the modulus is irreducible over GF(2), so the residues form a field, and `card_adjoinRoot_modulus` that this field has `2^128` elements.
The kernel checks a certificate of the test: 128 squarings by Algorithm 1 fix `u`, and a block inverts `u^(2^64) - u`.

`prEvent_xorBlock_ghash_eq_le` (`Proofs/Aes/Universal.lean`) takes two different lists of `m` blocks and a target block `c`.
It proves that a uniform hash subkey gives XOR `c` on their GHASH values with probability at most `m / 2^128`.
`prEvent_xorBlock_ghash_singleton_eq` proves that on distinct one-block inputs this probability is `1 / 2^128`.
`ghash_zeroBlock_cons` proves that a zero block in front does not change GHASH, so `[X]` and `[0, X]` agree for every key.
`prEvent_xorBlock_ghash_ghashInput_eq_le` proves the bound on GCM's padded input, for two different pairs of additional data and ciphertext with each string below `2^64` bits.
This is Lemma 2 of McGrew and Viega, [ePrint 2004/193](https://eprint.iacr.org/2004/193), Appendix A, without output truncation.
Its numerator `m` is the length of the longer of their two padded lists, the length block included.
The bound counts uniform hash subkeys; it does not bound tag forgery and says nothing about the cipher.

`gctr_inc_block` proves that GCM encrypts block `k` of the text under `J_0` incremented `k + 1` times.
`counter_ne_preCounter` and `counter_injOn` assume the length checks of §5.2.1.1.
Under them, the counters of the text differ from each other and from `J_0`, the counter of the tag.
`encrypt_shortTag` and `decrypt_shortTag` prove that both functions reject the 64-bit and 32-bit tags, which SP 800-38D Appendix C restricts.
The Python tests check seven test cases of the NIST CAVP file `gcmtestvectors.zip`, one of them a forged tag that decryption rejects.

### X25519 and ChaCha20-Poly1305

The X25519 proofs cover the clamp of RFC 7748 §5 and the decoding of a coordinate (`Proofs/X25519.lean`).
`decodeScalar_eq` proves that the clamp sets bit 254, clears bits 0 to 2 and bit 255, and keeps bits 3 to 253 of the key.
`decodeScalar_mod_eight`, `le_decodeScalar` and `decodeScalar_lt` follow: a clamped scalar is a multiple of eight, at least `2 ^ 254` and below `2 ^ 255`.
`val_decodeUCoordinate` proves that decoding clears bit 255 and reduces modulo the field prime, so a noncanonical coordinate is accepted.
`decodeUCoordinate_encodeUCoordinate` proves that decoding the bytes of a reduced coordinate returns it.
`ladder_mod_two_pow` proves that the bits of the scalar above bit 254 do not change the ladder.
So no run of the ladder can observe the cleared bit 255; only the clamp theorems record it.
`swap_ladder_decodeScalar` proves that a clamped scalar leaves no swap pending at the end of the ladder.

The ladder computes a scalar multiple on Curve25519, and X25519 is a key agreement (`Proofs/MontgomeryCurve.lean`, `Proofs/X25519/`).
The curve `v ^ 2 = u ^ 3 + 486662 u ^ 2 + u` is the Weierstrass curve with `a₂ = 486662` and `a₄ = 1`, so the group law that Mathlib proves applies to it.
`Represents.double` and `Represents.diffAdd` prove the doubling and the differential addition of RFC 7748 §5 on projective u-coordinates.
They hold for every point, the point at infinity and the points of order 2 included, over any field in which `2 ≠ 0`.
The differential addition needs the u-coordinate of the difference of its two points, and that coordinate must not be `0`.
`ladder_represents` takes a point `P` whose u-coordinate is not `0` and a scalar `k` below `2 ^ 255`.
After the pending swap, the ladder ends with projective u-coordinates of `[k] P` and `[k + 1] P`.
`x25519_encodeUCoordinate` follows: X25519 of the encoded u-coordinate of such a point encodes the u-coordinate of `[k] P` for the clamped scalar `k`, and `0` when `[k] P` is the point at infinity.
`modulus_prime` and `order_prime` prove, by Pratt certificates that the kernel checks, that `2 ^ 255 - 19` and the order `ℓ` of RFC 7748 §4.1 are prime.
`addOrderOf_basePoint` proves that the base point `(9, v)` has order `ℓ`, from one run of the ladder that the kernel evaluates.
`uCoord_decodeScalar_smul_ne_zero` proves that `[k] B` has a u-coordinate other than `0` for every clamped scalar `k`, since `k` is a multiple of 8 with `2 ^ 254 ≤ k < 2 ^ 255 < 8 ℓ`.
`x25519_agree` proves the agreement of RFC 7748 §6.1: X25519 of the key `a` on the public key of `b` equals X25519 of `b` on the public key of `a`, for every pair of keys.
No theorem covers an input u-coordinate of `0`, a noncanonical encoding, or a u-coordinate on the quadratic twist of the curve, though X25519 accepts all three.
No theorem assumes or bounds the hardness of the Diffie-Hellman problem on the curve.

The ChaCha20-Poly1305 proofs cover output length, counter exhaustion, rejection of a wrong tag and the round trip (`Proofs/ChaCha20Poly1305.lean`).
`crypt_crypt` proves that the cipher, run twice under one key, counter and nonce, gives back its input.
`decrypt_encrypt` proves that decryption of an honest ciphertext and tag returns the plaintext.
`tag_eq_of_decrypt_eq_ok` proves that no other tag passes for that ciphertext.
These are statements about the definitions alone, not about their security.
The clamp of the Poly1305 key has its own theorem.
`testBit_clampR` gives every bit of `r` without the mask, by its place in the little-endian 32-bit words of `r`: the top four bits of bytes 3, 7, 11 and 15 and the bottom two bits of bytes 4, 8 and 12 are clear, and every other bit of the low 16 bytes of the key is kept.
So a clamp with another mask would fail it.
`clampR_lt` bounds `r` by `2 ^ 124`.
`poly1305Accumulator_lt` proves that the accumulator stays below the prime `2 ^ 130 - 5`, whatever `r` and the message, since each step reduces modulo the prime.
The cipher and the keystream have their own theorems.
`crypt_eq_ok_iff` gives every byte of the output of the cipher.
Byte `j` is byte `j` of the input XOR byte `j % 64` of the block whose counter is the initial counter plus `j / 64`.
So a keystream shorter than the input, which leaves its last bytes in plaintext, or a counter that repeats, would fail it.
`encrypt_eq_ok_iff` gives the AEAD ciphertext in the same terms, with the counter starting at 1.
It gives the tag too: the Poly1305 tag of the MAC input of RFC 8439 §2.8, written out, under the first 32 bytes of block 0.
`byteAt_keyStream` and `size_keyStream` give the keystream itself.
`pad16_eq_iff` proves that the padding of the MAC input is the fewest zero bytes that complete a multiple of 16, so aligned input gets none.
`getElem_serializeState` gives each byte of the serialized state, the least significant byte of each word first.
`stateOfBytes_serializeState` and `serializeState_stateOfBytes` prove that reading 64 bytes as a state undoes the serialization.
No theorem relates ChaCha20-Poly1305 to an independent model of RFC 8439.
The Python tests compare the bindings with the RFC 7748 and RFC 8439 vectors.
The million-iteration X25519 vector requires `ETHLIB_SLOW_VECTORS=1`.

### libp2p TLS certificates

`authenticate` (`Networking/Libp2p/Tls.lean`) follows the "Peer Authentication" and "libp2p Public Key Extension" sections of [libp2p TLS](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md) at commit `c750236`.
It checks that the chain holds one certificate, its validity interval, its self-signature, the libp2p extension and the host-key signature.
The caller chooses the accepted host and certificate algorithms, and whether a unique ID is rejected.
libp2p TLS leaves these choices open, so EthLib defines no default profile.

The host keys checked are secp256k1 and P-256, with an uncompressed named-curve key.
Ed25519, RSA and other ECDSA host keys are rejected as unsupported algorithms, so vector 1 of libp2p TLS fails.
The only self-signature algorithm checked is ECDSA on P-256 with SHA-256.
A secp256k1 host signature must have a low s, as the peer ID rules require; a P-256 signature need not.
Every critical extension other than the libp2p one is rejected, because no other extension is understood.
Non-critical extensions other than the libp2p one are ignored.
Names are checked as DER but never compared, and no certification path is validated.
Name strings may be UTF8String, PrintableString, IA5String, BMPString or UniversalString; a TeletexString is rejected.
The reader accepts any serial number, and either time form for any year.
RFC 5280 §4.1.2.2 asks certificate users to handle unusual serial numbers, and §4.1.2.5 to process both time forms.

`authenticate_ok_iff` and `authenticateCertificate_ok_iff` (`Networking/Proofs/Libp2p/Tls.lean`) state every check that success requires: the single chain, the validity interval, the unique-ID rule, the algorithms, the self-signature and the host key.
`authenticate_peerId` says that the returned peer ID belongs to the host key in the libp2p extension.
For a secp256k1 key it is the identity peer ID of the key's point, and for a P-256 key the SHA-256 peer ID of its protobuf.
In both cases the host signature verifies over `libp2p-tls-handshake:` and the certificate's exact encoded key.
`authenticate_single`, `authenticate_empty`, `authenticate_validity`, `authenticate_extension` and `authenticate_critical` reject a chain of another length, a time outside the interval, a missing libp2p extension and another critical extension.
`authenticatePeer_peerId` proves that a dialer that succeeds gets the peer ID it expected.
These are correctness properties of the checks, not an unforgeability theorem.
`read_ok_iff` (`Serialization/Proofs/Der.lean`) states the DER reader in the terms of X.690 §§8.1.2, 8.1.3, 8.1.5 and 10.1.
A read takes one identifier octet with a low tag number, other than 0, the length on the fewest octets, the content and the rest.
`encoded_eq_of_read_ok` derives that a tag and a content have a single encoding.
`integer_ok_iff` states that an INTEGER reads as `i` exactly when its content is `i` in two's complement on the fewest octets (X.690 §8.3).
`natural_ok_iff` states the nonnegative case.
`content_eq_of_integer_ok` derives that an integer has a single content.
`readTime_eq_ok_iff` states exactly which certificate times read, and their value (RFC 5280 §4.1.2.5).
A UTCTime is accepted for a year from 1950 to 2049, and a GeneralizedTime for a year from 1 to 9999.
Both must hold a valid proleptic Gregorian date, a time of day without a leap second, and `Z`.
The value counts 86400 seconds for each day from 1970-01-01, then adds the time of day.
The days are counted in a calendar model of year and month lengths, not in the reader's closed form.
`readValidity_eq_ok_iff` says that a validity reads as two such times in order.
`readCertificate_validity` says that the endpoints of a parsed certificate are what its own validity field reads as.
That field is located in the signed part that the input bytes encode.
`boolean_ok_iff` states that a BOOLEAN is one octet, FF for TRUE and 00 for FALSE (X.690 §§8.2, 11.1).
`bitString_ok_iff` states that the BIT STRING reader accepts exactly the octet 0, then the octets it returns.
`validBits_ok_iff` states that BIT STRING contents count at most 7 unused bits, all zero (X.690 §§8.6.2, 11.2.1).
The trailing zero bits of a named bit list (X.690 §11.2.2) are not checked, since the reader does not know the type.
`fixedString_eq_true_iff` states that code units of a fixed width pass exactly when they write Unicode scalar values big-endian.
The reader takes a scalar value to be at most 10FFFF and outside D800 to DFFF.
X.690 also forbids a leading signature and some control functions (§§8.23.7 to 8.23.9), which the reader does not check.
A BMPString may also hold FFFE or FFFF, which X.680 §41.15 leaves out of its character set.
`validate_go_boolean_ok_iff`, `validate_go_bitString`, `validate_go_bmpString_ok_iff` and `validate_go_universalString_ok_iff` state what validation accepts for one value of these tags, for any positive fuel; no theorem shows that each nested value receives it.
`validate_boolean_ok_iff`, `validate_bitString`, `validate_bmpString_ok_iff` and `validate_universalString_ok_iff` give the same at the top, as the certificate reader validates each Name attribute value and each algorithm parameter.
No theorem states the validation of INTEGER, OCTET STRING, OBJECT IDENTIFIER, NULL, UTF8String, PrintableString or IA5String, nor the rejection of every other tag.
No theorem states the validation of a SEQUENCE or a SET OF, its order or its children.
Nothing in Lean shows that authentication can succeed; the Python tests check vectors 1 to 4 of libp2p TLS.

### QUIC wire encodings

RFC 9000 §16 writes an integer below `2^62` in 1, 2, 4 or 8 bytes, and the two high bits of the first byte give the length.
`Varint.decode_encodeWith` (`Networking/Proofs/Quic/Varint.lean`) proves the round trip for every value and every width that holds it, with arbitrary trailing bytes.
`Varint.eq_encodeWith_of_decode` proves the converse: every input that decodes is the encoding of its value at the width its first byte selects, followed by the rest.
`Varint.minWidth_le` and `Varint.length_encode_le` prove that the encoder picks the shortest width.
`Varint.decode_nil` and `Varint.decode_error_iff` prove that the decoder fails, always as truncated, exactly when the input ends before the selected integer does.
The integer decoder accepts longer forms, and `Frame.decode` accepts only shortest frame types (§12.4).
The Python suite checks the examples of RFC 9000 Appendix A.1, the bounds of Table 4 and the rejection of `2^62`.
It also checks three longer forms of 37 and every proper prefix of one encoding of each width.

`Packet.decode_encode` (`Networking/Proofs/Quic/Packet.lean`) proves the round trip for well-formed headers, with arbitrary trailing bytes after a protected header.
Retry and Version Negotiation consume the rest of the datagram, since neither has a Length field (RFC 9000 §12.2).
`Packet.decodePacketNumber_mod` and `Packet.decodePacketNumber_lt` prove that a reconstructed packet number keeps the received low bytes and stays below `2^62`.
`Packet.decodePacketNumber_closest` proves that no other such value is closer to the expected number, as RFC 9000 Appendix A.3 intends.
The sender's choice of width from its unacknowledged range (§17.1, Appendix A.2) is left to the caller.

`Frame.decode_encode` (`Networking/Proofs/Quic/Frame.lean`) proves the round trip for an encoded frame permitted in its packet type.
A STREAM frame without LEN consumes the remaining packet, so its round trip has no trailing bytes.
`Frame.decode_ne_ok_of_not_allowed` proves that a frame forbidden by Table 3 cannot be accepted.
`Frame.valid_of_decode` proves that a decoded frame meets the format checks.
They cover ACK range underflow, offset limits, stream-count limits, token lengths, connection-ID lengths and the retirement order of §19.15.
A frame body that ends early or breaks one of these checks is FRAME_ENCODING_ERROR (§20.1).
`Frame.valid_ack_iff` states the ACK check against the ranges that RFC 9000 §19.3.1 computes from Largest Acknowledged, First ACK Range, Gap and ACK Range Length.
An ACK frame passes it exactly when none of those ranges reaches below packet number 0.
Each additional range lowers the packet number by at least two, so that also keeps their count a QUIC integer.
`Frame.ackedRanges_nonneg_of_decode` applies it to a decoded ACK frame.

The Python cases include the RFC 9000 Appendix A.3 packet number and the header bytes of RFC 9001 Appendices A.2, A.4 and A.5, alongside hand-derived layouts of every frame type.
The header decoder expects its caller to remove header protection and authenticate the payload first, so a reserved-bit error comes only after authentication (RFC 9000 §17.2).
The caller also checks a long header's Length against the bytes that follow it.
These codecs do not implement transport state, flow-control credit, sender-role checks or packet protection.

### QUIC v1 key derivation

The labelled HKDF proofs (`Cryptography/Proofs/Hash/Tls13.lean`) state the field bounds of RFC 8446 §7.1, the label encoding and agreement with HKDF-SHA-256.
The QUIC proofs (`Networking/Proofs/Quic/Keys.lean`) state the Initial and packet key derivations of RFC 9001 §5.1 and §5.2 and prove that they succeed.
The keys have their required lengths in their types for AES-128-GCM and ChaCha20-Poly1305 with SHA-256.
The Python suite checks the secrets, keys and labels of RFC 9001 Appendix A.1, and the keys of Appendix A.5.
Anyone who sees the client's first Destination Connection ID can compute the Initial secrets, as RFC 9001 §5.2 says.
These results establish neither cryptographic security nor constant-time execution.

### TLS 1.3 key schedule

The no-PSK SHA-256 schedule takes a shared secret and encoded transcripts from its caller.
`keySchedule_ok` and `keySchedule_eq_ok_iff` (`Networking/Proofs/Quic/Tls.lean`) prove that it succeeds and state its seven secret derivations.
`keySchedule_congr_hash` proves that the schedule reads each transcript only through its SHA-256 hash.
`finished_ok` and `deriveSecret_ok` prove that the Finished value and Derive-Secret succeed, the latter for every label within the bounds of §7.1.
The Python suite checks the secrets and Finished values of RFC 8448 §3.
The schedule's results do not cover message parsing, negotiation, peer authentication or the Diffie-Hellman exchange.
The schedule does not check the shared secret, and the SHA-384 schedule of TLS_AES_256_GCM_SHA384 is absent.
The certificate, group and signature policy questions of [#2163](https://github.com/ethereum/EthLib/issues/2163) remain open.
These results establish neither cryptographic security nor constant-time execution.

### TLS 1.3 handshake codecs

`decode_encode` and `encode_injective` (`Networking/Proofs/Quic/Tls/Messages.lean`) prove that every successfully encoded handshake message recovers its fields, with arbitrary trailing bytes, and that successful encodings are injective.
The messages are ClientHello, ServerHello, EncryptedExtensions, CertificateRequest, Certificate, CertificateVerify and Finished, with the layouts of RFC 8446 §4.
The caller supplies the hash length of Finished.
The decoders check field bounds, the fixed TLS 1.3 legacy fields and duplicate extension types.
No theorem yet states the converse: that every input a decoder accepts is the encoding of its result.
So these checks rest on the code and the Python tests, not on a proof.
They preserve extension order, opaque certificate bytes, opaque extension data and unrecognized two-byte identifiers.

`decodePayload_encodePayload` (`Networking/Proofs/Quic/Tls/Extensions.lean`) proves the round trip for every payload form.
The forms are supported and selected versions, supported groups, signature algorithms, the three key-share forms, ALPN and opaque QUIC transport parameters.
The caller chooses the payload form from its message context; parsing a message alone does not validate these opaque payloads.

The Python suite checks message layouts and payload bounds against the RFC wire formats.
It also parses and re-encodes the RFC 8448 §3 trace.

These codecs define no accepted cipher-suite, group, signature-scheme or libp2p certificate profile.
They do not check negotiation, extension placement, required extensions, message order, key shares, certificate authentication, signatures or Finished values.

### TLS 1.3 transcripts

`Transcript.append` retains exactly the received bytes of one complete SHA-256 handshake message, including its four-byte header.
The transcript proofs (`Networking/Proofs/Quic/Tls/Transcript.lean`) state that preservation and the HelloRetryRequest replacement of RFC 8446 §4.4.1.
A retry replaces one saved ClientHello with a synthetic `message_hash`, then appends the received retry bytes.
A retry after another message or a second retry is rejected.
The transcript always hashes with SHA-256; the steps must reject a suite with another hash.

The Python suite checks the RFC 8448 §3 transcript, and its SHA-256 hash against an independent SHA-256.
It also checks the CertificateVerify signed content of RFC 8446 §4.4.3, including the zero separator and the role's context string.

The client and server steps, QUIC CRYPTO reassembly and encryption-level checks are absent.
The codecs reject NewSessionTicket and KeyUpdate, which a QUIC connection still carries after the handshake.
The maintainer policy questions of [#2163](https://github.com/ethereum/EthLib/issues/2163) remain open.

### QUIC v1 packet protection

`unprotect_protect` (`Networking/Proofs/Quic/Protection.lean`) proves the wire-packet round trip for AES-128-GCM and ChaCha20-Poly1305.
The round trip assumes that the receiver reconstructs the sent packet number.
RFC 9001 §5.5 notes that a long delay can break that reconstruction, and authentication then fails.
`removeHeaderProtection_applyMask` proves that header removal restores the fields under the mask of the unchanged ciphertext sample.
`unprotect_ok_iff` unfolds acceptance into header removal, packet-number reconstruction, AEAD authentication and the authenticated header checks.

The decoder checks reserved bits only after authentication, and checks a long header's Length against the isolated payload.
`unprotect_eq_error_of_decryptPayload` proves that an AEAD failure is reported before the checks of the authenticated header.
Nonzero reserved bits in an authenticated header give their own error, since RFC 9000 §§17.2 and 17.3.1 make them a connection error.
The other failures reject only this packet.
`unprotect_eq_reservedBits_iff` proves that this error comes only from a packet whose payload authenticates.
Initial packets require AES-128-GCM, as RFC 9001 §5 specifies.
The Python suite compares complete packets and Retry tags with RFC 9001 Appendices A.2 to A.5.
These operations do not track nonce reuse, key updates or AEAD usage limits, and the proofs establish no cryptographic security or constant-time execution.

### Noise XX and libp2p identities

`readLibp2p_authenticates` (`Networking/Proofs/Noise/Identity.lean`) says that the read of message 2 or 3 accepts only a payload whose signature verifies on the static key that the message carries.
The state then stores that remote, and completion returns it without reading a message or verifying the signature again.
`complete_ok` holds for any state: the returned remote is the stored one, its static key is the remote static key of the handshake, and the ciphers are those of that handshake.
`Produced.complete_authenticates` adds, for states that the libp2p initialize, write and read functions produce, that the signature verifies on that static key and that the public key decodes to the stored point.
A caller that edits the state can therefore complete with a remote whose signature does not verify.
`Produced.complete_isOk` says that completion of such a state after message 3 succeeds.
These are acceptance theorems, not a proof of protocol security, confidentiality or constant-time execution.
They relate the identity to the transport keys only through the shared handshake state.
The transcript of Noise §5.2 has its own theorems (`Networking/Proofs/Noise.lean`).
`chainingKey_foldl_mixHash` and `cipher_foldl_mixHash` prove that a run of transcript mixes leaves the chaining key and the cipher unchanged.
`eq_or_collision_of_hash_mixHash_eq` proves that two mixes that end at one handshake hash started at one handshake hash and mixed the same bytes, or else names the two different SHA-256 inputs that hash alike.
No theorem assumes or bounds the collision resistance of SHA-256, and none binds the whole transcript of a handshake.
`unframe_frame` proves that reading back a written frame of the noise-libp2p "Wire Format" returns its message.

`handshake_complete` (`Networking/Proofs/Noise/Handshake.lean`) is the correctness theorem of the raw XX handshake.
Two honest peers, with any static and ephemeral secrets and one prologue that both use, complete the three messages when each payload fits in its message.
Each read returns the payload that the other peer wrote.
Both peers end with the same symmetric state, and each stores the static public key of the other.
The send cipher of each peer is then the receive cipher of the other.
The proof uses `x25519_agree` for the three tokens `ee`, `es` and `se`, so it needs no assumption on X25519.
It says nothing about a peer that deviates from the specification, nor about secrecy.
`libp2p_complete` (`Networking/Proofs/Noise/Libp2pHandshake.lean`) lifts it to the libp2p suite.
It assumes that making each identity payload succeeds and that each payload fits in its message.
Making a payload fails on the zero secret or when signing fails, so its success is a hypothesis.
Each read of message 2 or 3 then succeeds, so, by `readLibp2p_authenticates`, it verified the signature of the other peer's identity key.
Completion returns, on each side, the static key, the identity key and the extensions of the other peer, with swapped ciphers.

The chaining key of each peer has its own theorems (`Networking/Proofs/Noise/Handshake.lean`).
For each message of XX, one theorem for writing it and one for reading it name the X25519 outputs that the chaining key mixes, in order; message 1 mixes none.
`chainingKey_writeMessage_readMessage_writeMessage` and `chainingKey_readMessage_writeMessage_readMessage` compose them for the initiator and the responder.
After message 3, each chaining key starts from the one that the protocol name sets, then mixes `ee`, `es` and `se` in that order.
Each token takes the local key that Noise §5.3 assigns to its role, and each remote key is the one that the final state stores.
If both peers computed `es` or `se` from their two ephemeral keys, they would still agree and `handshake_complete` would still hold, but these theorems would not.
No theorem ties a stored remote ephemeral key to the bytes of the message that carried it, and none states the cipher key that each mix sets.
Only the libp2p read verifies an identity, and completion checks that the stored remote has the remote static key of the handshake.
The raw transport split of an XX state checks neither.
The Python tests compare the raw XX handshake with a published test vector.
No published vector covers the libp2p payload, so its tests check the keys and signatures with independent code.

The payload codec of noise-libp2p "The libp2p Handshake Payload" has its own theorems (`Networking/Proofs/Noise/Identity.lean`).
`decodePayload_eq_ok_iff` proves that the decoder accepts exactly the protobuf messages of at most 65535 bytes, and gives the payload that it returns.
The identity key and the signature are the last length-delimited values of fields 1 and 2, or empty when there is none.
The extensions are absent when field 4 has no such value, and otherwise are those values joined in wire order.
A value of fields 1, 2 or 4 with another wire type is skipped, like an unknown field.
`encodePayload_eq_ok_iff` proves that the encoder writes fields 1 and 2, then field 4 only when there are extensions.
It returns the encoding exactly when it has at most 65535 bytes.
`decodePayload_encodePayload` proves that decoding an encoded payload returns that payload.
The decoder is not strict, so many byte strings decode to one payload, and no theorem says that an accepted string is an encoding.
No theorem reads the fields of the extension message.

The DER signature of an identity has its own theorems (`Networking/Proofs/Libp2p/PeerId.lean`).
`derInteger_eq` proves that the content of the DER INTEGER of a number below `2 ^ 256` is that number in big-endian bytes, on the fewest bytes such that the first has its top bit clear.
`exists_derByteCount` shows that such a byte count, from 1 to 33, exists for every number below `2 ^ 256`.
So a positive number gets a leading zero byte exactly when its first nonzero byte is `0x80` or more, and zero is the single byte `0x00`.
`decodeSignature_eq_ok_iff` proves that the decoder accepts exactly the encodings of r in [1, N) and s in [1, N/2], where N is the order of the secp256k1 group, and returns r and s.
So each accepted pair r, s has exactly one byte encoding.
No theorem relates the encoder to an independent model of X.690.
`verify_sign` (`Networking/Proofs/Libp2p/PeerId.lean`) proves that a signature that a secret makes verifies under the key protobuf of that secret, since signing returns a low s that the strict decoder accepts.

The bindings take explicit keys and state tuples.
Callers must use fresh ephemeral keys and use the returned state after each successful cipher call.
They must discard handshake state after an error.

### Engine API authentication

`Jwt.check_build_of_size` (`Engine/Proofs/Jwt.lean`) proves that a token built with a 32-byte secret passes with that secret at clocks within 60 seconds of its issued-at time.
`Jwt.within_eq_true_iff_of_nonneg` and `Jwt.within_eq_true_iff_of_neg` give the clock comparison of the issued-at time in full, one for each sign of the exponent of the date.
For a negative exponent the statement scales the bounds instead of dividing the date, so it is the exact comparison.
They prove correct the two shortcuts that avoid expanding a huge exponent, where a test can run the shortcut but cannot compute the value it replaces.
The builder validates the JSON it generates, and `Jwt.build_eq_ok` proves that this validation never fails.
`Jwt.authenticate_eq_error_of_tag_ne` proves that a token whose tag differs from the HS256 tag of its parts is refused before any JSON is read.
`Jwt.compact_signature_of_check` proves that an accepted token is the compact form of its parts with their HS256 tag under the secret.
So the clock check accepts no other tag part for those parts.
Keeping a party without the secret away from the reader also assumes HMAC unforgeability, and a captured token can be replayed within its 60 seconds.
`Jwt.check_eq_false_of_algorithm_ne` proves rejection when the decoded algorithm differs from HS256.
The Unicode escape of [RFC 8259 §7](https://www.rfc-editor.org/rfc/rfc8259#section-7) has its own theorems (`Engine/Proofs/Jwt/Json.lean`).
`Jwt.Json.hex4_cons_eq_some_iff` proves that four hex digits, in either letter case, name the number they write in base 16.
`Jwt.Json.hex4_eq_none_of_length_lt` proves that fewer than four characters are no escape.
`hexValue?_hexDigitChar` and `hexValue?_toUpper_hexDigitChar` prove that those hex digits are read in lowercase and in uppercase.
`Jwt.Json.unicodeEscape_eq_none_of_hex4` proves that an escape without four hex digits is refused.
`Jwt.Json.unicodeEscape_eq_of_not_surrogate` proves that a value outside the surrogate range is returned as the code point it names.
`Jwt.Json.unicodeEscape_eq_of_pair` proves that a high surrogate followed by an escaped low surrogate is returned as the code point of the pair.
`Jwt.Json.unicodeEscape_eq_none_of_surrogate` proves that every other surrogate is refused: the grammar admits a lone surrogate ([§8.2](https://www.rfc-editor.org/rfc/rfc8259#section-8.2)), but this reader refuses one.
`Jwt.Json.string_eq_none_of_control` proves that a character below `0x20` is refused when it comes next in a string unescaped.
The total JSON reader has no theorem of full agreement with RFC 8259.
These theorems do not establish HMAC unforgeability or constant-time execution.

### ERC-2335 keystores

The keystore proofs show that a short intermediate key, a mismatched checksum, or a key derivation beyond the caller's limits prevents decryption (`Proofs/Keystore.lean`).
They do not prove Unicode normalization correct for every input, or prove the cryptographic security of the keystore.
The Python suite compares NFKD with Unicode 16.0.0's normalization tests and checks the two ERC-2335 vectors.
JSON text parsing stays in the export boundary; the specification consumes a `Lean.Json` value.
Before parsing, the export refuses deep nesting, long digit runs and large positive exponents, which could exhaust the parser's stack, time or memory.
Decryption takes the caller's limits on memory and work, and refuses a key derivation whose modeled memory or work exceeds them.
The model counts bytes of buffers and calls of 64-byte block functions; no theorem shows that it bounds the code.
The Python binding sets default limits.

### scrypt

The scrypt proofs state the length each step returns, the inputs each step accepts, and the table of ROMix and the integer that picks its index (`Proofs/Hash/Scrypt.lean`).
`validCost_iff` states the cost test as the bound of RFC 7914 §2: a power of two above 1 and below `2^(16 r)`.
`salsa208_ok_iff`, `blockMix_ok_iff`, `romix_ok_iff` and `scrypt_ok_iff` state which inputs each step accepts.
`scrypt_ok_iff` also carries the bounds that PBKDF2 needs on the password and the salt.
`salsa208_size`, `blockMix_size`, `romix_size` and `scrypt_size` state the length each step returns.
`integerify_eq` states Integerify of RFC 7914 §5, whose remainder mod `N` is the index, as the last 64 bytes of the value read little-endian through `Base.bytesToUint`.
`romixFill_replicate_fst_get` states that entry `j` of the table that ROMix fills is BlockMix applied `j` times to the input.
It holds for every `j` below `N`, and `romixFill_fst_get` holds for a fill that starts from any index.
`romixFill_fst_get_lt` states that the fill leaves the entries below its starting index unchanged.
`romixFill_snd` states that the value the fill returns is BlockMix applied `count` times to its start value, so `N` times in ROMix.
ROMix reads its table at indices that depend on its input, so a test vector checks only the entries that it reaches.
`mixBlocks_append` states that mixing a block appends to the output it is given.
`mixBlocks_eq_append` states that when mixing from an empty output succeeds, mixing from any output puts that output before the same blocks.
No theorem states the read loop of RFC 7914 §5, step 3, or that block `k` of the mixed output is ROMix of block `k` of the input.
No theorem relates Salsa20/8, BlockMix or the derivation to an independent model of RFC 7914.
The Python tests (`bindings/python/tests/hmac_kdf/test_password_kdf.py`) check the Salsa20/8, BlockMix, ROMix, PBKDF2-HMAC-SHA256 and scrypt vectors of RFC 7914 §§8 to 12.

### RIPEMD-160

`compress_toBitVec` (`Proofs/Hash/Ripemd160.lean`) proves that the compression of one block, read as 32-bit vectors, is the compression of a model of the authors' pseudo-code.
The statement holds for every chaining variable and every 64-byte block.
The model runs both lines in one loop, rotates 32-bit vectors, and reads each word least significant byte first.
It shares the constants, the word orders and the rotation amounts with the code.
`K_from_square_roots` and `K'_from_cube_roots` derive the constants from square and cube roots.
`r_groups_permute` and `r'_groups_permute` check only that each group of a word order reads every word once.
`hash_eq_spec` proves that the hash of every message is the hash of the model, with no bound on the length.
The model pads the message as MD4 does (RFC 1320 §3.1 and §3.2), with the low 64 bits of the bit length.
It runs the blocks from its own initial value, and its digest puts the least significant byte of each word first.
`pad_eq_spec` proves that the padding of the code is the padding of the model.
The Python tests (`bindings/python/tests/precompile/test_ripemd160.py`) check the hash against the test vectors on Bosselaers' RIPEMD-160 page.

### KZG

No text is agreed yet as the normative KZG specification.
The specifications in consensus-specs point to this repository through a redirect that names no commit.
The Final EIPs pin an older consensus-specs text.
The [KZG README](EthLib/Cryptography/Kzg/README.md#the-normative-text) gives the three readings, and no one has settled on one.
The theorems below are about the definitions of EthLib.
Which source text EthLib's definitions match depends on the reading.

The KZG and PeerDAS proofs use `Bls.pairingLaws`, which proves the pairing law of the check.
Their theorems take no pairing-law hypothesis.

Blobs, cells, commitments, proofs and field elements are byte vectors with their length in the type.
`Proofs/Kzg/Core.lean` proves that parsing rejects bytes of any other length.
It and `Proofs/Kzg/Cells.lean` prove that the operations reject other malformed inputs.
An example is two lists of different lengths.

Each operation takes the trusted setup as an argument and returns `Except KzgError`, so the kernel can unfold it.
`computeCellsAndKzgProofs_blob_spec` and `recoverCellsAndKzgProofs_spec` (`Proofs/Kzg/Fk20Proofs.lean`) state the cells and proofs that two operations return.
They take two hypotheses on the setup.

- `setup.Valid`: every point of the setup is on its curve.
  For the embedded setup, `TrustedSetup.ofHex_valid` proves it if the setup decodes.
- `hsetup_tor`: the first 4032 monomial points of `G1` have an order that divides `r`.
  For the embedded setup, `TrustedSetup.ofHex_torsion` (`Proofs/Kzg/SetupTorsion/Embedded.lean`) proves it for all 4096 monomial points of `G1`, if the setup decodes.
  The kernel checks each point from its `x` coordinate.
  This is a recorded exception to the rule of a few seconds for concrete facts in [CONTRIBUTING.md](CONTRIBUTING.md#known-answers).
  It costs about 8 CPU-minutes per build and about as much per replay, in 16 modules.
  Each module takes 20 to 50 seconds and 1.9 GB to elaborate, and 2.4 GB to replay.
  No theorem proves that the embedded setup decodes, so that stays an assumption.
  The Python suite gives two checks of it, both on compiled code.
  Each KZG vector runs an operation that first decodes the embedded setup.
  `bindings/python/tests/kzg/test_trusted_setup.py` decodes each point of the setup, in `G1` and `G2`, and checks that it is in the subgroup.

`TrustedSetup.WellFormed.valid` and `TrustedSetup.WellFormed.torsion` derive both from a well-formed setup.
`computeCellsAndKzgProofs_blob_spec_ofHex` and `recoverCellsAndKzgProofs_spec_ofHex` state the two theorems for the embedded setup, with neither hypothesis.
Of the setup, they assume only that it decodes.

`uncompress_KZG_SETUP_G2_MONOMIAL_1` (`Execution/Proofs/Evm/Precompiles/PointEvaluation.lean`) states that the point evaluation precompile uses `G2` point 1 of the embedded setup as `[tau]_2`.
It also assumes only that the setup decodes.

For a well-formed setup, `blobToKzgCommitment_represents` (`Proofs/Kzg/Commitment.lean`) proves that a blob's commitment holds its polynomial at the secret.
On a well-formed setup (assumption D3), `blobToKzgCommitment_binding` in the same file proves that two blobs whose decoded values differ share a commitment only when the secret is a root of `p - p'`.
Here `p` and `p'` are the interpolants: the polynomials of degree below 4096 that take each blob's decoded values on the domain.
The theorem also proves that `p - p'` is nonzero and has degree below 4096.
That proof needs no pairing law.
It is not computational binding: no theorem bounds the cost of finding two such blobs without the secret.
For a well-formed setup, honest KZG proofs and blob proofs verify (`verifyKzgProof_computeKzgProof`, `verifyBlobKzgProof_computeBlobKzgProof`, `Proofs/Kzg/Verify.lean`).
`verifyKzgProofImpl_iff` states when the check accepts: `c - y = w (τ - z)`, for decoded points representing `c` and `w`.
On a well-formed setup (assumption D3), `verifyBlobKzgProof_binding` (`Proofs/Kzg/BlobBinding.lean`) splits an accepted blob opening into three cases.
Let the commitment and the proof convert with `bytesToKzgCommitment` and `bytesToKzgProof`, as in EIP-4844.
Let their decoded points represent `f(τ)` and `g(τ)` for polynomials `f` and `g` of degree below 4096.
Let `p` be the interpolant of the blob's decoded values, and let `z` be the evaluation challenge.
Then `f = p`; or `f ≠ p`, `f - p` has degree below 4096, and `z` is a root of `f - p`.
Or `h = f - p(z) - g (X - z)` is nonzero of degree at most 4096, and the secret `τ` is a root of `h`.
The cases can overlap.
They carry meaning only when an algebraic adversary outputs `f` and `g` over the setup's points, without `τ`.
This reading is the algebraic group model, an assumption.
For other choices, such as the constants that the points represent, the third case only restates the check.
For this single check, no theorem bounds the probability of the second or the third case.
It is not computational binding: no theorem bounds the cost of finding such polynomials without the secret.

`blobBindingAdvantage_le` (`Proofs/Kzg/BlobBindingAdvantage.lean`) bounds an accepted blob batch that contains a commitment different from its blob's computed commitment.
The game samples the setup secret uniformly in `Fr` and gives the algebraic adversary only the public setup powers.
The adversary supplies polynomial representations for the group encodings in its queries and output.
The theorem assumes that each representation of a valid encoding evaluates to its point at the secret, on every run.
This hypothesis stands for the algebraic group model, an assumption; nothing restricts how the adversary computes its representations.
The game rejects final batches above `n` blobs.
With at most `qBlob` individual challenge queries and `qBatch` batch challenge queries by the adversary, the bound is `(qBlob + n) 4095 / r + (qBatch + 1) (n - 1) / r` plus the success probability of `setupSecretReduction`.
Here `r` is the order of `Fr`.
The reduction runs the same experiment once and recovers `τ` from roots of representation differences or the final batch error.
The secret-recovery term is defined on the full setup powers.
Root search is noncomputable in the model; no theorem proves the reduction's running time.
`length_setupSecretCandidates_le_points` (`Proofs/Kzg/BlobBindingReduction.lean`) bounds the roots that the search tests by 4096 for each annotated point, plus 4096 for the final batch error.
No theorem relates the secret-recovery term to the discrete logarithm or the strong Diffie–Hellman problem.
`verifyBlobKzgProofBatch_ok_iff_symbolic` (`Proofs/Kzg/BlobBindingVerifier.lean`) connects the game's scalar acceptance equation to the concrete verifier at its concrete challenges.
`verifyBlobKzgProofBatch_ok_iff_game` specializes it to openings that match the submission, as every successful challenge loop gives: when each blob challenge is the concrete hash of its blob and commitment, those openings are the concrete batch.

`verifyKzgProofBatch_ok_iff_root` (`Proofs/Kzg/BatchBinding.lean`) states when the batch check of openings accepts, as an equivalence.
Let opening `i` have commitment `c_i`, value `y_i`, point `z_i` and proof `w_i`.
For a well-formed setup, its verdict is true exactly when its challenge `r` is a root of `P(X) = sum_i X^i (c_i - y_i - w_i (τ - z_i))`.
`P` is zero exactly when every opening satisfies the identity of the single check.
`verifyKzgProofBatch_exists_ok` shows that the batch check returns a verdict, with no error, when its six arrays have one size.
`verifyCellKzgProofBatchImpl_ok_iff_root` (`Proofs/Kzg/CellBatchBinding.lean`) states the same for the batch check of cells, as an equivalence.
For a well-formed setup and decoded points that represent `c` and `w`, its verdict is true exactly when the challenge is a root.
Let cell `k` have commitment `c_{i_k}` at commitment index `i_k`, proof `w_k`, coset shift `h_k`, and values that interpolate to `I_k` of degree below 64.
Then the challenge is a root of `sum_k X^k (c_{i_k} - I_k(τ) - w_k (τ^64 - h_k^64))`.
That polynomial is zero exactly when every cell is valid.
`prEvent_cellErrorPoly_root_le` bounds the root case by `(q + 1) (n - 1) / r`, for at most `n` cells.
Its game is the one of the openings below.
`verifyCellKzgProofBatchImpl_binding` (`Proofs/Kzg/CellBinding.lean`) is the binding of the batch check of cells.
Let an accepted batch hold two cells of 64 values at one cell index below 128, for commitments that represent one scalar.
Then the values agree, or the challenge is a root of a nonzero error polynomial.
Otherwise a search on the two cells returns a solution of the bilinear strong Diffie–Hellman problem.
The problem is Definition 2.4 of the extended KZG paper.
The solution is `(c, x)` with `x` the element `e(g_1, g_2)^(1 / (τ + c))` of the target group.
The theorem holds in any model of that group, `TargetGroup`.
`TargetGroup.ofPairingLaws` gives the model of the pairing itself.
`Proofs/Kzg/CellVerifier.lean` lifts these three results to the outer check, `verifyCellKzgProofBatch`, which the bindings call.
That check takes one commitment per cell, keeps the first copy of each, and runs the core check.
`verifyCellKzgProofBatch_valid_or_root` checks each cell against its own commitment.
`verifyCellKzgProofBatch_exists_ok` shows that the outer check returns a verdict, with no error, on well-formed input.
The input is well formed when the sizes agree, each cell index is below 128, each cell decodes, and each commitment and proof passes KZG validation.
`verifyCellKzgProofBatch_ok_iff_root` states that this verdict is true exactly when the challenge is a root.
`verifyCellKzgProofBatch_binding` concludes that the two cells are equal as bytes, or one of the two other cases holds.
`prEvent_cellInput_root_le` keeps the bound `(q + 1) (n - 1) / r`, where the adversary outputs the inputs of the outer check.
In `verifyCellKzgProofBatch_valid_or_root`, `verifyCellKzgProofBatch_ok_iff_root`, `verifyCellKzgProofBatch_binding` and `prEvent_cellInput_root_le`, the scalar of a commitment or a proof is a function of its bytes.
Wagner and Zapico, ePrint 2025/1683, Definition 1, write the bilinear strong Diffie–Hellman problem with `1 / (τ - c)`.
`isBsdhSolution_iff_sub` (`Proofs/Kzg/Arsdh.lean`) proves that this form and the one of the extended KZG paper differ only by the sign of `c`.
`IsArsdhSolution` in the same file is the winning condition of adaptive rational strong Diffie–Hellman, Definition 2 there.
These are winning conditions for a fixed secret.
The games below give the advantages.
`multiproof_batching` (`Proofs/Kzg/MultiproofBatching.lean`) proves Lemma 2 of 2025/1683, the multiproof batching lemma, over any field.
In place of the paper's cosets, it assumes that the vanishing polynomial of `S - S_j` is constant on each part `S_j`, and that the parts are nonempty.
`eval_nodal_cellNodes` (`Proofs/Kzg/CellBatching.lean`) is Lemma 1: on cell `i`, the vanishing polynomial of cell `j` takes the value `h_i^64 - h_j^64`.
`cell_multiproof_batching` in the same file applies Lemma 2 to a set of cells.
`code_binding` (`Proofs/Kzg/CodeBinding.lean`) is the deterministic core of Lemma 4, code-binding.
Let exactly 64 cells and one more cell satisfy the scalar equation of a valid cell for one commitment.
Then all 65 cells take the values of one polynomial of degree below 4096.
Otherwise a search returns a bilinear strong Diffie–Hellman solution, or a second search returns a `(4095, 64)`-ARSDH winning solution.
Both searches read only the setup, the commitment, the cells and the proofs.
`Proofs/Kzg/BlobVerifier.lean` lifts the batch check of openings to `verifyBlobKzgProofBatch`, which checks the blobs of a block and of a blob transaction before Fusaka.
`verifyBlobKzgProofBatch_exists_ok` shows that it returns a verdict, with no error, when the sizes match, each blob decodes, and each commitment and proof passes KZG validation.
Assume a well-formed setup and decoded points that represent the scalars `c` and `w` of their bytes.
Then `verifyBlobKzgProofBatch_ok_iff_root` states that this verdict is true exactly when the batch challenge is a root of the error polynomial of the blob batch.
`verifyBlobKzgProofBatch_valid_or_root` assumes the same and splits an accepted batch into two cases.
Every entry satisfies `c_i - y_i = w_i (τ - z_i)` and passes `verifyBlobKzgProof`, or the batch challenge is a root of a nonzero error polynomial.
`prEvent_blobInput_root_le` bounds the root case by `(q + 1) (n - 1) / r`, where the adversary outputs blobs, commitments and proofs.
Its game takes the hash of the batch challenge as a random oracle on the batch of openings that the check builds.
The adversary makes at most `q` queries, and its batch has at most `n` commitments.
In `verifyBlobKzgProofBatch_ok_iff_root`, `verifyBlobKzgProofBatch_valid_or_root` and `prEvent_blobInput_root_le`, the scalar of a commitment or a proof is a function of its bytes.
With `scalarOf`, the discrete logarithm of a validated point, this holds for every input, so it is no extra assumption.
The bound takes any such functions, fixed before the adversary runs.
The bound is tight at `q = 0` and `n = 2` (`exists_blobInput_adversary_prEvent_root_eq`).
There, an adversary that makes no query outputs two blobs whose error polynomial is `1 + X`, and the event has probability exactly `1 / r`.
`verifyBlobKzgProofBatch_of_blobOpeningValid` proves that the check accepts every batch of valid blob openings.
So it accepts the commitments and proofs that `blobToKzgCommitment` and `computeBlobKzgProof` return (`verifyBlobKzgProofBatch_computeBlobKzgProof`).

`Proofs/Kzg/PeerDasGames.lean` states Lemmas 3 and 4 of 2025/1683 as games, and proves them.
In each game, the secret `τ` is uniform in `Fr`.
Every adversary receives only `[τ^i]_1` for `i ≤ 4095` and `[τ^i]_2` for `i ≤ 64`, the input of Definitions 1 and 2 there.
`bsdhAdvantage` and `arsdhAdvantage` are the advantages of Definitions 1 and 2, with `(d, D) = (4095, 64)`.
The verifier of the games builds the full setup from these points and checks each cell alone with `verifyCellKzgProofBatch`.
The error polynomial of one cell is a constant, so `CellOpening.Verifies.valid` needs no random oracle.
The code is the Reed–Solomon code of §3.1 there: a codeword holds the values of a polynomial of degree below 4096 on the 128 cosets.
Each of its cells is the encoding of 64 values that the verifier decodes.
`computeCells_eq_codewordCell` (`Proofs/Kzg/PeerDasCodeword.lean`) shows that the cells that `computeCells` returns for a blob are this codeword.
The polynomial is that of the blob: it has degree below 4096 and takes the values of the blob on the blob domain (`eval_blobPolynomial`).
So openings of cells that `computeCells` returns for one blob never win code-binding (`not_codeBindingWins_of_computeCells`).
That theorem leaves the commitment and the proofs arbitrary, so it says nothing about whether the openings verify.
`positionBindingAdvantage_le` is Lemma 3, position-binding, Definition 4 there.
The advantage of every adversary is at most the BSDH advantage of one reduction.
2025/1683 cites Lemma 3 from Lemma 2 of §3.1 of Wagner and Zapico, ePrint 2024/1362, where the adversary also receives `[τ^i]_2` for `i ≤ 4095`.
`codeBindingAdvantage_le` is Lemma 4, code-binding, Definition 5 there.
The advantage of every adversary is at most the BSDH advantage of one reduction plus the ARSDH advantage of a second.
Each reduction runs the adversary once, then a deterministic search; their running times are not formalized.
The BSDH reductions work in any model of the target group, `TargetGroup`.
That BSDH and ARSDH are hard stays an informal hypothesis: no theorem assumes it, and the bounds hold for every adversary.
An adversary is any Lean function, so without a model of cost, hardness cannot be stated as a Lean hypothesis.
The BSDH advantage is relative to a model of the target group; `TargetGroup.ofPairingLaws` is the model of the real pairing.
These games check one cell per call.
`batchCodeBindingAdvantage_le` (`Proofs/Kzg/PeerDasBatchGames.lean`) states code-binding with one batch check of all opened cells of the commitment.
The hash of the challenge is a random oracle into `Fr` on the inputs of the core check, and the adversary makes at most `q` queries.
That idealises SHA-256 reduced modulo `r`, whose values are not exactly uniform.
The verifier accepts when the batch check returns a verdict and its challenge is a root of the error polynomial of the batch.
At the challenge of the hash, this is the batch check of cells (`CellBatchInput.acceptsAt_challenge_iff`); no theorem relates the two at another challenge.
The bound is the bound of Lemma 4 plus `(q + 1) 127 / r`, the root term of the random-oracle game, for at most 128 distinct cells.
The verifier accepts valid openings with every challenge (`CellBatchInput.acceptsAt_of_cellOpeningValid`).
A client that samples a column checks it in its own batch, with many commitments at one cell index.
That game does not model several such batches, each with its own challenge.
`Proofs/Kzg/PeerDasColumnGames.lean` models them.
There the adversary outputs a commitment, openings and `m` columns, and the verifier makes one oracle query per column.
A column holds an opening when one of its entries has the commitment, the cell and the proof of the opening, at the cell index of the column.
`verifyDataColumnSidecarKzgProofs_eq_verify` (`Consensus/Proofs/DataAvailability/Column.lean`) shows that the client's check of a sidecar is the batch check of such a column.
`verifyDataColumnSidecar_eq_true_iff` (`Consensus/Proofs/Gossip/Sidecar.lean`) states exactly when a sidecar passes its shape check.
A passing sidecar has one cell and one proof for each commitment it answers to, which from Gloas are the commitments given with it (those of the bid, when gossip checks it).
Before Gloas it also answers to no more commitments than the blob limit at the epoch of its header.
Let each column have at most `n` cells, and let the adversary make at most `q` queries.
`columnPositionBindingAdvantage_le` bounds position-binding by the advantage of a BSDH reduction plus `(q + m)(n - 1)/r`.
`columnCodeBindingAdvantage_le` bounds code-binding by the advantages of a BSDH reduction and an ARSDH reduction plus the same term.
Before Gloas, the type of the commitments of a sidecar allows at most `MAX_BLOB_COMMITMENTS_PER_BLOCK` of them.
So `n` equal to that limit covers every sidecar whose column the check accepts.
The term bounds the event that the challenge of some column is a root of a nonzero error polynomial (`prEvent_batchesRomRoot_le`).
Otherwise every opening that a column holds verifies alone, and the games of single cells apply.
The verifier accepts a column of cells and proofs of blobs with every challenge (`ColumnBatch.acceptsAt_computeCellsAndKzgProofs`).
`cellOpeningValid_computeCellsAndKzgProofs` (`Proofs/Kzg/HonestCells.lean`) is about the cells and proofs that the code computes for a blob.
Under every well-formed setup, they are valid openings for the commitment of the blob, so also under the setup that the games build.
A valid opening satisfies the scalar equation of a valid cell, with points that pass KZG validation.
`verifyCellKzgProofBatch_of_cellOpeningValid` proves that the batch check of cells accepts every batch of valid openings.
It assumes a well-formed setup, and the commitments of the batch may repeat.
So the batch check accepts the cells and proofs of blobs (`verifyCellKzgProofBatch_computeCellsAndKzgProofs`).
For one cell, `CellOpening.verifies_iff` shows that the verifier of the games accepts an opening exactly when it is valid.
`CellOpening.verifies_computeCellsAndKzgProofs` applies this to the setup that the games build: the openings of a blob verify there.
EthLib does not prove Theorem 1 of 2025/1683, that PeerDAS is a secure data-availability sampling scheme, and does not claim it.
That theorem is informal in the paper.
Its §3.2 explains how it follows from the two lemmas.
The steps are §3.2 of ePrint 2024/1362, for many blobs, and the framework of Hall-Andersen, Simkin and Wagner, ePrint 2023/1079.
2025/1683 does not prove these steps again, and EthLib does not formalize them.

`findSdh_valid_bytes` (`Proofs/Kzg/Binding.lean`) is the evaluation binding of single proofs.
Let the check accept one commitment at one point with two different values.
Then a search over the two openings returns a strong Diffie–Hellman solution for the secret.
It needs a well-formed setup and no model of a hash.

`verifyKzgProofBatch_binding` and `verifyKzgProofBatch_binding_single` (`Proofs/Kzg/BatchBinding.lean`) are the binding of the batch check of openings.
Let an accepted batch open one commitment at one point to two values, or let a single check accept a second value.
Then the values agree, or the search on the two openings returns a strong Diffie–Hellman solution, or the challenge is a root of a nonzero `P`.
They need a well-formed setup.
`prEvent_batchErrorPoly_root_le` (`Proofs/Kzg/BatchChallenge.lean`) bounds the last case.
Its game takes the hash of the challenge as a random oracle on the inputs of the batch.
The adversary makes at most `q` queries to that oracle, then outputs a batch of at most `n` openings.
The verifier then hashes that batch to its challenge.
So the adversary may hash many batches and keep one whose challenge is a root of its `P`.
The challenge is a root of a nonzero `P` with probability at most `(q + 1) (n - 1) / r`.
The one extra query is the verifier's.
The scalars `c_i` and `w_i` are functions of the batch, as the discrete logarithms of its points are.

`checksSufficient_of_subgroupChecks` (`Proofs/Kzg/CeremonyChecks.lean`) is about the ceremony that produced the trusted setup.
It proves that the ceremony's pairing checks force each G1 and G2 point of a contribution to represent the expected power of the trapdoor.
A point represents a scalar when its group element is that multiple of the generator, whatever its coordinates.
It holds under these hypotheses besides the checks themselves:

- Every point is valid and passes the subgroup check of its group.
- `previousTauNonzero`: the previous transcript's tau point is not at infinity.
- `pubkeyNonzero`: the contributor's public key is not at infinity.

`checksSufficient` states the same with the exponents of the points given, in `SubgroupExponents`.

### EVM instructions

Each instruction follows execution-specs, which computes with Python integers.
Lean core defines the same operations on `BitVec`, independently of EthLib.
The theorems in `Arithmetic.lean`, `Comparison.lean` and `Bitwise.lean` of `Execution/Proofs/Evm/Instructions/` prove that the two agree, apart from the divisor 0, where the EVM returns 0.
`sdiv_eq` covers the quotient of -2^255 by -1, the one signed quotient that does not fit in a word, and `bitwiseSar_eq` covers every shift up to 2^256 - 1.
The 38 test cases of EIP-145 pin SHL, SHR and SAR.

No theorem relates the definitions to the Yellow Paper.
The stack, the frame with its program counter and gas meter, and memory are modelled.
So are the instructions that read only the stack, memory, call data, code and return data.
They are in `Execution/Evm/Instructions/StackOnly.lean` and `Execution/Evm/Instructions/MemoryData.lean`.

A program logic over bytecode is in `Execution/Proofs/Evm/Logic/`.
Its first relation covers frames that send no message.
`Reaches S` is the chain of steps of a relation `S`.
`Step` is the relation of the steps that `step` gives, other than requests for a message and errors that abort the run.
`runFrame_of_reaches` proves that a frame that reaches a stopped frame runs to it in `runFrame`, for every bound on the gas of messages and every runner of messages.
`Triple S P Q` says that every frame of `P` reaches a frame of `Q` by the steps of `S`, and `Hoare fork` is `Triple` over `Step`.
`Spec fork P Q` is total correctness for such frames: every frame of `P` reaches a stopped frame of `Q`.
A run that ends out of gas ends in an exceptional halt, so a postcondition of a normal halt needs a precondition with enough gas.
`Logic.At` is a running frame of a code that names every field of the frame, its return data included.
`Logic/Rules.lean` gives rules for the opcodes that push bytes of the code, read call data and the caller, compare, jump, hash memory, read and write storage, and return or revert.
`Logic/Stack.lean` gives rules for POP, SWAP1 to SWAP16, EXP and the opcodes of three operands, at every fork with the one-counter meter.
The rules of `Logic/Rules.lean`, `Logic/Stack.lean`, `Logic/Copy.lean` and `Logic/Log.lean` keep the return data that `At` names.
`Logic/Rules.lean` gives the rule for DUP1 to DUP16, and the rule for DUP1 is its case at depth 0.
Every opcode whose instruction takes one, two or three operands runs by the matching rule, with its instruction from the fork.
DUPN, SWAPN and EXCHANGE of Glamsterdam have no rule yet.
`Logic/NatCode.lean` stores a code of `size` bytes as one natural number.
It states the size of the code, its bytes and the data of a PUSH from that number.
`NatCode.valid_of_walk` proves that a JUMPDEST is a valid jump destination when a walk along the opcodes from position 0 reaches it.
`decide +kernel` checks the walk.
`Logic/Steps.lean` defines the tactic `evm_step`, which applies the rule of the opcode at the program counter and proves the facts about the code by evaluation.
The tactic proves nothing on its own: each step it takes applies one of the rules above, and the kernel checks the result.
`Logic/Fault.lean` gives the postcondition `Faulted` of a frame that halts exceptionally: no output, the error, no gas with the one-counter meter, and the state and substate the frame had.
The caller discards that state; no theorem here states it.
`Logic.invalid` is the rule for a byte that is no opcode at the fork, such as `0xfe` at every fork.
`Logic.jump_invalid` and `Logic.jumpi_invalid` are the rules for a jump to a position that is not a valid jump destination.
`Logic.push_of_readFrame` is the rule for an opcode whose instruction pushes a word that the code, the message, the program counter and the memory fix.
`Logic.callvalue`, `Logic.address`, `Logic.origin`, `Logic.caller`, `Logic.calldatasize`, `Logic.codesize`, `Logic.pc_rule` and `Logic.msize` are its cases.
A size is pushed modulo 2^256, as the instruction pushes it.
`Logic.jumpi_of_eq_zero` is the rule for JUMPI on a condition proved equal to 0.
`Logic.Subroutine` is the specification of a block of code that a caller jumps to with a return address under its arguments.
It holds for every return address that is a JUMPDEST of the code, and every stack under it that leaves room for the block.
`Logic.callSubroutine` proves that a push of the address of the block and a JUMP reach the return address with the results.
It needs both addresses to be JUMPDESTs of the code, and room on the stack below 1024 words.
`Logic.KnownSubroutine` is the same specification over frames that know only the size of memory and some facts.
`Logic.callKnownSubroutine` proves its call, with the push and the jump keeping the size and every fact.
`Logic.stop` is the rule for STOP, which stops the frame with no error and an empty output.
`Logic.stop_of_size_le` is the rule for a frame at or past the end of its code, which stops the same way.
`Logic.sstore_of_account` restates the rule for SSTORE when the current account exists.
It gives a state that holds the new word in the slot, and that the frame reaches.
That state keeps every other slot, the original words and the accounts.
`recordStorageRead_recordStorageRead` proves that recording a storage read twice records it once.
`Logic.insert_insert_getD_self` proves that recording the access of a slot twice records it once.
`Logic.mem_insert_getD_self` proves that a slot whose access is recorded is warm.
`Logic.mem_insert_getD_of_ne` proves that the record leaves every other slot as cold or warm as it was.
`Logic.le_sloadCost` proves that from Berlin, SLOAD costs at least 100.
`Logic.gas_rule` is the rule for GAS, which pushes the gas left after its own price of 2.
`Logic.extcodesize` is the rule for EXTCODESIZE from Berlin to before Glamsterdam.
It charges the prices of EIP-2929, and needs the state to hold the code of the account.
`Logic.extcodesize_of_berlin_le` is the rule for EXTCODESIZE from Berlin, Glamsterdam included, at the price of the fork.
`Logic.mstore8` is the rule for MSTORE8, which writes the lowest byte of a word.
`Logic.mcopy` is the rule for MCOPY from Dencun, which grows memory for both ranges before it reads the source.
`Logic.copyWith` is the rule for a copy of a buffer of the frame to memory, with zeros past its end.
`Logic.calldatacopy` is its case for CALLDATACOPY.
`Logic.codecopy` is its case for CODECOPY.
`Logic.returndatacopy` is the rule for RETURNDATACOPY from Byzantium, for a range that ends within the return data.
`Logic.returndatasize` is the rule for RETURNDATASIZE from Byzantium, which pushes the size of the return data and keeps it.
`Logic.extcodecopy` is the rule for EXTCODECOPY from Berlin to before Glamsterdam.
It charges the prices of EIP-2929 and 3 gas a word, and needs the state to hold the code of the account.
`Logic.extcodecopy_of_berlin_le` is the rule for EXTCODECOPY from Berlin, Glamsterdam included, at the price of the fork.
`Logic.Holds` says that memory covers a range and that the range reads as given bytes.
`Logic.holds_memoryWrite` proves that a write within memory holds the written bytes.
`Logic.Holds.memoryWrite_of_disjoint` proves that such a write keeps every range it does not touch.
`Logic.Holds.memoryExtend` proves that growth keeps every range.
`Logic.Holds.append` proves that two adjacent ranges hold their bytes in order.
`Logic.Holds.left` proves that a range that holds two blocks holds the first from its start.
`Logic.Holds.right` proves that it holds the second after the first.
`Logic.Holds.loadWord` proves that a range that holds the bytes of a word reads as that word.
`Logic.extendMemory_of_le` proves that a range within memory grows nothing and costs nothing.
`Logic.extendMemory_of_lt` proves that a range of some bytes past memory grows it to the rounded end of the range.
It needs a size of memory that is a multiple of 32.
That growth costs the price of the new size minus the price of the old size.
`Logic.size_memoryExtend_extendMemory` proves that memory then has the greater of its old size and that rounded end.
`Logic.Known` is a running frame whose memory is named only by its size, a multiple of 32, and by facts that `Holds` states.
`Logic.Known.of_at` proves that a rule that keeps memory, for every memory, keeps the size and every fact.
`Logic.known_of_write` proves that after a write, memory holds the written fact and every fact apart from the write.
`Logic.Known.join` proves that the facts of two adjacent ranges join into one.
`Logic.mstore_known` gives MSTORE this form, with memory grown by the growth for its size.
`Logic.mstore8_known` gives MSTORE8 this form.
`Logic.mcopy_known` gives MCOPY this form, from Dencun, for a source that is the range of a fact.
`Logic.calldatacopy_known` gives CALLDATACOPY this form.
`Logic.codecopy_known` gives CODECOPY this form.
`Logic.returndatacopy_known` gives RETURNDATACOPY this form, from Byzantium, for a range within the return data.
`Logic.extcodecopy_known` gives EXTCODECOPY this form, from Berlin to before Glamsterdam.
These write rules ask for a range of some bytes.
`Logic.mload_known` proves that MLOAD of the range of a fact with a word pushes that word.
`Logic.return_known` proves that RETURN of the range of a fact returns the bytes of the fact.
`Logic.revert_known` proves the same for REVERT from Byzantium.
`memoryReadBytes_memoryWrite_eq_append` proves that a read that ends where a write ends gives the bytes before the write, then the value.
`Logic.staticcallWith` is the rule for STATICCALL from Berlin to before Glamsterdam.
Its message carries no value and is static.
`Logic.staticcall` is its case with empty ranges of input and output.
`Logic.callStep_child` gives the step of a call that sends no value of its own, for each kind of call.
`Logic.callKindWith` is the rule for such a call from Berlin to before Glamsterdam.
After the call, the return data is the output of the frame that ends the message.
`Logic.delegatecallWith` is the rule for DELEGATECALL from Berlin to before Glamsterdam.
Its message runs the code of the address on the current account, with the sender and the value of the current message.
`Logic.callcodeWith` is the rule for CALLCODE with no value from Berlin to before Glamsterdam.
Its message runs the code of the address on the current account, as its sender.
`Logic.createStep_child` gives the step of CREATE or CREATE2 that sends its message, from Berlin to before Glamsterdam.
It needs the new address to hold no code and a nonce of 0, as EIP-684 asks.
`Logic.createKindWith` is the rule for such a creation, under an assumption on the frame that ends it.
`Logic.createWith` is its case for CREATE.
`Logic.create2With` is its case for CREATE2.
`Logic.resumeCreate_eq` proves that the creator pushes the new address, or 0 when the frame that ends the creation has an error.
After a creation with no error the return data is empty, and otherwise it is the output of that frame.
`Logic.createMessageGas_of_tangerineWhistle` proves that from Tangerine Whistle a creation passes on all but one 64th of the gas left.
`Logic.depositCode_of_ok` proves that from Berlin to before Glamsterdam a frame with no error deposits its output as code, at 200 gas a byte.
It needs the output to hold at most 24576 bytes (EIP-170), and from London not to start with `0xEF` (EIP-3541).
`Logic.depositCode_of_prefix` proves that from London an output that starts with `0xEF` fails with all the gas taken, the state put back and no output.
`Logic.depositCode_of_outOfGas` proves that an output too long or too dear fails the same way, out of gas.
`Logic.processCreateMessage_eq_ok` proves that a creation with no value and no precompile ends as its init code ends, then deposits.
`Logic.meets_of_spec_create` proves that the runner of the interpreter meets `CreatesAs` for a specification of the init code.
`Logic.running_eq_false_of_sstore_of_isStatic` proves that in a static frame, a step at SSTORE stops the frame.
`sstoreStep_halts` proves that SSTORE never completes in a static frame, or when the current address has no account.
In that second case the write fails and aborts the run.
`Logic.running_eq_false_of_log_of_isStatic` proves the same for LOG0 to LOG4.
`memoryReadBytes_memoryWrite_of_disjoint` proves that a write within memory leaves a read of a disjoint range unchanged.
`memoryReadBytes_memoryWrite_memoryWrite` proves that a read across two adjacent writes gives both values in order.
`memoryWrite_comm_of_disjoint` proves that two writes within memory to disjoint ranges commute.
`memoryReadBytes_memoryWrite_memoryWrite_rev` proves the same read when the higher write comes first.
From Berlin, the rule for SLOAD takes as a hypothesis whether the slot is cold, and charges 2100 or 100 by EIP-2929.
`Logic.sstore` is the rule for SSTORE from Berlin, with one counter of gas, in a frame that may change the state and holds more than 2300 gas.
It charges `sstoreTotalCost`, the price and the state gas of the write, ignores the refill of state gas, and adds `sstoreRefund` to the refund counter, from the original, current and new words and whether the slot is cold.
It takes the state that the write gives as a hypothesis, since the write needs the account of the current address.
`Logic.log` (`Logic/Log.lean`) is the rule for LOG0 to LOG4, at every fork with the one-counter meter, in a frame that may change the state.
It appends one log of the current address with the topics and the range of memory.
It pays 375, 8 for each byte, 375 for each topic and the growth of memory.
It says nothing of the order of the logs of several frames, or of logs that a revert drops.
`Logic.branchTable` (`Logic/Branch.lean`) is the rule for a table of entries that branches on the top word of the stack.
It holds at every fork with the one-counter meter.
Each entry is DUP1, a push of a key of `n` bytes, EQ, a push of a destination of `m` bytes, and JUMPI.
The run jumps to the destination of the first entry whose key is the word, or goes on past the table.
It pays 22 gas for each entry it tests, and needs each destination to be a valid destination of a jump.
`Triple.loop` (`Logic/Loop.lean`) proves a loop from an invariant for each value of a natural measure.
A run of the loop then ends by the measure, not by the gas.
`Triple.loop_gas` proves a loop whose invariant carries the gas, with a price for each run that may depend on the runs left.
The loop then needs the sum of those prices and the price of its exit.
`Logic.holds_empty` proves that memory holds no bytes from an offset within it.
`Logic.Stored` is a running frame that knows ranges of memory, the facts of some slots, and the refund counter.
A fact of a slot gives its account, its key, its word before the transaction, its word now, and whether it is warm.
`Logic.Agrees` says that a state and its accessed keys agree with a base outside a list of slots and two lists of addresses.
There each word reads as in the base state, and each slot is warm exactly when the base keys hold it.
The words before the transaction and the block are those of the base state.
Outside the addresses of both lists each account is that of the base state.
Outside the second list, of remade addresses, an account exists exactly when it does in the base state.
There it also has the nonce, the code hash and the code of the base state.
A `Stored` frame agrees with its base outside the slots of its facts, and at every address.
`Logic.Agrees.trans` proves that agreement composes, outside both lists of slots and both lists of addresses of each kind.
`Logic.Agrees.getAccount` proves that outside both lists of addresses an account is that of the base state.
`Logic.Stored.of_known` proves that a rule that keeps the state and the substate keeps every fact.
`Logic.Stored.of_at` proves the same for a rule that also keeps memory.
`Logic.sload_stored` proves that from Berlin, SLOAD of the key of a fact of the frame's account pushes its word now.
It makes the slot warm.
`Logic.sstore_stored` proves that from Berlin to before Glamsterdam, SSTORE to the key of such a fact writes it and makes it warm.
It needs a frame that may change the state, more than 2300 gas, and the account of the frame in the base state.
It pays the price of EIP-2200 with the prices of EIP-2929 from the facts of the slot, and adds the refund of the write.
`Logic.StoppedStored.of_known` proves that a rule that halts and keeps the state and the substate keeps every fact.
`Logic.stop_stored` proves that STOP keeps every fact.
`Logic.returndatasize_stored` proves that from Byzantium RETURNDATASIZE pushes the size of the return data and keeps every fact.
`Logic.returndatacopy_stored` proves that from Byzantium RETURNDATACOPY of a range within the return data writes it as a fact of memory.
These frames say nothing of the logs, the accessed addresses and the other fields of the substate.
`Logic.AccountFact` gives the address, the nonce, the balance and the code of an account that exists.
`Logic.Change` names the slots that a message may touch and the addresses whose balances it may move.
It also names the addresses whose accounts it may remake, by a creation or a change of a nonce or a code.
It also names the facts of slots, the balances, the facts of accounts and the refund that the message gives on success.
`Logic.Effect` (`Logic/Effect.lean`) is the effect of a message on storage and accounts, from the frame that sends it.
Outside the slots and the addresses of its change, the state after agrees with the state before.
A failed message touches no slot, moves no balance and remakes no account.
A message that succeeds gives the facts of some slots, some balances and some accounts, and adds a refund.
`Logic.effects_rollbackOnError` proves that a callee whose stopped frame agrees with the state of its caller outside a change has its effect after the rollback.
`Logic.agrees_moveEther` proves that a move of a value that is not 0 between two accounts changes only their balances.
It needs the two accounts to exist and the sender to have a nonce or a code.
`Logic.agrees_modifyState` proves that a change of one account that keeps it alive changes only that account and keeps every code.
`Logic.CallMessage` is the message that a call sends when it sends no value of its own, by the kind of the call.
`Logic.callKind_stored` proves that from Berlin to before Glamsterdam, such a call keeps the facts of a `Stored` frame.
It keeps each fact of a slot that the effect of the callee does not touch.
It needs an input range that a fact of memory holds, an output range within memory, and the gas of a cold call.
It also needs an assumption that gives the effect of each frame that ends the message.
The assumption also gives the output of such a frame when it succeeds.
On success the frame gains the facts and the refund of the effect, and that output as its return data.
It also gains the fact of the start of that output in the output range.
On failure it keeps its facts of slots, and the assumption may rule a failure out.
The assumption may also describe the output of a frame that ends with an error, such as a revert.
On failure the return data of the frame is such an output.
Either way it keeps each fact of memory apart from the output range.
Its new base agrees with the old one outside the touched slots and the slots of the facts.
`Logic.call_stored` proves this for CALL with no value.
`Logic.staticcall_stored` proves this for STATICCALL.
`Logic.delegatecall_stored` proves this for DELEGATECALL.
`Logic.callcode_stored` proves this for CALLCODE with no value.
`Logic.ValueMessage` is the message that CALL sends with a value.
`Logic.callValue_stored` proves that from Berlin to before Glamsterdam, CALL with a value that is not 0 keeps the facts of a `Stored` frame in the same way.
It needs a frame that may change the state, and its account must hold the value in the base state.
It needs the gas of a cold call, 9000 for the value, and 25000 more when the callee is dead in the base state.
On success the new base also holds the balances and the facts of accounts of the effect.
The new base agrees with the old one outside the addresses whose balances the effect moves or whose accounts it remakes, too.
`Logic.CreateMessage` is the message that a creation sends, to run its init code at the new address.
`Logic.AfterCreate` is the frame after a creation from a `Stored` frame.
`Logic.createKind_stored` proves that from Berlin to before Glamsterdam, CREATE or CREATE2 keeps the facts of a `Stored` frame.
It needs init code that a fact of memory holds, and a frame that may change the state.
The creator must hold the value in the base state.
Its nonce in the base state must not be the greatest, and its depth must leave room for one more frame.
From Shanghai the init code must hold at most the greatest size of EIP-3860.
It needs the new address from the base state to hold no code and a nonce of 0, and the price of the creation.
It also needs an assumption that gives the effect of each frame that ends the creation.
On success the frame pushes the new address, gains the facts and the refund of the effect, and its return data is empty.
On success the new base holds the balances and the facts of accounts of the effect.
On failure the frame pushes 0 and keeps its facts of slots, and the assumption may rule a failure out.
Its return data is then an output that the assumption allows for a frame that ends with an error.
The new base gives the creator its grown nonce, unless the effect remakes the creator.
Its new base agrees with the old one outside the touched slots, the moved and remade addresses, and the creator.
`Logic.create_stored` proves this for CREATE.
`Logic.create2_stored` proves this for CREATE2.
`Logic.nonce_of_shape` proves that an account with the nonce and the code hash of an account that exists has its nonce.
`Entered` (`Execution/Proofs/Evm/Call/Run.lean`) gives the state and the substate that the frame of a message starts from, after the move of its value.
`Entered.of_not_transfers` proves that a message that moves no value starts from the start state and the substate of its caller.
`Logic.meets_runsAll` proves that the runner of the interpreter meets the specifications of a family of codes that call each other, at every bound.
Each specification is a triple under the assumption that the whole family runs as specified, so a callee may call its caller back.
Each specification holds from every frame that a message with its code enters, so a message may move a value.
The proof is an induction on the bound on the gas of messages.
`HoareUnder.of_exists` proves a triple from a precondition that gives a witness, with a triple for each witness.
`StepBy` (`Logic/Message.lean`) adds the steps that send a message, which a runner of messages ends with a frame.
`runFrame_eq_of_reaches` proves that `runFrame` runs a frame as it runs each frame that it reaches.
It holds for every relation whose steps `runFrame` runs alike at both ends, as `Step` and `StepBy` do.
A runner can also fail on a message, and then `runFrame` fails with the error of the runner.
`Meets callee runChild` says that each frame that the runner gives meets the assumption `callee`.
It also says that the runner fails only with an error that aborts the run, and asks nothing more of such a message.
`meets_process` proves that the runner of the code of a message meets the assumption that always holds, for every bound.
It rests on `aborts_of_process_eq_error` (`Execution/Proofs/Evm/Call/MessageCall.lean`), which proves that a message and a creation fail only with an error that aborts.
`meets_of_spec` (`Logic/Callee.lean`) proves that this runner meets a stronger assumption, `RunsAs`, for a callee code with a specification.
The specification is one with no message, from the frame that a message with that code starts, so the callee sends no message itself.
The assumption covers a message with that code and a target, with no value and no precompile.
Its frame starts from the state of the caller, with its target touched before Paris, as `processMessage` does.
The frame that ends the message is a stopped frame of the specification, rolled back on a failure.
`meets_of_specUnder` proves the same for a callee that sends messages, from a triple under an assumption `A` on its own messages.
It asks that the runner meet `A` at every bound.
`meets_of_spec` is its case with the assumption that always holds.
`processMessage_map_val` proves that a message that moves no value and has no precompile ends as the run of its code ends, for every lawful meter.
`processMessage_map_val_value` proves the same for a message that moves value, from the state after the transfer.
No theorem yet proves that this runner meets an assumption for a callee that sends value or is a precompile.
No theorem reasons about a callee that calls back into its caller and depends on the state that the caller wrote.
`SpecUnder fork callee P Q` holds under every runner that meets `callee`, and for every bound that holds the gas of the frame.
From every frame of `P`, the steps of `StepBy` reach a stopped frame of `Q`, or a frame whose runner fails on its message.
So `SpecUnder.runFrame` concludes that `runFrame` returns a stopped frame of `Q`, or fails with an error that aborts.
`hoareUnder_iff_triple` states each triple under an assumption as a `Triple` over `StepBy` under each runner that meets it, so the two share their rules.
The code that a message runs is arbitrary and may call the caller again.
So the assumption is all that a triple says about a frame that ends a message, and about the state after it.
`Logic.callWith` (`Logic/Call.lean`) is the rule for CALL with no value, a range of input and a range of output.
It pays the growth of memory for both ranges, and the message carries the bytes of the input range.
The caller writes the start of the output of the callee at the start of the output range, as far as both go.
`Logic.call` is its case with empty ranges.
It holds from Berlin to before Glamsterdam, with the one-counter meter.
It pays 2600 or 100 for the access to the address, by EIP-2929.
It passes on at most all but one 64th of the gas left, by EIP-150.
Its postcondition gives the state and substate that the frame that ends the message gives, and nothing more.
`meets_process_noCode` proves that the runner of the interpreter meets one more assumption.
That assumption says that a message with no code, to an account that is no precompile, ends with no error.
`Logic.callWith` and `Logic.call` also state that the message is static when the frame is.
`Logic.callValue` is the rule for CALL with a value that is not 0, from Berlin to before Glamsterdam.
The frame must be one that may change the state.
It pays the access of EIP-2929, 9000 for the value, 25000 more when the callee is dead by EIP-161, and the growth of memory.
The message gets the gas that EIP-150 allows and the stipend of 2300, and carries the value.
The message is not static.
`Logic.callValueLow` is the rule for such a CALL when the current account holds less than the value.
It sends no message, pushes 0, and gives back the gas it would pass on with the stipend.
Its return data is then empty.
`meets_paidNoCode` (`Logic/Callee.lean`) proves that the runner ends a message with value to no code with no error.
Its frame ends in the state that the move of the value gives.
No rule covers CREATE, DELEGATECALL or STATICCALL.

A triple under an assumption asks the runner to fail only with an error that aborts.
It does not say on which message the runner fails.
`HoareOn fork callee S P Q` (`Logic/FailsOn.lean`) asks nothing of the errors of the runner.
Instead it names the messages on which a run may stop because the runner fails.
`S` is a condition on the frame that the step hands to the runner, after it pays for the message, and on the message.
`MeetsOk callee runChild` says that each frame that the runner gives meets `callee`, and lets the runner fail on every message with an error of any kind.
`HoareOn` holds under every runner that meets `callee` in this sense, and for every bound that holds the gas of the frame.
From every frame of `P`, the steps of `StepBy` reach a frame of `Q`.
Or they reach a frame that sends a message of `S`, and the runner fails on that message.
`SpecOn` is its case whose postcondition is a stopped frame.
`hoareOn_true_iff` proves that `HoareOn` with the set of every message is `HoareUnder`.
`HoareUnder.toOn` replaces each error of a runner with one that aborts, which keeps the steps and the frames on which the runner fails.
With `HoareOn.toUnder` it gives `hoareOn_true_iff`.
So a triple under an assumption is the case of the full set, and a smaller set gives a stronger triple.
`HoareOn.toUnder` and `SpecOn.toUnder` prove that each such triple is a triple under the same assumption, for every set.
`hoareOn_iff_triple` proves that `HoareOn` is a `Triple` over the steps under each runner, as `hoareUnder_iff_triple` does with no set.
The rules of `HoareUnder` hold for `HoareOn` with the same set: `of_hoare`, `of_child`, `assumption`, `of_exists`, `seq`, `consequence`, `cases`, `loop_lt` and `loop`.
`HoareOn.of_child` asks that the message be in `S`.
`HoareOn.mono` and `SpecOn.mono` prove that a larger set of messages keeps a triple.
`SpecOn.seq`, `SpecOn.consequence` and `SpecOn.of_spec` prove the rules of sequence, consequence and no message for a triple to a stopped frame.
`SpecOn.runFrame` proves that `runFrame` returns a stopped frame of `Q`, or fails.
When it fails, a frame that the steps reach sends a message of `S`, and the runner fails on it.
Then `runFrame` fails with the same error.
`HoareOn.runFrame_of_ok` proves that a run that succeeds through such a triple goes on from a frame of `Q`, for a runner that meets the assumption.
That run ends where the run from that frame ends.
`Hoare.runFrame_of_ok` proves the same for a triple over the steps, under every runner.

From Pectra, a call to an account whose code is an EIP-7702 delegation indicator runs the code of the delegate.
`Logic.Routes fork state c route` (`Logic/Route.lean`) says which code a call to an account with the code `c` runs.
The route is the code of the address itself, or a delegate with the code that the state holds for it.
`Logic.Routes.congr` proves that the route depends on the state only through the code at each address.
`Logic.Routes.recordAccountRead` proves that a recorded read leaves the route unchanged.
`Logic.CallSends` gives the frame and the message of a call that sends no value of its own, along a route.
The message runs the code of the route; when delegated, its code address is the delegate and it runs no precompile.
`Logic.callStep_child_of_routes` proves that the step of such a call sends that message, for each kind of call.
It holds at every fork from Berlin, with the one-counter meter.
The call pays the access to the address, the access to the delegate, the growth of memory, and the gas it passes on.
`Logic.callKindRoute` proves the rule for such a call as a `HoareOn` triple.
Its set holds only the message of the call, so a run may stop because the runner fails only on that message.
`Logic.callRoute` proves its case for CALL.
Unlike `Logic.callWith`, neither rule asks that the code be no delegation, or that the fork come before Glamsterdam.
`Logic.callStep_child` and `Logic.callKindWith` are their cases with no delegation, so the step has one proof.
`Logic.callStep_fails_of_routes` (`Logic/CallSteps.lean`) proves that such a call fails, or halts the frame with an error, when its gas is below its price before the gas it passes on.
That price is the access to the address, the access to the delegate if any, and the growth of memory.
`Logic.callStep_deep_of_routes` proves that such a call at the greatest depth, with at least that price in gas, sends no message, pays only that price and pushes 0.
`Logic.callStep_fails_of_missing` proves that from Pectra such a call fails when the lookup of the code of the delegate fails.
Instead of failing, the step may halt the frame with an error.
Each holds for every kind of call with the one-counter meter: the first two from Berlin, the third from Pectra.

A triple says about the state after a message only what its assumption says, so a proof needs an assumption on what the callee does.
`Logic.KeepsOn runChild S R` (`Logic/Keeps.lean`) says that each message of `S` that the runner ends with no error keeps the relation `R`.
It is the assumption `Logic.MeetsOk` of a triple, for that condition on the frame that ends the message.
`R` holds from the state of the frame that sends the message to the state of the frame that ends it.
`Logic.KeepsOn.mono` proves that a smaller set of messages and a weaker relation keep the assumption.
`Logic.ReadsAs tx S` says that `tx` has the account, the storage and the transient storage of `S` at every address, and its code at every hash.
It leaves free the block before the transaction, the created accounts, the wiped storage and the read records.
`Logic.ReadsAs.recordAccountRead` proves that a record of an account read keeps this relation.
`Logic.ReadsAs.recordStorageRead` proves the same for a record of a storage read.
`Logic.ReadsAs.routeState` proves the same for the state once a call follows a route.
`Logic.Routes.of_readsAs` proves that a state that reads as `S` gives each code the route that `S` gives it.
`Logic.SentVia message S to` names the CALLs with no value from the current account of `message` to `to`, from a frame that reads as `S`.
Each such call runs the code that `to` holds in `S`, along its route, with any data, any gas and any reservoir.
`Logic.CallSends.sentVia` proves that the message of a CALL with no value along a route is such a call, via the state before the call.

`StepRules fork R` (`Execution/Proofs/Evm/Call/StepRules.lean`) lists the rules for a transitive relation `R` of two frames.
`R` must hold of each step that keeps the state up to the records of reads.
It must also hold of each write of storage, transient storage, a log or SELFDESTRUCT.
It must hold of the rise of a nonce below `2^64 - 1`, and of a child taken in by its caller.
`StepRules.step` proves that such a relation holds of every successful step, given it for the frame that ends each message sent.
`StepRules.runFrame` proves the relation for a successful run of a frame.
`StepRules.processMessage` turns it into a fact of every call and creation, by induction on the gas of the message.

The block of a transaction state is the state before the block, with the writes of the block so far.
A rollback restores the storage of a snapshot only when both states have the same block.
`parentResult_step` (`Execution/Proofs/Evm/Call/Parent.lean`) proves that every successful step keeps the block of the state, at every fork.
A step that sends a message keeps it once the frame that ends the message has the block of its caller.
`KeepsParent runChild` says that the runner ends each message that succeeds with the block of the frame that sends it.
`parent_runFrame` proves that a successful run of a frame keeps the block, under a runner that meets `KeepsParent`.
`parent_processMessage` proves that a successful call keeps the block of the state it is sent from, at every fork.
`parent_processCreateMessage` proves the same for a successful creation.
`keepsParent_processRunner` (`Logic/Message.lean`) proves that the runner of the code of a message meets `KeepsParent`, for every bound.
`KeepsParent.keepsOn` (`Logic/Keeps.lean`) proves that such a runner keeps the block on every set of messages of `Logic.KeepsOn`.
`processMessage_sameOutside_of_error` proves that a call that ends with an error reads as the state it is sent from at every address, at every fork.
That covers the account, the storage and the transient storage, and `getStorage_processMessage_of_error` states it for one storage word.

From Cancun, `deletesCreated_processMessage` (`Execution/Proofs/Evm/Call/ToDelete.lean`) proves that a call marks for deletion only accounts already marked or created in the transaction.
From Paris, `touchedAccounts_processMessage` (`Execution/Proofs/Evm/Call/Touched.lean`) proves that a call touches no account beyond those of its substate.
`sameOutside_deleteAccounts` (`Execution/Proofs/Transactions/Deletion.lean`) proves that the deletions at the end of a transaction change only its accounts to delete and its touched accounts.
`sameOutside_deleteAccounts_of_dencun` proves that, from Cancun, the deletions after the settlement of gas change only the created accounts of the settled state, when its message starts from the substate of a transaction.
`runTransaction_deletes_created` states this for the run of a transaction, with each of its steps named; there the created accounts are those the transaction created.
Before Glamsterdam, `runTransaction_removes_marked` (`Execution/Proofs/Transactions/Deletion.lean`) proves that each account marked for deletion by a frame that no revert undoes is absent after the transaction, when its message ends without an error.
Before Cancun, `runTransaction_removes_selfdestructed` states it for the account that runs SELFDESTRUCT in such a frame.
`Visits` (`Execution/Proofs/Evm/Logic/Marks.lean`) names those frames: the frames that a run reaches, and those of the code of each message on the way that ends without an error.
`toDeleteLe_of_visits` proves that the frame that ends such a run, without an error, marks every account that a visited frame marks.

The facts of `Logic/GasMono.lean` and `Logic/LessGas.lean` are for the one-counter meter, the meter of every fork before Glamsterdam.
`Logic.addGas k` adds `k` to the gas of a frame.
`Logic.RunMono` says that an instruction, on each frame, fails or gives a frame `b`.
On that frame with `k` more gas, it then gives `b` with `k` more gas.
A frame that reverts counts as failed, so these facts say nothing of the gas of a run that reverts.
`Logic.GasMono` says the same of the step from every frame with less gas than a frame.
`Logic.HoareG` and `Logic.SpecG` are triples over the steps of `Step` from frames that are `GasMono`.
`Logic.HoareG.toHoare` proves that such a triple is a triple over `Step`.
`Logic.At.ruleG` is the rule of an opcode whose instruction is `RunMono`.
`Logic.invalidG` (`Logic/Fault.lean`) is the rule for a byte that is no opcode at the fork, and `Logic.invalid` follows from it.
`Logic.reaches_low` proves that these steps from a frame `l` with `k` more gas follow the run of `l`, when that run ends with no error.
`Logic.low_of_reaches` proves that a stopped frame these steps reach is then the end of the run of `l`, with `k` more gas.
Both hold for every bound on the gas of messages and every runner of messages.
`Logic.SpecG.low` proves that a specification from a frame with `k` more gas then holds of the end of the run with `k` more gas.
`Logic.SpecG.halted` proves that the run then ends in the normal halt of a specification from a frame of `At`, with `k` less gas.
`Logic.SpecG.not_ok` proves that the run does not end with no error when every frame of the postcondition has an error.
`Logic.halted_of_specG` takes a specification over `Logic.StepG` to a normal halt that pays `cost`, from a frame of `At` with every gas from some bound on.
The specification needs to hold only with at least `cost` gas.
It proves that every run of that frame that succeeds, with any gas, had at least `cost` gas.
That run ends in that halt with exactly `cost` less gas.
`Logic.no_ok_of_specG` proves that every frame that the loop runs a frame of `At` to, with any gas, has an error.
It assumes a specification over `Logic.StepG` to frames with an error, with every gas from some bound on.
`Logic.Stuck` is a running frame from which the step fails, and from it with any less gas.
`Logic.not_ok_of_reaches` proves that a run does not end with no error when these steps from the frame with `k` more gas reach a stuck frame.
`Logic.no_ok_stuck` proves the same for a frame of `At` that reaches a stuck frame with every gas from some bound on.
`Logic.no_ok_stuck_at` proves the same for a frame of `At` that reaches a stuck frame with its own gas.
GAS has no rule of this kind, since it pushes the gas left, and no theorem here covers a step that sends a message.
`Logic.At.ruleG_of_follows` is the rule of an opcode whose instruction, run on each frame of the rule with less gas, fails or gives its frame with less gas.
Each instruction that `Logic/RunMono.lean` covers is `RunMono`, such as `Logic.runMono_sstore` for SSTORE.
`Logic.follows_readFrame` proves that an instruction that pushes a word of the frame, run with less gas, fails or gives its frame with less gas.
It needs the word not to depend on the gas.
The opcode rules of `Logic/Rules.lean`, `Logic/Stack.lean` and `Logic/Log.lean` are proved over the steps from frames that are `GasMono`, such as `Logic.calldataloadG`.
Each such rule has the hypotheses and the conclusion of the rule over `Step` of the same opcode, which follows from it by `Logic.HoareG.toHoare` or `Logic.SpecG.toSpec`.
Of the opcode rules there, the one for GAS has no such form, since it pushes the gas left.
Those for EXTCODESIZE, a frame past the end of its code and `Logic.sstore_of_account` have none yet.
`Logic.branchTable` has no such form yet.
`Logic.At.stuck` proves that a frame is stuck at an opcode whose instruction fails on every frame with the same message, stack and state, and at most the same gas.
`Logic.sstore_stuck` proves that SSTORE is stuck in a static frame, or when the current address has no account.
`Logic.sstore_low_stuck` proves that from Istanbul SSTORE is stuck with 2300 gas or less, by EIP-2200.

The facts of `Logic/NoAbort.lean` are for the one-counter meter too.
`Logic.NoAbort` says that a result is no error that aborts the run.
An error of the state aborts, and so do an opcode with no instruction, an encoding error and a fork with no specification.
Each instruction of `Logic/RunMono.lean` except SSTORE never aborts, such as `Logic.noAbort_log` for LOG0 to LOG4.
`Logic.NoAbortLow` says that the step from every frame with less gas than a frame does not abort.
`Logic.HoareGA` and `Logic.SpecGA` are triples over the steps of `Logic.StepG` from frames that are `Logic.NoAbortLow`.
`Logic.HoareGA.toG` proves that such a triple is a triple over `Logic.StepG`.
`Logic.At.ruleGA_of_follows` is the rule of an opcode whose instruction never aborts.
Run with less gas on each frame of the rule, the instruction must fail or give its frame with less gas.
`Logic.At.ruleGA` is the same rule for an instruction that is `RunMono`.
Each opcode rule over `Logic.StepG` whose instruction never aborts is proved over `Logic.StepGA` first, such as `Logic.calldataloadGA`.
The rule over `Logic.StepG` of the same opcode follows from it by `Logic.HoareGA.toG` or `Logic.SpecGA.toG`.
`Logic.no_error_of_reaches` proves that the loop runs a frame `l` to a frame, never to an error.
It assumes that these steps reach a stopped frame from `l` with `k` more gas.
`Logic.no_error` proves that the loop runs a frame of `At` to a frame, with any gas.
It assumes a specification over these steps from that frame with every gas from some bound on.
Both hold for every bound on the gas of messages and every runner of messages.

`Logic/RunsOk.lean` says when a run succeeds, that is when the loop ends its frame in a frame with no error.
`Logic.RunsOk` is that condition, for any lawful meter.
`Logic.Spec.runsOk` proves that a specification to frames with no error gives a run that succeeds, under every runner.
`Logic.SpecOn.runsOk` proves the same for a specification whose runner may fail only on the messages that it names.
It assumes a runner that never fails on those messages.
`Logic.not_runsOk_of_lt` proves that no run with less gas than `cost` succeeds, from a specification to a halt that pays `cost`, as above.

BLOCKHASH reads its hash from a list that the block transition builds from the recent blocks of the chain.
The Yellow Paper (Appendix H.2, [`Paper.tex`][yp-blockhash]) defines the result by a walk up the parent hashes instead.
So the two agree when the recent blocks are linked and reach back far enough.
`BlockChain.addBlock` (`Execution/Blocks/Transition.lean`) defines the chain after a block, and keeps its last 255 recent blocks.
`HistoryOk` (`Execution/Proofs/Blocks/History.lean`) says that the recent blocks are linked and not empty.
Each one is numbered one above the one before it and names the hash of that one as its parent hash.
The chain also holds at least as many recent blocks as the number of its last block, or 255 when that number is higher.
`stateTransition_historyOk` proves that a block that passes the transition keeps `HistoryOk`, and `genesis_historyOk` gives the start.
On such a chain, `blockHash_ancestor` proves that each of the last 256 blocks has an entry in the list, and that BLOCKHASH reads it.
For a block number `n` in the window, the entry is the hash of the last block when `n` is its number.
Otherwise it is the parent hash of the recent block numbered `n + 1`.
When a recent block is numbered `n`, the entry is its hash.
`ChainRun.windows` carries the whole result along a run of blocks.

The theorems assume `HistoryOk` of the first chain.
A chain with too few recent blocks does not meet it.
`blockHash_of_short` proves that on such a chain, BLOCKHASH gives 0 for a block inside the window that the list does not reach.
For example, from block 100 with only that block recent, BLOCKHASH in block 101 gives 0 for block 98, where the Yellow Paper gives the hash of block 98.
No theorem relates the recent blocks of a chain to a real network.

[yp-blockhash]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex

### System contracts

The four modules under `Execution/Proofs/Blocks/SystemCall/` for beacon roots, historical block hashes, withdrawal requests and consolidation requests prove the effects of their deployed bytecode.
Their `systemCall_set` and `systemCall_dequeue` theorems hold from each contract's activation, with the gas meter of the fork, including the state gas meter from Glamsterdam.
They require the specified bytecode at the contract's address.
The queue theorems assume bounds on the storage counters, and the history theorem requires a block number from 1 to below `2^256`.

`Logic.Reaches.followsMeter` lifts a normal one-counter run to the state gas meter when its execution gas initially covers that counter.
The counter pays execution gas and state gas and ignores refills, so it gives a conservative budget.
`Logic.SupportedCode` checks each opcode, skipping PUSH data, against a fixed list of instructions.
The list leaves out GAS and every instruction that sends a message.
The lifted run has the same fields outside its meter, including its state and output.
`SystemContract.systemCall_of_writesStorage` applies this result to the actual system-call runner and its initial reservoir.

### SHA-256 precompile

The precompile reuses the SHA-256 of the cryptography layer, so its theorems are about the gas and the failure.
`sha256_eq_ok_iff` and `sha256_eq_error_iff` (`Execution/Proofs/Evm/Precompiles/Sha256.lean`) prove that a call succeeds exactly when the gas covers `60 + 12 * ceil(len / 32)`, and then returns the digest of the whole call data.
`le_wordCount` and `wordCount_le` prove that the word count is the least number of 32-byte words that covers the call data.
`sha256_ok_eq_spec` carries `hash_eq_spec` over to the output, so the output is the FIPS 180-4 hash when the call data is shorter than 2^61 bytes.
`sha256_ok_eq_spec_of_gas` drops that hypothesis for every call that succeeds with less than `60 + 12 * 2^56` gas.
`gasCost_lt_two_pow_64` proves that the price of call data shorter than 2^63 bytes fits in the 64 bits the C export returns.

No theorem relates the module to the execution-specs code it follows, which calls `hashlib.sha256`.

### MODEXP

These theorems state agreement with EIP-198 and EIP-7823.
`compute_eq_pow_mod` (`Execution/Proofs/Evm/Precompiles/Modexp/Core.lean`) proves that the output is `BASE ^ EXPONENT mod MODULUS`, or 0 for a zero modulus.
It rests on `powMod_eq` (`Execution/Proofs/Evm/PowMod.lean`), which proves that the square-and-multiply loop equals `b ^ e % m`.
`modexp_outOfGas` and `modexp_ok` (`Execution/Proofs/Evm/Precompiles/Modexp/Core.lean`) prove that, with every length within the EIP-7823 bound, a call fails exactly when the gas is below the price.
`modexp_eq_ok_iff` (`Execution/Proofs/Evm/Precompiles/Modexp/Core.lean`) proves that a call succeeds exactly when, from Fusaka, every length is within the EIP-7823 bound and the gas covers the price, and that it then returns the computed output.
`modexp_eq_error_iff` (`Execution/Proofs/Evm/Precompiles/Modexp/Core.lean`) proves that a call fails exactly on the first oversized length, from Fusaka, in the order base, exponent, modulus, or else on gas below the price.

No theorem relates the module to the execution-specs code it follows.

### BLAKE2F

The theorems pin down the input format exactly, and state the compression function F against a model of RFC 7693.
`output_invalidInputLength`, `output_invalidFlag` and `output_ok` (`Execution/Proofs/Evm/Precompiles/Blake2f.lean`) prove that a call fails exactly when the input is not 213 bytes long, or its flag byte is neither `0` nor `1`.
Otherwise it returns `compute` of the input, which decodes the fields and runs F of RFC 7693 on them.
`blake2f_eq_ok_iff` (`Execution/Proofs/Evm/Precompiles/Blake2f.lean`) proves that a call succeeds exactly on a 213-byte input with enough gas and a flag byte of `0` or `1`, returning `compute` of the input with that flag.
`readWord_toNat`, `readRounds_toNat` and `writeState_word` state the encoding of EIP-152 for every input: the rounds field big-endian, every word little-endian, and the output in the encoding of the input.

`roundsFrom_bijective` (`Cryptography/Proofs/Hash/Blake2b.lean`) proves that the rounds of F permute the work vector.
The statement holds for every round count, message block and starting round.

`compress_toBitVec` (`Cryptography/Proofs/Hash/Blake2b.lean`) proves that F, read word by word as 64-bit vectors, is the F of a model of RFC 7693 §3.1 and §3.2.
The statement holds for every round count, state, message block, offset counter and flag.
The model rotates 64-bit vectors, and takes the offset counter as one 128-bit vector whose high word is `t1`.
It shares the IV and the message schedule with the code.
`IV_sqrt` derives the IV from square roots, and `SIGMA_perm` checks only that each row of the schedule is a permutation.

The output of F is also checked by the Python tests (`bindings/python/tests/precompile/test_blake2f.py`).
They run test vectors 0 to 7 of EIP-152, and read the rounds field of test vector 8.
They also run one full block of the BLAKE2 test vectors, and one call that sets `t1`.
Test vector 8 asks for `2^32 - 1` rounds, so no test checks its output.

### ECRECOVER

The ECRECOVER theorems rest on the secp256k1 ones, and all three are in `Execution/Proofs/Evm/Precompiles/Ecrecover.lean`.
`output_sign` proves that a signature made with a private key returns that key's address.
`output_verify` proves that a nonempty output is the address of a key that verifies the signature.
`output_of_verify` proves that every key that verifies a signature has its address returned for `v = 27` or `v = 28`, when `r + n >= p`.

No theorem relates the module to the execution-specs code it follows, which calls a C library to recover the key.

### P256VERIFY

The P256VERIFY theorems rest on the secp256r1 ones, and are in `Execution/Proofs/Evm/Precompiles/P256Verify.lean`.
`isValid_callData` proves that, on the 160-byte call data of EIP-7951 with an affine public key, the input check gives the result of ECDSA verification.
`p256Verify_callData_sign` proves that a signature from the signing operation of SEC 1 returns the word 1 under its public key, when the call has at least 6900 gas.
`p256Verify_callData_neg_s` proves that, for `s` in `(0, n)`, `(r, s)` and `(r, n - s)` give the same result at every gas limit.
Either both signatures are valid or neither is, so the call does not require a low `s`.
`exists_p256Verify_eq_ok_valid` proves that the valid output is reachable.
The witness signs the hash 0 with the private key 1 and the nonce 1.
So the public key and the point `R = k G` are both the base point.

No theorem checks the module against the EIP-7951 pseudocode line by line.
The Python test `bindings/python/tests/precompile/test_p256verify.py` runs it on the 781 test vectors of EIP-7951, 778 of which come from Wycheproof.

### EIP-2537 precompiles

The BLS12-381 precompiles read and write field elements and points in the encoding of EIP-2537.
`bytesToG1_g1ToBytes` and `bytesToG2_g2ToBytes` (`Execution/Proofs/Evm/Precompiles/Bls12381/RoundTrip.lean`) prove that decoding the encoding of a valid point gives the same group element.
With the subgroup check, the same holds for a point of the subgroup.
`g1ToBytes_bytesToG1` (`Execution/Proofs/Evm/Precompiles/Bls12381/Encoding.lean`) and `g2ToBytes_bytesToG2` prove the converse, so every decoded point has one encoding.
The same file proves the round trips of a field element, an element of `Fp2` and the padding.

`valid_of_bytesToG1_eq_ok` and `valid_of_bytesToG2_eq_ok` (`Execution/Proofs/Evm/Precompiles/Bls12381/Group.lean`) prove that every decoded point is valid.
`inSubgroup_of_bytesToG1_eq_ok` and `inSubgroup_of_bytesToG2_eq_ok` prove that a point decoded with the subgroup check lies in the subgroup.
`bls12G1Add_eq_ok_iff` and `bls12G2Add_eq_ok_iff` (`G1.lean` and `G2.lean` in the same directory) prove that G1ADD and G2ADD return the encoding of the sum of their two decoded points.
`toPoint_add_of_bytesToG1_eq_ok` and `toPoint_add_of_bytesToG2_eq_ok` prove that this sum maps to the sum of the two points on the curve.
`bls12G1Add_g1ToBytes` and `bls12G2Add_g2ToBytes` prove the converse: on the encodings of two valid points, with enough gas, both return the encoding of their sum.
Neither precompile checks that its inputs lie in the subgroup, as EIP-2537 specifies.
So the sum is taken in the full group of points of each curve.
`exists_bls12G1Add_ok` and `exists_bls12G2Add_ok` apply this to two copies of each generator.

`bls12G1Msm_eq_ok_iff` and `bls12G2Msm_eq_ok_iff` (`G1.lean` and `G2.lean`) prove that G1MSM and G2MSM return the encoding of the sum of their pairs.
`g1Msm_eq_ok_iff` and `g2Msm_eq_ok_iff` (`Execution/Proofs/Evm/Precompiles/Bls12381/Msm.lean`) prove that this sum succeeds exactly when every point decodes with the subgroup check.
`toPoint_of_g1Msm_eq_ok` and `toPoint_of_g2Msm_eq_ok` prove that it maps to the sum of `m_i • P_i` on the curve.
Each scalar `m_i` is the integer of its 32 bytes, not reduced modulo the subgroup order, as EIP-2537 allows.
`inSubgroup_of_mem_g1Msm` and `inSubgroup_of_mem_g2Msm` prove that every decoded point lies in the subgroup.
`toPoint_g1Msm_generator` and `toPoint_g2Msm_generator` apply this to the generator with any scalar.
`G1.lean` and `G2.lean` also bound the MSM discounts, so an MSM never costs more than its separate multiplications.

`bls12Pairing_eq_ok_iff` (`Pairing.lean` in the same directory) proves that the pairing check succeeds exactly when every padding is zero and every point decodes with the subgroup check.
It then returns the word of `pairingCheck` on the decoded pairs.
`exists_represents_of_decodePairs` (`PairingProduct.lean`) proves that each decoded `P_i` represents some `a_i • g_1`, and each `Q_i` some `b_i • g_2`.
`bls12Pairing_eq_one_iff` proves that the output is the word 1 exactly when `sum_i a_i * b_i = 0`, that is, when the product of the pairings is 1.
`bls12Pairing_encodePairs` computes the output on the encodings of any represented pairs.
`bls12Pairing_generators` and `bls12Pairing_generator_neg` apply it to reach both outputs: 0 for `(g_1, g_2)`, and 1 for `(g_1, g_2)` with `(-g_1, g_2)`.

`bls12MapFpToG1_eq_ok_iff` and `bls12MapFp2ToG2_eq_ok_iff` (`G1.lean` and `G2.lean`) prove that the two map precompiles return the encoding of the curve map of their decoded field element.
The curve maps of RFC 9380 never fail.
So `bls12MapFpToG1_isOk_iff` and `bls12MapFp2ToG2_isOk_iff` (`Map.lean`) prove that each map precompile succeeds exactly when the length and gas checks pass and its padded field element decodes.
`inSubgroup_of_bls12MapFpToG1_eq_ok` and `inSubgroup_of_bls12MapFp2ToG2_eq_ok` prove that every output encodes a valid point of the subgroup.
`bytesToG1_of_bls12MapFpToG1_eq_ok` and `bytesToG2_of_bls12MapFp2ToG2_eq_ok` prove that the point decoder, with the subgroup check, accepts that output.
`bls12MapFpToG1_pad` and `bls12MapFp2ToG2_pad` prove that the padded encoding of every field element succeeds with enough gas.

No theorem relates the module to the execution-specs code it follows.

### A transaction whose message fails

`Execution/Proofs/Transactions/Failed.lean` states what a transaction leaves when its message fails, before Hegotá.
Its first theorems bound the writes to the sender, the beneficiary and the authorities that the authorization signatures name.

`buyGas_sender` in `Settlement.lean` proves that buying gas raises the nonce of the sender by one and takes the fees from its balance.
`buyGas_keeps` proves that it changes no code hash of the sender, no word of storage and no code.
`settleGas_accounts` proves that the settlement refunds the sender and pays the priority fee to the beneficiary.
It changes no nonce, code hash or code.
Storage stays at the sender when its nonce is not 0, and at the beneficiary unless it is deleted.

`authority_applyAuthorization` in `Authorization.lean` proves that one accepted authorization in scope sets the code hash of its authority to that of the delegation code, and raises its nonce by one.
`foldlM_applyAuthorization_authority` unrolls the whole list for an authority whose code is empty or a delegation indicator.
`acceptedBy` lists the authorizations that such an authority accepts, in order: those in scope, signed by it, with its nonce at that point.
After the list, the authority has one more nonce for each of them and the code of the last one, and the rest of its account stays.
The hypothesis on the code matters: an authority with other code refuses every authorization.
`foldlM_applyAuthorization_keeps` covers such an authority, under the hypothesis that no authorization sets a code with its code hash.
`processMessageCall_of_halt` in `Process.lean` puts the state back to the state before the authorizations when the message halts before its first frame, as EIP-8037 asks.
`processMessageCall_reads_of_error` proves that a failed frame reads as the state of its first frame, so a failed call keeps its accepted authorizations, as EIP-7702 asks.

`runTransaction_values_of_error` combines these results for one gas meter.
It names the output of the message call.
It gives the nonce, the code hash and the balance of every address against the state before settlement.
It gives the storage of every address but a deleted beneficiary.
That state reads as the state after the gas purchase when the transaction creates a contract or its first frame never starts.
When the first frame of a call starts and fails, it reads as the state that the authorizations leave.
`processTransaction_values_of_error` gives the same conclusion for every fork before Hegotá, with the gas meter of that fork.
`processTransaction_authority_of_error` gives each authority whose code is empty or a delegation indicator its values after the transaction.
Its nonce is its nonce before the transaction, plus one for the sender, plus one per accepted authorization.
Its code hash is that of the code the last one sets.
From Glamsterdam it needs the first frame of the call to start, which `FirstFrameHalts` denies.
Up to BPO5 it needs nothing more, since `aborts_of_prepareFirstFrame_of_lt_glamsterdam` in `Process.lean` shows that a call halts before its first frame only with an error that aborts the run.
`processTransaction_authority_of_firstFrameHalts` covers the halt from Glamsterdam: every authority keeps its code hash and its nonce, plus one for the sender, as EIP-8037 asks.
`processTransaction_authority_keeps_of_error` covers an authority with other code, which refuses every authorization: its account and its storage stay.
It assumes that no authorization sets a code with the code hash of the authority.
No theorem yet gives the storage of an authority that takes a delegation.
From Paris, an authority left empty by an authorization to the zero address is deleted with its storage, so that claim needs a condition.
`processTransaction_selfAuthorization_of_error` in `Replay.lean` applies the first theorem to a sender that signs its only authorization with the nonce of the transaction plus one.
It ends two nonces above the transaction.
`block_of_output` proves that the block after the transaction reads as the state that the transaction leaves.

### Transaction gas

Four theorems in `Execution/Proofs/Transactions/Process.lean` give the gas used and the block gas of a transaction that runs, before Hegotá.
`processTransaction_gasUsed_of_lt_london` covers the forks before London, where the refund is at most half of the gas used before it.
`processTransaction_gasUsed_of_london_of_lt_pectra` covers London to Dencun, where EIP-3529 caps the refund at a fifth of the gas used before it.
`processTransaction_gasUsed` covers Pectra to BPO5, where EIP-7623 raises the gas used to the call data floor when that floor is larger.
`processTransaction_gasUsed_of_glamsterdam` covers Glamsterdam, where EIP-8037 splits the gas into execution gas and a reservoir.
Its gas left is the execution gas left plus the reservoir left, and it gives the two block gas counts of EIP-7778 and EIP-8037.
At Glamsterdam, a negative state gas used counts as 0 in both block gas counts, a case that EIP-8037 leaves open.
From Hegotá a run fails as not yet specified, so there is no gas used to state.

`prepareFirstFrame_of_applyAuthorizations` gives the first frame of a call that moves no ether, after its authorizations.
`prepareFirstFrame_of_applyAuthorizations_error` proves that an error of the authorizations is the error of the first frame.
`prepareFirstFrame_of_value_eq_zero` gives the first frame of a call that moves no ether and applies no authorization.

### Nonces within 64 bits

EIP-2681 limits every nonce to `2^64 - 1`, and a nonce in EthLib is a natural number.
`TransactionState.NoncesFit`, `BlockState.NoncesFit` and `State.NoncesFit` say that every account has a nonce of at most that bound; an absent account reads as nonce 0.
`noncesFit_processMessage` and `noncesFit_processCreateMessage` (`Execution/Proofs/Evm/Call/NoncesFit.lean`) prove that every call and creation keeps the bound, at every fork.
A creation needs its new address to start with a nonce below the bound.
The new address of a creation sent by CREATE or CREATE2 has a nonce of at most 1, so it meets that condition.
`noncesFit_processTransaction` (`Execution/Proofs/Transactions/NoncesFit.lean`) proves it for a transaction that passes its inclusion check.
That check makes the nonce of the transaction equal that of its sender, and below the bound.
`stateTransition_noncesFit` (`Execution/Proofs/Blocks/NoncesFit.lean`) proves that a block that passes its transition keeps the bound of the state before it.
The bound on the state before the first block is a hypothesis: the genesis allocation must meet it.
From Glamsterdam, `stateTransition_rebuild_nonce` turns the 64-bit nonces that the block access list rebuilds into the nonces after the block, with no loss.

### Logs paid for by gas

The weight of a log, `48 + 33 * topics + data bytes`, bounds the length of its RLP encoding, for a log whose weight is below `2^64` (`encode_log_size_le`).
`processMessage_logsWeight` and `processCreateMessage_logsWeight` (`Execution/Proofs/Evm/Call/LogsPaid.lean`) bound the logs of a message by its gas.
Four times the weight of its logs, plus the gas it holds, never rises above the gas it starts with plus one allowance.
The allowance is 716 from Glamsterdam, four times the weight of an EIP-7708 transfer log, and 0 before.
It holds at every fork and for every lawful meter.
`processTransaction_logsWeight` (`Execution/Proofs/Transactions/LogsPaid.lean`) bounds the logs of a transaction by its gas limit plus that allowance.
`processMessageCall_logsWeight` gives the same bound for the message of a transaction.
It assumes that a commit of the meter raises no gas held, which both meters of the forks meet.
`encode_makeReceipt_processTransaction` then proves that the receipt of a transaction encodes, when its gas limit and the cumulative gas it records are below `2^64`.
No theorem yet derives those two bounds from the validity of a block.
Both transaction theorems hold only before Hegotá: from Hegotá a transaction fails as not yet specified, so it has no receipt.

### The supply of ether

`Execution/Proofs/State/Supply.lean` defines the supply of a transaction state as the sum of the balances of all its accounts.
`Execution/Proofs/Evm/Call/Supply.lean` proves that no call or creation raises it, at every fork.
`processTransaction_supply_le` in `Execution/Proofs/Transactions/Supply.lean` proves that a transaction lowers it by at least its burned fees: the base fee times the gas used, and the blob fee.
It assumes that the gas limit covers the least gas and that the price per gas covers the base fee, which the checks of the block ensure.

The equality holds in two cases.
`processTransaction_supply_of_glamsterdam` gives it from Glamsterdam, where SELFDESTRUCT and the deletions keep every balance.
`processTransaction_supply_of_dencun` gives it from Cancun for a transaction that creates no account.

Before Cancun, a SELFDESTRUCT whose beneficiary is its own account burns that balance inside the message, and the deletions burn what a marked account received after it.
The same holds from Cancun until Glamsterdam for a transaction that creates an account.
`processTransaction_supply_eq` in `Execution/Proofs/Transactions/Burn.lean` gives the exact change for every transaction that runs, at every fork, these cases included.
The supply after the transaction, plus the burned fees, the burns of SELFDESTRUCT and the deleted balances, is the supply before.
The burns come from a certificate of the run of the message, `RunBurns` in `Execution/Proofs/Evm/Call/BurnRun.lean`.
Each rule of the certificate takes one equation of the interpreter: a step from a running frame, a halt, a stop, a resume, a failed resume, the choice of a precompile, the entry of a call, its rollback, or the deposit of code.
Its other premises are side conditions that the run implies, such as the block of the state it keeps.
So a certificate follows the run step by step.
`RunBurns.ended_eq` proves that two certificates from the same start end in the same frame, and `RunBurns.total_eq` that they have the same total.
The log of a certificate records each burn of SELFDESTRUCT, and a frame that rolls back, or a creation whose deposit of code fails, drops what it burned.
`RunBurns.counted` proves that each burn the log counts is the burn of a step that runs SELFDESTRUCT, above 0, in the account the burn is from.
That step starts from a running frame that the run reaches, as `RunReaches` follows the same rules as the certificate.
The deleted balances are read after the gas is settled and before any account is deleted, once for each account.
`processTransaction_transactionBurns` proves that every transaction that runs has a certificate, and `TransactionBurns.unique` proves that all its certificates give the same two amounts.
From Glamsterdam, `TransactionBurns.eq_zero_of_glamsterdam` proves that both amounts are 0.
`processTransaction_supply_eq` makes the same two assumptions as `processTransaction_supply_le`.

`Execution/Proofs/Blocks/Burn.lean` gives the exact change of the supply across a whole block, and `Execution/Proofs/Blocks/Supply.lean` derives the bound and the Glamsterdam equality from it.
The block creates the wei of its withdrawals from Shapella, by EIP-4895, and of its rewards before Paris.
The DAO transfer only moves wei.
`stateTransition_supply_le` proves that the supply after the block plus the burned fees is at most the supply before plus the created wei, at every fork that the transition runs; it fails from Hegotá.
`stateTransition_supply_of_glamsterdam` proves the equality from Glamsterdam.
`stateTransition_supply_le_of_lt_glamsterdam` writes the burned fees from the header before Glamsterdam: the gas used and the blob gas used, each at its base fee.
From Glamsterdam the gas used of the header is the larger of the execution gas before the refunds, by EIP-7778, and the state gas, by EIP-8037, so it does not give the burned fees.
There the theorems take the fees from the body that the transition runs.
`stateTransition_supply_eq` in `Execution/Proofs/Blocks/Burn.lean` gives the exact change at every fork that the transition accepts.
It adds the created wei and subtracts the burned fees, the surviving SELFDESTRUCT burns and the deleted balances.
`BodyBurns` certifies the system calls before the transactions, each transaction in order, and the calls that read requests.
The system calls also carry burn logs, since the theorem assumes no particular code at their addresses.
`BlockLosses.transactions` retains each transaction's burn log and deleted balances.
`BodyBurns.total_eq` shows that two certificates of the same body give the same total of losses, when the block has at most two ommers before Paris, as its checks enforce.
So the run fixes that total.
From Glamsterdam, `BodyBurns.total_eq_zero_of_glamsterdam` proves that the total of losses is 0.

### The authorizations of EIP-7702

`Execution/Proofs/Transactions/Authorization.lean` covers every case of one authorization, at every fork.
`applyAuthorization_cases` proves that an authorization that succeeds is skipped, refused, or accepted after it pays and delegates.
`applyAuthorization_of_accepts_of_pay` gives an accepted authorization from what its payment leaves.
`applyAuthorization_of_payAuthorization_error` proves that a failed payment stops the authorizations with its error.
`applyAuthorization_of_authorityAccepts_error` proves that an authority whose code cannot be read stops them with that error.
`payAuthorization_eq_ok_iff` proves that from Glamsterdam a payment succeeds exactly when its charge does.
`state_payAuthorization` proves that a payment keeps the state, the accesses and the refund.
`sameOutside_delegate` proves that a delegation changes no account, storage or transient storage but the authority's.
`getCode_delegate_of_ne` proves that a delegation keeps the code under every hash but the hash of the code it sets.
`getCode_delegate_self` proves that a delegation stores the code it sets under its hash, when that hash is not the hash of the empty code.

Real code is neither empty nor a delegation indicator.
`authorityAccepts_of_code` proves that an authority with real code refuses every authorization.
`foldlM_applyAuthorization_keeps` proves that the authorizations keep the account, storage, transient storage and code of an address with real code.
It assumes that no authorization of the list carries a code to set whose Keccak-256 hash is the code hash of that address.
When the state stores each code under its own hash, only a collision of Keccak-256 breaks this assumption.
`meter_foldlM_applyAuthorization_of_lt_glamsterdam` proves that up to BPO5 the authorizations keep the meter.

The two theorems below hold for any recovery of an authority.
Both assume that the state holds the code of every account.
`foldlM_applyAuthorization_isOk_of_lt_glamsterdam` proves that up to BPO5 the authorizations succeed over any meter.
`foldlM_applyAuthorization_isOk` proves that the authorizations succeed, and from Glamsterdam take at most 227790 execution gas times their number.
From Glamsterdam, it assumes that the meter holds that much gas for every authorization.
From Glamsterdam, it also assumes that the state holds the code of every account before the transaction.
From Glamsterdam, it also assumes that every charge within the gas left succeeds and takes at most its amount.

`chargesWithin_nat` proves this last condition for the meter up to BPO5.
`chargesWithin_stateGasMeter` proves it for the meter of EIP-8037.

### Merkle Patricia Trie

The trie commits to a map from byte keys to byte values under one 32-byte root.
Two theorems in `Execution/Proofs/Trie/Binding.lean` describe what the root binds, for every hash.

The first is `verifyProof_binding`, about two Merkle proofs of one key that verify against one root.
They are one proof and give the key one value.
Otherwise `findProofCollision` returns two different nodes of the proofs with one hash.
The second is `root_binding`, about two tries with one root.
They give every key one value, or `findCollision` returns such a collision in the proofs of that key.
Both searches are proved to return only collisions, and to return none for an input compared with itself.

`verifyProof_sound`, in the same file, compares a proof with the proof that the trie builds for the key.
The proof is that honest proof and gives the trie's value of the key.
Otherwise `findProofCollision` returns a collision between the two proofs.

A secured trie hashes each key into its path, so two of its keys can have one path.
`root_binding` and `verifyProof_sound` name that case too.
There `findPathCollision` returns two different keys of the trie with one hash.
It searches only a secured trie, and it is proved to return only collisions.
`findKeyCollision_of_nodup` proves that the key search returns none for keys with distinct hashes.

Both theorems assume that the keys of each trie are distinct, as the keys of a map are.
The variants `root_binding_foldl_trieSet` and `verifyProof_sound_foldl_trieSet` apply to tries built by setting any list of key-value pairs from an empty trie.
Later entries replace earlier values of the same key, and an empty value removes its key.
`nodup_keys_foldl_trieSet` proves that this construction gives distinct keys, as the trie of Yellow Paper Appendix D (Shanghai version) assumes, so callers need no distinctness hypothesis.
This construction is the path of Python `trie.root`, through `Execution/Exports/Trie.lean`.
`root_of_rootExport` (`Execution/Exports/Proofs/Trie.lean`) proves that the export returns the root of this trie, built from its decoded pairs.
`rootExport_of_root` proves the converse, so the two variants apply to the output of Python `trie.root`.
The state and storage roots in `Execution/State/Root.lean` build tries directly, and `stateEntries_nodup` and `storageEntries_nodup` (`Execution/Proofs/State/Root.lean`) supply their distinct keys.
`root_binding_secured` (`Execution/Proofs/Trie/Binding.lean`) applies `root_binding` to two secured tries with distinct keys and one root.
The two tries give every key one value, or `findSecuredCollision` returns a collision in the proofs of the key or among the keys.
`storageRoot_binding` proves that two storages with one root give every key the same word, `0` when unset.
Otherwise `findStorageCollision` returns a collision.
`stateRoot_binding` applies `root_binding_secured` to the state trie and then `storageRoot_binding` at each address with an account.
Two states with one state root give every address the same account, and at every address with an account every key the same word, or `findStateCollision` returns a collision.
Storage at an address without an account is outside `stateEntries`, and code is committed only through `codeHash`.
So the state root binds no storage at an address without an account, does not separate a key set to `0` from an unset key, and binds nothing in the code map beyond each account's `codeHash`.
The storage and state searches are proved to return only collisions, and none for an input compared with itself.
No theorem bounds the probability of finding two storages or two states with one root that differ.
The indexed roots in `Execution/Blocks/Roots.lean` also build tries directly, with the RLP encoding of each index as its key.
`indexedEntries_nodup` (`Execution/Proofs/Blocks/Roots.lean`) supplies their distinct keys, since the RLP decoder reads each index back from its encoding.
Applied to the plain tries of two lists with these distinct keys, `root_binding` shows that two lists with one root give every key one value.
Otherwise `findCollision` returns a collision in the proofs of that key.
The path searches return nothing there, since the trie is not secured.
`indexedRoot_binding` concludes that the two lists are equal, or `findIndexedCollision` returns a collision in the proofs of one index.
Two transactions, or two withdrawals, with the same bytes are equal, so `transactionsRoot_binding` and `withdrawalsRoot_binding` conclude the same for the lists themselves.
`receiptsRoot_binding` does so for receipts whose types are below `0xc0`, which holds for type 0 and for every type that a fork adds.
No theorem bounds the probability of the indexed-root search itself.
The bound below covers two tries that give one key two values.

`Execution/Proofs/Trie/RandomOracle.lean` turns this binding into a probability bound, with the hash a random oracle.
The trie definitions take their hash in any monad, so the experiment runs the root of the specification with a hash that queries the oracle.
An adversary outputs two tries and a key.
The experiment computes both roots and both proofs of the key, then queries the key, every key of both tries and every node of both proofs.
The adversary wins when the tries are both secured or both plain, each has distinct keys, and they have one root, yet give the key different values.
`collision_of_extract` shows that every win leaves two different cached inputs with one answer.
The searches `findCollision`, `findPathCollision` and `findLookupCollision` name them, run with a table that agrees with the cache.
`prEvent_wins_le` then bounds a win by `Q^2 / N` through `prEvent_experimentWith_le`, where `Q` bounds the queries of the whole experiment.
`prEvent_wins_le_two_pow` states it with `N = 2^256`.
The bound needs no hypothesis that the cache covers the witnesses, since the experiment queries them itself.
One oracle answers keys and nodes alike, so a collision between a key and a node counts too.
The first trie may be fixed before the run, so the same bound covers a second trie with the root of a given one.
That bound is still `Q^2 / N`, not a sharper fixed-target bound.
`Q` counts every hash call of the experiment, repeats included, and the extraction makes many: each proof level rebuilds its subtree.

`verifyAccountRange_complete` and `verifyStorageRanges_complete` (`Execution/Proofs/Network/SnapRangeComplete.lean`) prove that honest snap answers from secured tries pass their checks, or `findCrossCollision` returns a Keccak-256 collision among proof nodes.
The keys are listed by increasing hash, and the proof contains the proofs of the start and the last entry.
That order assumes the keys of each trie have distinct Keccak-256 hashes; no search returns two keys with one hash.
The account theorem uses successful slim and full encodings of each account; `fullAccount_encode_slimAccount` proves that the conversion returns the full form.
The storage theorem assumes whole tries before the last range; every range starts at the requested hash for one account and at the zero hash for several.
`verifyAccountRange_complete_nil`, `verifyStorageRanges_complete_nil`, `verifyAccountRange_whole` and `verifyStorageRanges_whole` cover empty last ranges and whole tries; whole tries need no proof and no collision alternative.
An empty AccountRange with no proof is the empty reply `noState`, rather than a claim about the trie.
`findCrossCollision_self` shows that the search finds none when the sent proof is the honest one and holds no collision.
No theorem bounds the probability that `findCrossCollision` finds a collision.

An answer of `eth_getProof` (EIP-1186) is checked against a state root by `AccountProof.verify` (`Execution/State/AccountProof.lean`).
It checks the account proof, then each slot proof against the storage root of the answer.
`verifyAccount_sound` and `verifySlot_sound` (`Execution/Proofs/State/AccountProof.lean`) carry `verifyProof_sound` over to the fields of the answer.
Take a secured trie with distinct keys and its root.
When a check passes, the trie's value under the key decodes to the fields of the answer.
When the check reports absence, the trie holds no value under the key.
A slot reported absent also has the word 0 in the answer.
Otherwise a search returns a collision with the trie's own proof, or two keys with one hash.
`verifyAccount_sound_state` and `verifySlot_sound_storage` apply them to the tries of a state, whose keys are distinct.
`verifyAccount_getProof` and `verifySlot_getProof` prove that the trie's own proofs pass, with the fields that the trie holds.
A proof can show that the address has no account, or that a slot is not set.
The storage value of a slot that is not set is 0, so the answer must give that word.
EIP-1186 does not say which fields the answer holds for an address without an account.
So the check judges no field of an absent account, and reports the absence.

The node's side is `AccountProof.ofState`: the answer that a state gives, with the proofs of its own tries.
For an address with no account it gives the fields of the empty account and the root of the empty trie, one of the two readings that the check accepts.
`ChainView.accountProof` (`Execution/Rpc/Proof.lean`) serves it as `eth_getProof` at the block that the parameter names.
`verify_ofState` (`Execution/Proofs/State/AccountProofOfState.lean`) proves completeness: the answer passes the check against the state root.
It reports the account present exactly when the state has it, and, for a present account, each slot set exactly when its word is not zero.
The theorem does not assume distinct key hashes.
When the answer does not pass, the search `findAnswerCollision` returns two keys with one hash.
It reads the address, the addresses of the state, the slots asked for and the storage keys of the address.
It assumes that an address with no account has the word zero at each slot asked for.
No theorem shows that the state transition keeps that property, though the fixtures expect the word zero there.
`Valid.verify_accountProof` applies it to a canonical block of a valid view, against the state root of its header.
An answer at the pending block or at a block off the canonical chain is not covered, since the view does not check their states.
`accountProof_agree` proves that the balance, the nonce and the words of the answer are those of `eth_getBalance`, `eth_getTransactionCount` and `eth_getStorageAt` at the same block.
`accountProofOfJson_accountProofJson` proves that the reader reads back what the writer writes, for a nonce below `2^64`.

### The RLPx session

`receive` (`Networking/Devp2p/Session.lean`) follows an RLPx session after the handshake, frame by frame.
It follows ["p2p" Capability](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#p2p-capability), [Message Encoding](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#message-encoding) and [Message ID-based Multiplexing](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#message-id-based-multiplexing) in `rlpx.md`.
Before the peer's Hello, only Hello and Disconnect pass, and Hello opens the session.
In an active session, a Ping asks for a Pong.
After a Disconnect, every frame is rejected.
An ID from `0x10` on goes to the shared capability that holds it, and `route` gives that capability and the relative ID.

`receive_beforeHello`, `receive_hello_active`, `receive_ping` and `receive_closed` (`Networking/Proofs/Devp2p/Session.lean`) state these steps.
`route_negotiate` states that each ID a shared capability holds routes to it, and `route_negotiate_of_lt` that no ID below `0x10` does.
`route_injective` states that two IDs never route to one place, and `route_comm` that both peers route every ID the same way.
`messageCount_le_iff_unknownId` (`Execution/Proofs/Network/Message.lean`) states that the IDs an eth version holds are those below the first ID from which its decoder rejects every ID as unknown.
No theorem says anything about a sequence of frames beyond one step, or about timeouts.

The source leaves three points open, and the session reads them as follows.
It reads a Disconnect sent instead of Hello uncompressed, as it reads Hello, though "All messages following Hello are compressed" could be read otherwise.
It never rejects a Hello for its version, as "Implementations must ignore any difference in protocol version" asks.
It does not check the identities that the reasons `0x07`, `0x09` and `0x0a` name, which the source does not require.

The session also rejects the data of a capability message above 16 MiB, compressed or not.
"Message Encoding" says that messages carrying more "should be rejected by closing the connection".
Compressed data is rejected when its Snappy header declares more, before it is decompressed.

### The eth session

`receiveEth` and `sendEth` (`Execution/Network/Session.lean`) follow an eth session with one peer, message by message, and `EthSession.run` follows a list of sent and received messages.
They follow [Basic Operation](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#basic-operation), [Protocol Messages](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#protocol-messages) and [Transactions (0x02)](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#transactions-0x02) in `caps/eth.md`.
Before the peer's Status, only a Status that passes `checkStatus` is accepted, and until both Status messages have passed, this node sends nothing but Status.
The session keeps the requests that this node sent and that no response has answered yet, and a response must answer one of them.
It keeps the hashes of the transactions sent, in Transactions or PooledTransactions, and received, and refuses a Transactions message that would send a transaction twice, or back to the peer that sent it.
It also refuses an empty Transactions message, which "Transactions (0x02)" forbids.
On the proof-of-stake networks that the session assumes, NewBlockHashes and NewBlock are discarded.
`snapAllowed` says whether the shared capabilities meet the requirement of snap, since [Relation to eth](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md#relation-to-eth) makes snap "a dependent satellite of eth".

`receiveEth_beforeStatus`, `receiveEth_status_iff`, `receiveEth_response`, `receiveEth_unsolicited`, `receiveEth_discard`, `receiveEth_secondStatus`, `receiveEth_sentTxs` and `receiveEth_receivedTxs` (`Execution/Proofs/Network/Session.lean`) state the receiving steps.
`sendEth_beforeStatus`, `sendEth_beforeOwnStatus` and `sendEth_pending` state the sending steps.
`run_sentTxs` and `run_no_resend` state that along any run of a session, a Transactions message sends no transaction that went out before, and none that the peer sent before it.
`snapAllowed_iff` states that the requirement holds exactly when a capability named eth is shared.
The session pairs a response with its request; the content of the response is judged apart, by `checkHeaders`, `receiptsMatch` and the other checks.

The source leaves five points open, and the session decides none of them.
A second Status from the peer gives the error `secondStatus`, and the source fixes no reaction to it; this node may send a Status at any time.
A response that answers no pending request gives `unsolicited`; the source fixes a reaction only for the elements of Cells, a disconnect.
A snap message on a connection without eth has no reaction in the source, and `snapAllowed` only names the case.
A peer that keeps sending NewBlock or NewBlockHashes "should be disconnected", with no count, so each such message is only discarded.
A peer that sends a transaction twice, or back to this node, breaks the rule of "Transactions (0x02)", but the source fixes no reaction, so the session accepts the message.

The session also leaves out "A node should never send a transaction back to a peer that it can determine already knows of it" ([Transaction Exchange](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#transaction-exchange)), which also covers announcements.
A PooledTransactions answer is never refused for a resend in an active session, and the session counts its transactions as sent, since "must not resend the same transaction" names no message.
The session does not track the requests of the peer, so it does not check what a sent response answers, and two answers may carry one transaction.
The session accepts a message from the peer before this node has sent its own Status, though the peer must wait for it; the source fixes no reaction.
It reads every message, sent or received, as one of the negotiated version, which the decoder of that version ensures.
Two pending requests may share a request ID, and a response then removes the oldest one that it answers.
No decoded item fails to encode, since a length must reach `2^64` for that.
If one did, its transaction would have no hash and would reject its whole message, while [Transaction Encoding and Validity](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#transaction-encoding-and-validity) asks only to discard invalid transactions.
The session accepts an empty Transactions message from the peer, which the source only discourages.

### multistream-select negotiation and the TCP upgrade

`listen` and `dial` (`Networking/Libp2p/Multistream.lean`) are the two peers of a multistream-select negotiation, and `run` lets them read each other's messages until both stop.
They follow [libp2p connections, "multistream-select"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#multistream-select) and the [multistream-select README](https://github.com/multiformats/multistream-select/blob/9a1fbe8edadebea223f47102f1913b8026c23a1c/README.md#protocol).
Each peer sends its header at the start, and aborts when its first message is not the header of the other.
A dialer with no proposal sends nothing and fails, a case the sources leave open.
The dialer sends its first proposal with its header, and its next proposal after each `na`.
The listener echoes a proposal it supports, compared byte for byte, and answers `na` to any other.
`negotiate_eq_find` (`Networking/Proofs/Libp2p/Multistream.lean`) proves that the agreed protocol is the first proposal that the listener supports.
`negotiate_agree`, `run_of_find_some` and `run_of_find_none` prove that the listener then agrees on it too, or still waits when there is none.
Each of them assumes that no proposal is `na`: a dialer that proposes `na` cannot tell an echo from a refusal.

`upgrade` (`Networking/Libp2p/Upgrade.lean`) negotiates the security protocol, then the multiplexer, of a TCP connection between consensus nodes, as in [Upgrading Connections](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#upgrading-connections).
Each node proposes and supports `/noise` alone, the protocol ID of [noise-libp2p](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/noise/README.md#negotiation), and then `/yamux/1.0.0` if it supports yamux, then `/mplex/6.7.0`.
That follows the phase 0 networking specification of the consensus layer.
On TCP, it requires Noise and mplex, allows yamux, and puts yamux first when a node supports it.
`upgrade_eq` (`Networking/Proofs/Libp2p/Upgrade.lean`) proves that any two such nodes agree on Noise, then on yamux exactly when both support it, and on mplex otherwise.
The Noise handshake that runs between the two negotiations is not run here.
The multiplexer always has its own negotiation: the inlined muxer negotiation of the same document is optional and is left out.

The sources leave five points open, and the model takes the narrowest reading of each.
A dialer that gets an answer that is neither its proposal nor `na` stops in the state `unexpected`, since no source fixes a reaction.
Listing with `ls` is optional, and the listener leaves it out, so it treats `ls` as an ordinary proposal, refused unless supported.
Simultaneous open serves hole punching, while the consensus layer requires endpoints that peers can dial, so it is left out.
The consensus layer names only Noise for TCP, and does not say whether a node may propose another security protocol first.
The profile proposes Noise alone.
Which messages share a packet is not modelled; the recommendation to send the header with the first proposal or answer changes no message.

### The gossip RPC and the partial message extension

The gossip RPC (`Networking/Gossip/Rpc.lean`) carries the fields of the partial message extension, from the [gossipsub v1.3 schema](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.3.md#protobuf) and the [partial messages schema](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/partial-messages.md#protobuf).
They are the two partial flags of a subscription change, the extensions of a control message, and the partial message of an RPC.
The partial columns of the consensus layer travel in these fields.
`decodeRpc_encode` (`Networking/Proofs/Gossip/Rpc.lean`) covers them, and three theorems prove that a subscription change, a control message or an RPC without these fields decodes them at their defaults.
`ofGroupId` (`Consensus/DataAvailability/Column.lean`) reads a group ID back, and `ofGroupId_toGroupId` proves that it reads the ID of every group back to that group.
`ofGroupId_version` proves that an ID whose first byte is not the version 0 names no group.

The model takes these readings.

- A singular message field that occurs twice keeps its last occurrence whole, and so do the extensions across the occurrences of the control field.
  Protobuf merges the occurrences field by field, so the readings differ whenever the last occurrence leaves out a field that an earlier one set.
- The encoder writes the flags only when true, and the extensions, the partial message, its partial message bytes and its parts metadata only when present.
  So an RPC without extensions encodes as before, and a node can leave out the partial message bytes that a peer did not ask for, as the partial messages document requires.
  The topic and group ID of a partial message are always written.
- The experimental extension fields are skipped, like any field the schema does not name.
- `SubOpts.sendsPartial` reads a request for partial messages as support for sending them, as the schema says, and both flags count only in a subscription; `SubOpts.sendsPartial_of_asksPartial` and `SubOpts.partial_of_unsubscribe` prove both.
- `checkExtensionsOrder` checks that only the first RPC of a stream carries extensions; the router does not call it.
  Two extensions within one RPC are not seen there, since the decoder keeps the last one.

The sources leave these points open.

- The consensus layer fixes the protocol ID `/meshsub/1.1.0`, while the extension belongs to `/meshsub/1.3.0`, and no fork document changes the ID.
  EthLib adds the wire fields only.
- The partial columns document says that a peer sets "the `partial` field" of a subscription, while the schema names two fields, `requestsPartial` and `supportsSendingPartial`.
- The partial messages document is a working draft, and gossipsub v1.3 a candidate recommendation.
  The partial columns document cites the extension through a pull request, not a pinned file.

### The gossipsub caches

`MessageCache` and `SeenCache` (`Networking/Gossip/Cache.lean`) are the two caches of [gossipsub v1.0, "Message Cache"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#message-cache).
The message cache keeps history windows, the newest first, with `put`, `get`, `gossipIds` and `shift`, one per operation of the source.
`shift len` starts a new window and keeps at most `len` windows.
So a message put into the current window stays for `len` heartbeats, and `gossipIds gossip` reads at most the newest `gossip` windows.
`get_shift_iterate` and `gossipIds_shift_iterate` (`Networking/Proofs/Gossip/Cache.lean`) prove these lifetimes for a history of at least one window.
The second one also needs an ID that the cache did not hold before the put.
`gossipIds_subset_get` proves that every ID told of in gossip is found by `get`.
It needs no bound between the two window counts, since gossip reads only the newest of the windows that `get` searches.
The seen cache keeps each ID with the time in milliseconds when it was inserted.
`contains`, `insert` and `expire` read, add and remove entries for a lifetime in milliseconds.
The consensus layer sets `seen_ttl` in seconds (`gossipsubParameters`), so a caller passes it times 1000 as the lifetime.

The source calls the seen cache "a timed least-recently-used cache", and does not say whether a lookup refreshes the time of an entry.
Here an entry keeps the time when it was inserted, and a lookup changes nothing.
The source gives no bound on the size of either cache, so none is modelled.
The caches take the 20-byte message IDs of the consensus layer, where gossipsub allows any bytes.
`MessageId.toBytes` and `MessageId.ofBytes?` convert between these IDs and the bytes of IHAVE and IWANT, and `ofBytes?_toBytes` and `toBytes_of_ofBytes?` prove that they are inverse.

### The gossipsub router on a received RPC

`receiveRpc` (`Networking/Gossip/Router.lean`) is what a router does with one RPC from a peer, after [gossipsub v1.0, "Message Processing"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#message-processing) and the rules of [gossipsub v1.1](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md).
It is a pure function of the router state, the time in milliseconds and its inputs.
The standing of each peer is an input: four flags, for the zero, gossip, publish and graylist thresholds of v1.1, that the client computes.
The consensus layer fixes no score, so a client without scoring passes every flag false.
The message ID and the validation are inputs too; the consensus layer provides both.
The caller also passes two durations that v1.1 leaves open: the extension of a backoff after an early GRAFT, and the backoff of a PRUNE that carries none.
So every theorem in `Networking/Proofs/Gossip/Router.lean` holds for every standing, message ID, validation and duration.
The export `gossip_receive_rpc` fixes the message ID, and the form of the standing and the validation.
It computes every message ID by the rule of one named fork, so it fits a router whose topics all carry digests of forks with one rule: Phase 0 alone, or forks from Altair on.
It takes the standing and the validation as tables: a peer missing from the standing has every flag false, and a message whose ID is missing from the validation is ignored.
The theorems state these properties.

- Only a message of the RPC, on a joined topic, unseen before the RPC and accepted, is forwarded or delivered.
- A peer joins a mesh only by a GRAFT for a joined topic, when it is not explicit, its backoff has ended, and the outbound quota allows it.
- So a peer within its backoff never joins a mesh.
- Every IWANT goes to the sender, for unseen IDs that an IHAVE on a joined topic named.
- A peer below the gossip threshold that is not explicit gets no IWANT and no IWANT answer.
- A GRAFT from an explicit peer, or within the backoff for a joined topic, gets a PRUNE.
- No explicit peer enters a mesh.
- An IWANT is answered only with messages that it named and that the message cache holds after the RPC.
- A graylisted peer that is not explicit changes nothing.
- A GRAFT for a joined topic within the backoff of its sender puts the sender out of the mesh.
  This holds for a sender that is neither explicit nor graylisted.
- No RPC removes an entry of the seen cache.
- A forwarded or delivered message has its ID in the seen cache, with the time of the RPC.
- So after a message is forwarded or delivered, no later RPC forwards or delivers its ID.
  This holds within the lifetime of the seen cache, whatever RPCs come between, with any parameters, standing and validation.
  The first and the last RPC use the same parameters and the same message ID function.
  No theorem covers two messages with the same ID in one RPC: a lifetime of zero lets both through.

The sources leave these points open, and the router takes one reading of each.

- v1.1 ignores a GRAFT for "unknown topics", while v1.0 answers a topic the router left with a PRUNE.
  Here an unknown topic is one the router has not joined, and the GRAFT gets no answer; it could also mean a topic that no peer announced.
- A message on a topic the router has not joined is dropped before the seen cache, so it is neither delivered nor forwarded.
  An IHAVE for such a topic is ignored too, so that no IWANT asks for a message that would be dropped.
  A PRUNE for such a topic is ignored, so that PRUNEs for arbitrary topics cannot grow the backoff table.
  The cost is that a router that rejoins a topic within such a backoff may GRAFT that peer too early.
- A GRAFT from an explicit peer gets a PRUNE whatever its topic, since v1.1 rejects it with a PRUNE.
- A GRAFT within the backoff also removes its sender from the mesh, since v1.1 prunes it at once.
- A message goes to every peer in the mesh, the sender included, as v1.0 says.
- v1.0 does not forward a message that the router published itself.
  Under `StrictNoSign` a message names no sender, so the router knows its own messages only by the seen cache, which a publish must fill.
- The ID of a message that fails validation stays in the seen cache.
- A GRAFT declined under the outbound quota gets no answer.
- v1.1 says to extend the backoff on an early GRAFT, with no amount, so the caller passes it.
- A received PRUNE without a backoff sets the backoff that the caller passes; v1.1 recommends one minute for `PruneBackoff`.
- A received PRUNE never shortens a backoff, and the peers it offers are not recorded: connecting to them is a client choice.
- The PRUNE that answers an early GRAFT carries the whole seconds that remain of the backoff, rounded up, and the PRUNE to an explicit peer carries none; neither offers peers.
- v1.1 ignores "gossip" from a peer below the gossip threshold; here that is both IHAVE and IWANT, and never from an explicit peer.
- IDONTWANT, from gossipsub v1.2, is ignored.
- A message goes to the mesh, then to the explicit peers; `receiveRpc_explicit` keeps the two lists from overlapping, and no theorem rules out a repeated peer within one list.
- The v1.1 limits on IWANT answers and on IHAVE messages per heartbeat fix no count, so none is modelled.
- The `peers.floodsub` set of v1.0 is left out: the consensus layer fixes `/meshsub/1.1.0` and names no floodsub peer.
- A message ID that is not 20 bytes is never requested and never answered, since no consensus message has one.

### The gossipsub heartbeat, topic membership and publishing

`join`, `leave`, `publish` and `heartbeat` (`Networking/Gossip/Router.lean`) follow [gossipsub v1.0, "Topic Membership"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#topic-membership), the list on publishing at the end of ["Message Processing"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#message-processing), and ["Heartbeat"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#heartbeat).
They add these rules of gossipsub v1.1: ["Heartbeat Maintenance"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#heartbeat-maintenance), ["Outbound Mesh Quotas"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#outbound-mesh-quotas), ["Adaptive Gossip Dissemination"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#adaptive-gossip-dissemination) and ["Flood Publishing"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#flood-publishing).
Each is a pure function of the parameters, the router state, the time, its topic or message, and the choices of the client.

The client choices are arguments, so every theorem holds for each choice that meets its hypotheses.

- The choice among candidate peers, which gossipsub makes at random, is a function of a count and the candidates.
  The theorems that need it ask for a lawful one: a sublist of the candidates, of the count or of all of them.
- The order of the peers by score, which v1.1 uses to keep the best peers of a pruned mesh.
- The standing of each peer, as for a received RPC.
- The values that v1.1 leaves open and the consensus layer does not fix.
  They are `D_score`, `D_out`, the gossip factor and its rounding, flood publishing, and the backoffs of a pruned mesh and of an unsubscribe.

`ClientChoices.Valid` states the bounds of v1.1 on `D_out`: `D_out < D_low` and `2 · D_out ≤ D`.
It adds a gossip factor in `[0, 1]` and positive backoffs, since a PRUNE with no backoff asks its receiver for the default.
No theorem assumes it: each takes the bounds it needs as hypotheses.

The theorems in `Networking/Proofs/Gossip/Heartbeat.lean` state these properties.

- After a heartbeat, every mesh has at most `D_high + D_out` peers, at most `D_high` of them not outbound, and none twice.
  The two bounds need `D ≤ D_high`, as the consensus layer sets it.
- A mesh of a joined topic below `D_low`, once its negative peers leave, fills up to `D`, or takes every peer that it may GRAFT.
- A mesh of a joined topic between `D_low` and `D_high`, once its negative peers leave, keeps those peers in their order.
  It takes only outbound peers that it may GRAFT, until it holds `D_out` outbound peers or runs out of them.
  So a mesh at `D_low` takes no peer to reach `D`, and one that holds at least `D_out` outbound peers is unchanged.
- No mesh holds a peer with a negative score.
- A mesh of a joined topic pruned for oversubscription keeps `D_out` outbound peers, or all the outbound peers it held once its negative peers left.
  This needs `D ≤ D_high` and `D_out ≤ D`.
- Every peer added to a mesh gets a GRAFT.
- Every peer removed from the mesh of a joined topic gets a PRUNE with the backoff of a pruned mesh.
  The backoff of this node for that peer then ends no earlier than that backoff from now.
- No IHAVE goes to a peer below the gossip threshold, or in the mesh or fanout of its topic after the heartbeat.
- When the gossip windows of a topic hold message IDs, the gossip of any state reaches `max D_lazy (share of the candidates)` of them, or all of them when there are fewer.
  The heartbeat sends that gossip for the state after the mesh and fanout are maintained.
- A fanout topic not published to for more than `fanout_ttl` is gone.

The theorems in `Networking/Proofs/Gossip/Membership.lean` cover joining, leaving and publishing.
Joining a topic not yet joined sends one GRAFT per peer of the new mesh.
With a lawful choice, that mesh has at most `D` peers, each one that the node could GRAFT before.
Leaving sends a PRUNE with the unsubscribe backoff to each mesh peer, and sets that backoff on this node.
A published message goes only to explicit peers and to peers not below the publish threshold.
With flood publishing, a message not in the seen cache goes to every such peer of the mesh and of the topic.
`publish_receiveRpc` proves that a message this node published is not forwarded or delivered again within the lifetime of the seen cache.
It holds when only received RPCs come after the publish, and the last of them uses the parameters and the message ID function of the publish.

The exports `gossip_join`, `gossip_leave`, `gossip_publish` and `gossip_heartbeat` fix the choice among candidates to the first ones, in candidate order.
`Select.first_lawful` proves that this choice is lawful.
So the theorems hold for the exports, under the hypotheses that each states on the parameters.
The exports take the order of the peers as a list, the best first, with every unlisted peer after them.
A pruned mesh keeps its `D_score` best-ranked peers, then the first other peers in mesh order.
The exports reject client choices outside `ClientChoices.Valid`.
`gossip_publish` computes the message ID by the rule of one named fork, as `gossip_receive_rpc` does.

The sources leave these points open, and EthLib takes one reading of each.

- The rounding of the gossip factor times the number of candidates is a client choice.
  The gossip share counts the peers of the topic outside its mesh and fanout that are neither explicit nor below the gossip threshold.
- Outbound grafts may take a mesh past `D_high`.
  So `heartbeat_mesh_le` bounds a mesh by `D_high + D_out`, and `heartbeat_mesh_le_inbound` bounds its peers that are not outbound by `D_high`.
- Opportunistic grafting, a "may" of v1.1 with a count that the application sets, is left out.
- Joining again within the backoff of a leave is allowed: the peers still in backoff are skipped, so the mesh may be smaller.
  v1.1 says only that the backoff "should be finished" first.
- The mesh steps run in order: negative peers leave, then the low bound, the high bound, and the outbound quota.
  When pruning keeps too few outbound peers, the last kept peers that are not outbound give way to the best-ranked outbound peers left out.
- The heartbeat drops the meshes of topics not joined, with no PRUNE.
- Peers below the publish threshold leave the fanout, and fanout top-ups take neither them nor explicit peers.
- A published message goes to every explicit peer, whatever its topics, and is not published again while its ID is in the seen cache.
- The heartbeat drops the expired entries of the seen cache and keeps ended backoffs, which are read by time.
- PRUNEs that this node sends offer no peers.

### The streams of an mplex connection

`step`, `receive` and `send` (`Networking/Libp2p/MplexSession.lean`) check each mplex frame against the streams of one side.
`run` checks a list of frames in turn.
They follow [mplex, "Protocol"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/mplex/README.md#protocol).
A stream is known by its ID and by whether this side opened it, since "Both parties can open a substream with the same ID".
The flag of a frame says whether its writer opened the stream, so a received Initiator flag names a stream that the peer opened.
A close closes the stream for its writer, and a reset closes both directions.
A side's writes after its own close or reset, or after a reset it received, are refused as "a protocol violation".
`step_find?_of_ne` (`Networking/Proofs/Libp2p/MplexSession.lean`) proves that an accepted frame changes the state of its own stream only.
`run_receive_writeAfterClose` proves that once the peer has closed or reset a stream, this side refuses its later data on it.

The source leaves three cases open.
A NewStream on an ID and opener already in the table is `reusedId`: the source says only that reusing an ID after a close "may result in undefined behaviour".
A frame on a stream not in the table is `unknownStream`, and the source fixes no reaction.
A second close or a second reset by one side gets no error of its own, and is refused as a write after a close or a reset.
A closed or reset stream stays in the table, so a later NewStream with its ID and opener is `reusedId`.
Each side has its own close and its own reset, and a side may reset a stream after it closed it.
This side writes nothing after it has received a reset, but the peer's reset may cross one that this side sent.
Frames that the peer wrote before it learned of a reset by this side may also still arrive, so this side accepts and drops them until the peer closes or resets.
The export decodes every frame first, and the decoder refuses data over 1 MiB and data on a close or a reset.
So the table does not check them again.
The stream name of a NewStream is not read, since the source says that the protocol does not consider it.

### The streams of a yamux session

`step`, `receive` and `send` (`Networking/Libp2p/YamuxSession.lean`) check each yamux frame against the streams of one side, and `run` checks a list of frames in turn.
They follow [yamux, "Message Flow"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/yamux/README.md#message-flow), with the flags of ["Flag Field"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/yamux/README.md#flag-field) and the IDs of ["StreamID Field"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/yamux/README.md#streamid-field).
A Data or Window Update frame with SYN opens a stream with a new nonzero ID of its writer's parity: odd for the client, even for the server.
Data may follow SYN before the ACK, and the ACK must come from the side that did not open the stream.
The source says that this side "must then reply" with ACK to accept or RST to reject, so its frames on the stream carry one of them until it has sent ACK; any other is `missingAck`.
FIN closes the direction of its writer, and RST closes the stream at once.
Data spends the window of its direction, which starts at 256 KiB by ["Flow Control"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/yamux/README.md#flow-control), and a Window Update adds its length to the window of the other direction.
A Ping with SYN gets a Ping with ACK and the same value, and a Go Away from the peer marks the session.
`receive_ping` (`Networking/Proofs/Libp2p/YamuxSession.lean`) proves the reply to a Ping.
`run_parity` proves that every stream has a nonzero ID of its opener's parity.
`send_window` proves that the data sent on a stream is at most 256 KiB plus the deltas of the Window Updates received on it.
`closed_iff` proves that a stream is closed iff each side sent FIN on it and no frame on it carried RST.

The source leaves several cases open, and each refused one gets its own error.
Data beyond the window of the receiver is `windowExceeded`, though the source says only to track the window and names no reaction.
A frame from this side after either RST is `afterReset`, and so is a frame from the peer after its own RST, if this side has not reset the stream.
Frames that the peer wrote before it learned of a RST by this side may still arrive, so once this side has reset a stream, it accepts and drops every later frame of the peer on it without SYN, a RST included; a SYN on its ID is still `reusedId`.
Nonempty data or FIN after its writer's FIN is `afterFin`, since FIN says "the sender will send no further data"; a Window Update after FIN is accepted, since the other direction may still be open.
A second ACK is `unexpectedAck`, and so is an ACK from the side that opened the stream.
A frame without SYN on a stream not in the table is `unknownStream`, and a closed or reset stream stays in the table, so its ID cannot open a stream again.
A Data or Window Update frame on stream 0 is `sessionStream`, since the source reserves 0 for the session.
The source says that SYN "should" be set to open a stream; a frame without SYN on a new ID is refused as `unknownStream`, a stricter reading.
The windows are unbounded naturals, since the source fixes no maximum window.
A Ping with both SYN and ACK is answered like a Ping with SYN.
The source says only that Ping and Go Away "should" use stream 0, so they are read the same on any stream.
Neither side is stopped from opening streams after a Go Away, since the source fixes no rule.
The ACK backlog of 256 streams is a SHOULD under [yamux, "ACK backlog & backpressure"](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/yamux/README.md#ack-backlog--backpressure), and is left out.
The export decodes every frame first, so the table does not check the size of the data again.

### The block headers of the eth protocol

`checkHeaders` (`Execution/Network/Blocks.lean`) checks an answer to a GetBlockHeaders request of the eth protocol.
`checkHeaders_eq_ok_iff` (`Execution/Proofs/Network/Blocks.lean`) states the conditions under which an answer passes: it holds at most as many headers as asked, its first header is the start block, and each header follows the one before it.
`followsIn_eq_ok_iff` states that one header follows another exactly when it has the next number of the request and, when the request skips no block, the later block names the earlier one by its hash.
`headerParent_of_checkHeaders` draws the consequence for a whole answer to a request that skips no block.
No theorem checks a header against the chain or its validity rules.

### The block bodies of the eth protocol

A node fetches the bodies of blocks after their headers, with the BlockBodies message of the eth protocol.
`checkBody` (`Execution/Network/Bodies.lean`) checks such a body against the header that the node asked it for.
It follows "Block Encoding and Validity" in [`caps/eth.md`](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#block-encoding-and-validity).
The body must be the list of the transactions and the ommers, with the withdrawals from Shapella.
The transactions and the withdrawals must have the roots of the header.
The ommers list must hold at most two items, and its Keccak-256 hash must be the ommers hash of the header.
No ommer may have a number above the block's.
A transaction sent as a byte string must start with a type below `0x80`, as EIP-2718 asks, so that it cannot stand for a legacy transaction.

`checkBody_complete` (`Execution/Proofs/Network/Bodies.lean`) proves that the body of every block that passes `stateTransition` passes this check.
So a correct node never rejects it.
`checkBody_binding` proves that two bodies that pass for one header are equal in each part, or that a Keccak-256 collision is named.
For the transactions and the withdrawals, the search of the trie binding returns the collision; for the ommers, the two encodings are the collision.
It reuses `indexedRoot_binding` and `withdrawalsRoot_binding` for the roots, and `encode_injective` for the ommers.
`checkBody_tooManyOmmers` and `checkBody_tooManyOmmers_shapella` show that a body with three ommers is rejected once the earlier checks pass.
No theorem bounds the probability of finding two bodies that pass for one header and differ.

The check leaves four rules of that section to other checks.
It does not check the header itself, which the header checks of the eth protocol decide before the body is asked for.
It does not run the transactions or look at the state, so it does not say that the transactions are valid for the block.
It does not check the ommer headers against the chain, which needs the recent blocks that `validateOmmers` reads.
It does not ask that the sum of the gas limits of the transactions is at most the gas limit of the block, as `caps/eth.md` says.
Block validity asks only that each transaction fits in the gas that the block still has, so the stricter rule would reject valid blocks.

### The receipts of the eth protocol

`receiptsMatch` (`Execution/Network/Receipts.lean`) checks the receipts of one block in a Receipts answer against the receipts root of its header.
It follows "Receipt Encoding and Validity" in [`caps/eth.md`](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#receipt-encoding-and-validity).
Each receipt is put back in its consensus form.
On eth/68 it keeps the Bloom filter that the peer sent; from eth/69 on the filter of its logs is computed again.
The trie root of the list must be the root of the header.

`receiptsMatch_eq_true_iff` (`Execution/Proofs/Network/Receipts.lean`) states when the receipts of a block pass.
Each receipt reads as a receipt in consensus form, the one at its position in the list.
The receipts root of those forms, in the order of the list, is the root that the caller gives.
`consensusOfItem_eth68_eq_ok_iff` states how a receipt reads on eth/68.
A list reads as a legacy receipt, of type 0, and a byte string as a receipt whose type is not 0.
So a legacy receipt sent as a byte string does not read.
`consensusOfItem_eq_ok_iff` states that from eth/69 on a receipt reads as the list of [EIP-7642](https://eips.ethereum.org/EIPS/eip-7642#receipts-message-changes), with the Bloom filter of its logs computed again.
From eth/69 on, the reader does not check the type of a receipt against the fork; only the root comparison rejects a wrong type.

The caller gives the receipts root, the fork of the block and the eth version, and the check trusts them.

### The block access lists and the cells of the eth protocol

`accessListsResponse` (`Execution/Network/Message.lean`) checks a BlockAccessLists answer of eth/71 against the access list hashes of the requested blocks.
It follows "BlockAccessLists (0x13)" in [`caps/eth.md`](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#blockaccesslists-0x13).
`accessListsResponse_eq_true_iff` (`Execution/Proofs/Network/Message.lean`) states when an answer passes: it repeats the request ID and has one entry for each hash that the caller gives.
Each entry is the RLP empty string, or its RLP encoding has that hash under Keccak-256.
`accessListsAnswer_eq_true_iff` (`Execution/Proofs/Network/Snap.lean`) states the check of the entries alone, which snap/2 shares.
There the peer may cut the list short, so that check asks only for no more entries than hashes.
The caller gives the access list hash of each requested block, in the order of the request.
The check trusts these hashes: it reads neither the block hashes of the request nor their number.

`trieNodesAnswer` (`Execution/Network/Snap.lean`) checks a TrieNodes answer of snap/1 against the paths of its GetTrieNodes request, after "GetTrieNodes (0x06)" in [`caps/snap.md` at `a1d196b`](https://github.com/ethereum/devp2p/blob/a1d196b39a9ed2d16e623e1d7a2ba9f3d77ae08f/caps/snap.md#gettrienodes-0x06).
Each list of paths names one account node, or nodes of the storage trie of the account at its first path.
A path of 32 bytes is a full path, and a shorter one a compact partial path; `readPath_full` and `readPath_compact` (`Execution/Proofs/Network/Snap.lean`) state both readings.
The check asks only for no more nodes than the request names, so an empty answer, the reply of a peer without the state, passes.
`nodeCount_readGroup` counts one node per path after the first, and one for a list of one path, and `trieNodesAnswer_take` states that each prefix of an accepted answer is accepted.
The nodes are requested by path, not by hash, so the check reads no node: a requester can check a node only once it holds the parent, and the source fixes no such check.
The source leaves these points open, and the check takes one reading of each.

- A partial path of 62 or 63 nibbles has a compact encoding of 32 bytes, which the rule "<32 bytes" does not cover; it reads here as a full path.
- The source names the compact encoding, not the meaning of its leaf flag, so the flag is dropped.
- A path of more than 32 bytes is an error.
- An empty list of paths is an error, since it names no account.
- The account path of a storage group may be partial; the source groups the paths by account and does not say that this path is full.
- An empty path is an error, since it is no compact encoding; the root of a trie has the compact path `0x00`.

`checkCellsResponse_eq_ok_iff` (`Execution/Proofs/Network/Message.lean`) states that a Cells answer of eth/72 passes exactly when it repeats the request ID and its cells pass `checkCells` (`Execution/Network/Cells.lean`).
That check follows "Cells (0x15)" in [`caps/eth.md`](https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#cells-0x15).
`checkCells_eq_ok_iff` (`Execution/Proofs/Network/Cells.lean`) states the rules of those cells.
The caller gives the number of blobs of each transaction, and the check trusts it.

`CellMask.has_eq_true_iff` states which index a bitmap marks: index `i` exactly when `i < 128` and bit `i % 8` of byte `i / 8` is set, counting from the least significant bit.
"Cells (0x15)" fixes no bit order, and the check reads the bitmaps only through the subset rule and the count.
`CellMask.subset_eq_true_iff` states the subset rule in those marks: one bitmap is a subset of another exactly when the other marks each index that it marks.
`CellMask.count_eq_sum` states that the count of a bitmap, the `popcount` of "Cells (0x15)", is the number of set bits of its 16 bytes.
`CellMask.count_le_count_of_subset` states that a subset counts no more indices than the bitmap that holds it.
Together, `checkCells_eq_ok_iff` and `CellMask.count_le_count_of_subset` give that a response that passes has no more cells for each blob than the request asks for.
No export calls the cells check, so no test of the bindings runs it.

### Fork digests

A peer names the fork of a response chunk, and of a gossip topic, by a fork digest of four bytes.
`forkOfDigest` (`Consensus/ForkDigest.lean`) finds an epoch with the digest, and the receiver takes the fork at it.
It searches the epochs at which the digest can change.
These are epoch 0, the first epoch of each consensus fork, and, from Fulu, the first epoch of each blob schedule entry.

`computeForkDigest_digestStart` and `Config.forkAtEpoch_digestStart` (`Consensus/Proofs/ForkDigest.lean`) state that the digest and the fork at each epoch are those at the latest of these epochs at or before it.
`forkOfDigest_sound` states that an epoch that the search finds has the digest, with no hypothesis.
`forkOfDigest_recovers` states that the search reads back the fork at which a digest was computed, at every epoch.
It needs `digestsIdentify`, a check of the chain's configuration and genesis validators root.
A digest is four bytes of a hash, so two forks of one chain could share one, and nothing rules this out in general.
`digestsIdentify_sharedVersion` shows that the hypothesis is needed: on mainnet with Altair given the version of genesis, the check fails.
There `forkOfDigest_sharedVersion_altair` shows that the search reads Phase 0 from the digest of Altair.
The check depends only on the configuration and the genesis validators root, so a chain runs it once.
It reads at most nine epochs, plus one for each entry of the blob schedule.
It also reads the epoch of a fork left at the far future, which no message carries, so it can ask more than recovery needs.
`bindings/python/tests/consensus/test_fork_digest.py` runs it on mainnet, Sepolia and Hoodi, with their configurations and genesis validators roots from pinned sources, and it holds on each.
There the digest in a bootnode record of each chain reads back the fork that the record's next fork version implies.
On mainnet the check reads the root from the pinned genesis state, so it runs only with the archives.
`decodeResponseChunk_forkOfDigest` (`Consensus/Proofs/ReqResp/ResponseBounds.lean`) draws the consequence for req/resp: on a chain that passes the check, the receiver reads a chunk at the type of the sender's fork.

### Weak subjectivity

A node that starts from a recent checkpoint trusts it only for a limited time, the weak subjectivity period.
`Consensus/WeakSubjectivity.lean` computes the period with the rule of each fork: Phase 0 counts validators, Electra the churn of the balance, and Gloas three weighted churns.
The theorems in `Consensus/Proofs/WeakSubjectivity.lean` say what the 64-bit computation returns.

From Electra, `balanceChurnPeriod_eq_ok_iff` gives the period in closed form, the withdrawal delay plus `10 t / (200 c)` epochs for a total active balance `t` and a churn `c`.
It succeeds exactly when no product or sum reaches `2^64` and the churn is not zero.
In Phase 0, `phase0PeriodEpochs_eq_ok` shows that a computed period is one of the two expressions of the rule, on natural numbers.
`min_le_computeWeakSubjectivityPeriod` shows that, at every fork, the period is at least the withdrawal delay.

`computeWeakSubjectivityPeriodElectra_le` bounds the Electra period by a function of the parameters alone.
It assumes a positive churn quotient, and a minimum churn that is a positive whole number of increments.
At the mainnet parameters, `computeWeakSubjectivityPeriodElectra_le_mainnet` gives at most 3558 epochs, for every state.
`gloasWeightedChurn_eq_ok_iff` gives the Gloas weighted churn in closed form when its three churns and sums stay below `2^64`.
`computeWeakSubjectivityPeriodGloas_le` bounds the Gloas period by a function of the parameters alone when the activation floor covers the rounding losses.
At the mainnet parameters, `computeWeakSubjectivityPeriodGloas_le_mainnet` gives at most 1658 epochs, and a Python test reaches that bound.
Its state is not one that a chain can reach: one validator holds about 1.4 billion ether.
`computeWeakSubjectivityPeriodPhase0_le` bounds the Phase 0 period by the withdrawal delay plus the longer of two terms, `160 N / (600 delta)` and `230 N / (600 Delta)`.
Here `N` is the number of active validators, `delta` the churn of validators in one epoch and `Delta` the deposits that fit in one epoch.
The bound needs no condition beyond success of the computation.
It depends on the state through `N` and `delta`, so it gives no number for the parameters alone.

`isWithinWeakSubjectivityPeriod_eq_ok_iff` states when the check of a checkpoint succeeds and what it answers.
The state must hold the root of the checkpoint at its epoch and be at that epoch.
The answer is then whether the current epoch is at most the epoch of the checkpoint plus the period.
By `isWithinWeakSubjectivityPeriod_of_slot_le`, a checkpoint within its period at some slot is within it at every earlier slot.

From Electra, `accountable_safety_of_weakSubjectivityPeriod` (`Consensus/Proofs/Transition/WeakSubjectivitySafety.lean`) relates the period to the safety margin that the rule intends, under an assumption on the change of the validator sets.
The trusted set is the active validators of the state at the checkpoint, weighed by their effective balances, with at least one increment of stake.
Take two conflicting finalized checkpoints of the Casper FFG model.
The change of a set since the trusted set counts the stake that joined plus twice the stake that left.
Assume that the change of each justified set between their epochs is at most `3 c` for each of the `n` epochs of churn, the period less the withdrawal delay, with `c` the churn of the period.
Then the slashable validators hold at least `1/3 - SAFETY_DECAY/100` of the trusted stake, `7/30` with `SAFETY_DECAY` at 10.
The arithmetic is `safetyMargin_of_balanceChurnPeriod_eq_ok`, from `200 n c ≤ SAFETY_DECAY · t`.
In Electra an epoch adds at most the activation-exit churn `a ≤ c` and removes at most `c`, consolidation sources included, so its change is at most `a + 2 c ≤ 3 c`.
From Gloas an epoch changes the set by at most three times the weighted churn, plus 4 Gwei of rounding when the consolidation churn is zero.
The queues carry unused churn to later epochs, so the bound can hold over the window without holding in each epoch.
No theorem yet derives it from the state transition, and the model fixes the effective balances over the window.
The rule spends the withdrawal delay on keeping exits slashable and the other epochs of the period on churn, and the assumption takes the change over those epochs as given.
Activations have no such delay, and a validator outside the registry of the checkpoint weighs zero in the model.
The beacon chain weighs the votes of each epoch at the effective balances of that epoch.
Top-ups, the balance that a consolidation moves to its target, rewards and penalties all change those balances during the window.
The theorems weigh every vote at the balances of the checkpoint, so they reach a chain only once those changes are bounded, and no theorem bounds them yet.

`Consensus/Proofs/ChurnReservations.lean` bounds the balance that the churn updates of exits and consolidations reserve, from Electra, when they run in turn on one state.
These updates keep the slot and the validators, so the churn stays fixed.
Their sum fits the churn left at the start plus one full churn for each later epoch of the queue.
The bounds also hold for an idle queue, whose earliest open epoch is before the first permitted epoch.
The exact equalities require the first permitted epoch to be no later than the earliest open epoch at the start.
In a block, other writes to the registry and to the pending queues come between these updates, and these theorems do not cover that interleaving.

`departure_charges_le_window` (`Consensus/Proofs/DirectSafety/DepartureQueue.lean`) covers it for the exits of a run, before Gloas.
It takes a run from genesis to a state `x`, and a run on from `x` to a state before Gloas.
The charge of a validator is its effective balance, counted when a step of the second run first assigns its exit epoch.
The charges whose exit epoch is at most `high + 1` fit the unspent capacity of the exit and consolidation queues at `x`, plus one cap for each epoch from the epoch of `x` to `high + 1`.
The cap is `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` plus `consolidationCap`.
If `x` is before Electra, there is no carry, and the cap also adds the churn of validators for a bound on the size of the registry, at least 1, times `MAX_EFFECTIVE_BALANCE`.
`consolidationCap` is an assumption: it bounds the consolidation churn of the state where each step of the second run starts, from Electra.
That churn follows the total active balance, so the assumption keeps the bound close to the churn that the chain actually has.
The theorem also assumes that the preset orders its caps, `MAX_EFFECTIVE_BALANCE` at most `MIN_ACTIVATION_BALANCE` at most `MAX_EFFECTIVE_BALANCE_ELECTRA`; `CapOrder.mainnet` and `CapOrder.minimal` show that both presets do.
The bound counts exits at their assigned exit epochs, so it does not bound the exits that the blocks of one epoch initiate.
It does not bound activations, and no theorem yet derives the change of the active set or puts this bound into `accountable_safety_of_change`.

`departure_charges_le_funded_window` (`Consensus/Proofs/DirectSafety/IntervalBounds.lean`) derives `consolidationCap` instead of assuming it.
It applies `departure_charges_le_window` with a cap computed from the funded window, a bound on the active balance.
A window that ends before `ELECTRA_FORK_EPOCH` reads `departure_charges_le_window_before_fork` instead.
The funded window starts from the funded stake at `x`.
That stake counts the larger of the effective and the actual balance of each validator that is active, not yet active, or the source of a pending consolidation.
The window adds the deposit balance left to consume at `x` and `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` for each epoch of the window.
It also adds the credits that the second run records.
The window bounds the active balance at the state where each step of the second run starts, from Electra.
So the derived cap is at least the consolidation churn of each of those states.
It assumes that the second run ends at an epoch of at most `high + 1`, and that `tail.balanceEvents high` replays the balance events of the run.
`Run.balanceEvents_ok` shows that this replay succeeds for every run that ends before Gloas, so the second assumption always holds for some events.
The first assumption is a real restriction: no theorem yet cuts a longer run at `high + 1`, so for such a run `departure_charges_le_window` with its assumed cap is still the bound.
These events record each change of balance with the limit that the transition computes for it.
The recorded credits are the rewards, including those of proposers, whistleblowers and sync committees, and the deposits that the deposit churn does not limit.
Those are the deposits before Electra and, from Electra, the deposits to withdrawn sources of pending consolidations.
They raise the bound, so it is only as tight as the credits of the run.
The theorem charges `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` and the consolidation rate only if the window reaches `ELECTRA_FORK_EPOCH`, so it also covers a window that crosses the fork.
With a withdrawal delay below two epochs, the theorem uses the registry window times `MAX_EFFECTIVE_BALANCE_ELECTRA` instead.
The mainnet delay of 256 epochs never reaches that case.
The theorem also assumes the order of the caps and that the divisors of the preset are positive.
`Preset.divisorsPositive_mainnet` and `Preset.divisorsPositive_minimal` show the second for both presets.

From Phase 0 to Deneb, `accountable_safety_of_weakSubjectivityPeriod_of_lt_electra` covers the period in part.
The rule counts `N` active validators of average balance `t` ether, rounded down, a largest effective balance `T` ether, a churn of `delta` validators and `Delta` top-ups per epoch.
The theorem assumes each justified set gains and loses at most `delta` validators for each of the `n` epochs of churn, with `delta` the churn at the checkpoint.
It also assumes every effective balance at most `T`, with `T` a whole number of ether.
With large balances, `230 T < 320 t`, the rule's epochs for churn always satisfy `20 n delta T ≤ N t`, and so keep the margin.
`churn_le_of_phase0PeriodEpochs_eq_ok` gives that inequality for the epochs of the rule.
The rule takes the longer of those and its epochs for top-ups, so the theorem also assumes that the epochs for top-ups satisfy the same inequality.
Top-ups change a balance, which the model leaves out, and in the model a longer period only allows more churn.
The rule does not imply that hypothesis: with `N = 2^23` validators of 32 ether, `delta = 128` and `Delta = 512`, the rule takes 6280 epochs for top-ups, while the churn allows 3276.
Over 6280 epochs, the churn of validators alone lowers the bound of Gasper Theorem 8.3 to about 14% of the stake.
With small balances, `230 T ≥ 320 t`, no theorem relates the period to the margin.
The Python suite checks the periods against the three tables of the rule, except for the rows whose states take minutes to build.

### Inactivity leak

`Consensus/Proofs/Transition/InactivityLeakBound.lean` bounds the number of epochs after which a leak brings the effective balance of an absent validator to a threshold.
`InactivityLeakStake.lean` deduces that the voters then hold two thirds of the active stake.
Both take the balance, the score and the effective balance of each epoch as given sequences.

`InactivityLeakEpoch.lean` proves one link of that derivation: the leak lasts from one slot or epoch transition to the next, unless finality advances.
In an epoch transition from a leaking state, the state that justification returns still leaks, unless the finalized epoch rises (`processEpoch_finalized_lt_or_isInInactivityLeak`).
The steps after justification read the leak test on that state, or on a later one with the same slot and finalized checkpoint.
One slot from a leaking state ends in a leaking state, unless the finalized epoch rises (`advanceSlot_finalized_lt_or_isInInactivityLeak`).
`BalanceNotRaised.lean` proves the epoch part of that condition, from Altair (`balanceNotRaised_processEpochAltair`).
From the rewards up to the update of the effective balances, the balance of a validator does not rise.
This holds when no pending deposit carries its key and no pending consolidation targets it.
`BalanceNotRaisedBlock.lean` proves the part of the blocks, at every fork (`balanceNotRaised_processBlock`).
A block raises no balance of a validator that has a balance and is not its proposer.
From Altair the validator must sign no sync aggregate, and no deposit of the block may carry its key.
It needs more than `MIN_SEED_LOOKAHEAD + 2` epochs of RANDAO mixes.
`InactivityLeakRun.lean` derives those sequences for one validator from a run of the chain, from Altair, and so discharges the hypotheses of the bound (`effectiveBalance_le_of_leakRun`).
The run is a series of slots that end an epoch, each followed by slots and blocks that credit nothing to the validator.
It assumes that every epoch leaks, that the largest effective balance of the validator stays fixed, and that the validator is eligible and misses the target while above the threshold.
`twoThirds_of_leakRun` applies that run to each absent validator.
Either some epoch of the run does not leak or raises the finalized epoch, or the voters hold two thirds of the active stake at the end.
The first case is the expected one on mainnet when the voters vote: they should reach two thirds before the bound, and finality should resume; no theorem shows this.
It reads the balance of the voters in the final state.
No theorem yet bounds that balance from below by the one at the start of the run.

### Fast confirmation rule

`Consensus/ForkChoice/FastConfirmation.lean` holds the fast confirmation rule of [arXiv 2405.00549v4](https://arxiv.org/abs/2405.00549v4).
The rule weighs the committees of a range of slots exactly.
Each active member of their union counts once, by its effective balance in the source of balances, and a range with a whole epoch weighs the total active balance.
An earlier form of the rule estimated that weight as an average per slot, which is not an upper bound on a given committee.
[A counterexample on #1458](https://github.com/ethereum/EthLib/issues/1458#issuecomment-6764027413) shows that the estimate lets the rule confirm a block that an attack then reorgs, under the assumptions of the paper.
The pinned fast confirmation vectors of consensus-specs `v1.7.0-beta.4` were generated with that estimate.
In 24 of them, five cases at several forks, the rule now confirms another block, and `tests/parity/disagreements.toml` lists them as expected failures.
The vendored fast confirmation cases in `tests/consensus/fork_choice` still pass.
From Gloas the discount for empty slots also counts the votes for the pending node of the parent, which the rule of consensus-specs `v1.7.0-beta.4` leaves out.
No pinned vector reaches that case, so review alone checks it until the vectors move to a release with it.

`Consensus/Proofs/Models/ForkChoice/HonestSupport.lean` proves Lemmas 1, 3 and 4 of Appendix A.1 of the paper on sets of validators weighed by stake.
`lt_two_mul_honest_support_later` takes the honest ratio that Lemma 4 gives at one slot, and chains Lemmas 1 and 3 across slots.
The honest ratio that Lemma 4 gives at one slot yields honest support above half the threshold at a later slot.
It assumes that the later threshold grows at most in proportion to the stake of the committees.
It also assumes that every honest supporter at the first slot still supports the block, that every honest validator that joins the committees supports it, and Assumption 2 for the later committees.
Both slots weigh validators by the same stake.
`lt_two_mul_honest_support_later_of_add` covers thresholds that add an amount to the stake of the committees, with committees that only grow and an amount that never grows.
For the rule that amount is the boost less the discount, so it does not cover a discount larger than the boost.
No theorem yet takes these sets and stakes from the stores of an execution, or shows that the amount of the rule never grows.

`stake_le_computeCommitteeWeightBetweenSlots` (`Consensus/Proofs/ForkChoice/FastConfirmationIndicators.lean`) shows that the weight covers the stake of the active members of the committees.
`stake_le_computeCommitteeWeightBetweenSlots_of_covered` shows that the weight of a range with a whole epoch covers the stake of every validator active in the source of balances.
`lt_two_mul_honest_support_of_isOneConfirmed` then gives Lemmas 4 and 3 of the paper for a block that the store confirms.
Twice its honest support, plus the discount for empty slots, exceeds the committee weight since its parent plus the boost.
It takes any set `W` of validators whose stake the committee weight of the range covers.
It assumes that the Byzantine validators hold at most the configured share of the stake of `W`.
That is Assumption 2 of the paper when `W` is the set of active members of the committees of the range.
It also assumes that no validator the store knows to equivocate is honest.
It also assumes that the effective balances of those validators are whole numbers of 100 Gwei, since the store rounds the weight down to 100 Gwei for its share of the adversary.
`lt_two_mul_honest_supportersOf_of_isOneConfirmed` (`Consensus/Proofs/ForkChoice/FastConfirmationSets.lean`) builds the supporters, the equivocators and the committee members from the store, and their stakes are the store's numbers.
It replaces that assumption with an invariant of the state: each effective balance of the source of balances is a whole number of increments.
It also assumes that the increment of the preset is a whole number of 100 Gwei, as 10^9 Gwei is.
No theorem yet derives that from the state transition.
The update of effective balances keeps it, but the other steps and the upgrades have no proof.
It also assumes that each supporter of the block is a member of the committees of the range.
The store checks a vote against the committees in the state of its target, while the rule reads them in the state of the head.
In a store with a forward clock, `Store.ForwardReachable.votesHaveOrigins` gives each latest vote the facts of its attestation.
From those facts, `VoteOrigin.exists_mem_committee` (`Consensus/Proofs/ForkChoice/VoteOrigins.lean`) places the voter in a committee of the slot of its attestation, in the state of its target.
`mem_getCommitteesBetweenSlots` (`Consensus/Proofs/ForkChoice/FastConfirmation.lean`) places each member of a committee of a slot of the range, in the state of the head, among the members that the rule reads.
`Store.ForwardReachableWith.supportersOf_mem_committees` (`Consensus/Proofs/ForkChoice/FastConfirmationCommittees.lean`) proves the assumption for a range with part of an epoch, when the head descends from the block.
It needs a store built with a forward clock and one setting of the signature checks, as on an honest node.
Such a range ends at most one epoch after its start, so the vote of each supporter is at most one epoch after the block.
`Store.ForwardReachable.slot_le_of_blockState_of_getCurrentSlot` (`Consensus/Proofs/ForkChoice/BlockStates.lean`) puts each block state of a store with a forward clock at or before the current slot.
So the state of the head is at most one epoch after the vote.
`Store.ForwardReachableWith.committeesKept_of_voteOrigin` (`Consensus/Proofs/ForkChoice/CommitteeAgreement.lean`) then makes the state of the target and the state of the head agree on the count and the committees of the slot of the vote.
`Store.ForwardReachableWith.supportersOf_mem_committees` also needs an anchor block not after its state, the start of the range at or before the block, both lookaheads of the seed at least one epoch, and a ring of mixes longer than the minimum lookahead plus two epochs; both presets satisfy the last two.
`Store.ForwardReachableWith.lt_two_mul_honest_supportersOf_of_partialRange` is the corollary without the assumption.
The corollaries apply `lt_two_mul_honest_supportersOf_of_weighed`, which builds those sets for any `W` that holds the supporters and the active members of the committees, and whose stake the weight covers.
`lt_two_mul_honest_supportersOf_of_covered` drops that assumption when the range of the adversary holds a whole epoch.
Its set `W` is then every validator active in the source of balances, which holds each supporter.
Its Byzantine bound is Assumption 2 when every validator active in the source is a member of a committee of the range.
Otherwise it implies Assumption 2 when the validators that have left the committees are Byzantine, as Assumption 1 of the paper ensures.
With an honest one gone the two bounds are incomparable.
The tally of the source still counts the votes of validators that have left the committees, so the proof bounds their stake.
The paper assumes a static set of validators, Assumption 1.
`StaticPair` (`Consensus/Proofs/ForkChoice/StaticValidators.lean`) states the part of it that the proofs use.
It relates a reference state to each state that a store holds.
No effective balance is above that of the reference, and each honest validator is active and not slashed in both states, with one effective balance.
A Byzantine validator that is active and not slashed in the state is so in the reference too.
`Models.Network.Execution.Static` asks it of every block state and checkpoint state of each honest store.
No safety theorem takes it as a hypothesis yet.
Under it the honest supporters of a node weigh the same in any two states that a store holds, such as those of the head and of the rule.
The supporters of a node in such a state weigh at most its supporters in the reference.
Both results need the registries of the states to stay within the limit of the preset.
`StaticPair` does not cover the pulled-up state of the head, which the store does not hold, and it gives only an inclusion of the active Byzantine validators.
So the agreement of shufflings and the total active balance need more than it.
The honest support of the target of the current epoch takes the total active balance less the weight of the committees so far as the weight still to vote.
No theorem proves that, which rests on the shuffling of the head and its pulled-up state agreeing on the active validators of the epoch.
Each member of the committees must also be in the source of balances, or the rule fails; no theorem bounds the epochs between that source and the range.

`Execution.equivocatingIndices_honest` (`Consensus/Proofs/ForkChoice/HonestEquivocators.lean`) proves, for the store of each honest validator in an execution of the network model, that no known equivocator is honest.
It needs slots that last a positive time, and honest stores that start with no honest equivocator.
A store built from an anchor starts with none, by `Store.getForkchoiceStore_equivocatingIndices`.
In the model an honest validator signs a vote only after checking it against its own votes in its view.
Each of its votes in a sent message stays in its view, so no two of them can be slashed together.
`Execution.lt_two_mul_honest_supportersOf_of_isOneConfirmed` restates `Store.lt_two_mul_honest_supportersOf_of_isOneConfirmed` for such a store, without that assumption.

`Store.parentVotersOf` in `Consensus/Proofs/ForkChoice/FastConfirmationSets.lean` names the committee members whose recorded votes the discount for empty slots counts.
They are active and not slashed in the source of balances, are not known equivocators, and vote for the pending parent node or the parent payload node that the child builds on.
`exists_stake_parentVotersOf_of_computeEmptySlotSupportDiscount` shows that the discount is their stake less the adversarial weight of the empty slots, with subtraction truncated at zero.
If the parent sits at an earlier slot than the child, both counted nodes are ancestors of the pending child node, including from Gloas.
The ancestry needs only the two block reads and that local slot order, not `Reachable` or `ParentsBelow`.
`le_honest_parentVotersOf_of_computeEmptySlotSupportDiscount` shows that the discount takes off at most the honest stake of these voters.
It assumes Assumption 2 on the active members of the empty-slot committees, no honest known equivocator, aligned effective balances, and an increment divisible by 100 Gwei.
In an execution of the network model, `Execution.equivocatingIndices_honest` gives the assumption on known equivocators for the store of an honest validator.
These are store-local facts: no theorem here shows that a recorded honest vote is its voter's latest actual vote, or that it remains the recorded vote at a later store.

`Consensus/Proofs/ForkChoice/FastConfirmationIndicators.lean` also states the two FFG tests of the rule on the target of the current epoch.
`getCurrentTarget_eq_ok_iff` states that target as the checkpoint of the store's epoch in the chain of the head, and `epoch_eq_of_getCurrentTarget` gives its epoch.
`willCurrentTargetBeJustified_eq_ok_true_iff` states the two-thirds test, with both products checked for overflow.
`two_mul_le_three_mul_of_willCurrentTargetBeJustified` states the bound it gives on naturals: three times the honest support reaches twice the total active balance.
`willNoConflictingCheckpointBeJustified_eq_ok_true_iff` states the one-third test: it accepts a target that is the unrealized justified checkpoint, and otherwise asks that three times the honest support exceed the balance.
`willNoConflictingCheckpointBeJustified_of_willCurrentTargetBeJustified` shows that the one-third test passes wherever the two-thirds test does, for a nonzero effective balance increment.
No theorem relates either test to the justification of the target in a later state.

`Consensus/Proofs/ForkChoice/FastConfirmationConfirmedRoot.lean` states where the confirmed block of a slot comes from.
`Store.onFastConfirmation_confirmedRoot` shows that the rule starts from the block stored before, the finalized block or the observed justified block.
It keeps the block stored before only when that block is in the chain of the head, and at the first slot of an epoch only when `isConfirmedChainSafe` accepts it.
It takes the observed justified block only at the first slot of an epoch.
That block must then be in the epoch before the current one, and its checkpoint must be the unrealized justification of the head.
The rule stores that block, or a later root of the walk of `getAncestorRoots` from that block to the head.
That root and each root before it in the walk then pass `isOneConfirmed`, with the votes of the state of the observed justified checkpoint.
The rule makes two walks, and `Store.getAncestorRoots_of_append` in `Consensus/Proofs/ForkChoice/AncestorRoots.lean` shows that the second walk is the part of the first walk after the root where the first walk stopped.
No theorem yet shows that the roots of a walk are in the chain of the head.

These theorems prove no safety: no theorem yet shows that a start is safe, or that a one-confirmed walk keeps a block in the chain of every honest head.
They do not record every check of the rule.
For the start they leave out the other checks that compare the epochs and the slots of the blocks.
For the walks they leave out the checks on the epochs of the start and of the walked blocks.
They also leave out the check that the head of the slot before holds each block of the first walk.
They leave out the checks that a voting source or an unrealized justification is recent.
They also leave out the calls to `willNoConflictingCheckpointBeJustified` and `willCurrentTargetBeJustified`, whose tests `FastConfirmationIndicators.lean` states on their own.

`Store.blockShouldBeFinalized_eq_ok_iff` (`Consensus/Proofs/ForkChoice/FastConfirmation.lean`) states when a block is due for finality.
The next checkpoint is at the first epoch that starts at or after the slot of the block.
The block is due from the first slot two epochs after that one.
`Store.getRestartResilientConfirmedRoot_eq_ok_iff` states the confirmed block after a restart, when both blocks are stored and the current slot is known.
The rule takes the block confirmed before the restart exactly when three conditions hold.
That block is at a later slot than the confirmed block, is not yet due for finality, and is in the chain of the head.
Otherwise it keeps the confirmed block.
It fails when the test of finality overflows or the test of the chain fails.
The root confirmed before the restart and the head are inputs.
No theorem relates them to a block that an earlier store confirmed, or to the head that the fork choice finds, and the network model has no restart.

`Consensus/Proofs/ForkChoice/HonestConfirmations.lean` puts the store of the rule into the state of an honest validator of the network model.
An honest validator runs the rule at the start of a slot, at most once in each slot, with a store of the fork choice that is up to date with its view and whose clock is in that slot.
`ConfirmingMoves.fcr_eq_or` shows that every other move keeps the store of the rule and the slot of the last run.
`Execution.confirmingInduction` is the induction along an execution of that protocol, and `Store.onFastConfirmation_confirmedRoot` splits its case of a run into four cases.
`Execution.toForkChoice` gives, inside each such execution, an execution of the fork choice with the same views and stores.
Synchrony carries over to it, so the duty to vote and the theorems on executions of the fork choice apply to it.
The duty `Confirms` asks a run of the rule at the start of each slot of a set that is a parameter, and that each run succeeds.
A safety theorem would take a set that holds every slot from the stabilisation time of the model on, and so would cover only executions where the rule never fails at those slots.
The state of an honest validator at the start of an execution is free; a safety theorem would take the start `ConfirmingState.Initial`, with no run and the store of the rule from the finalized checkpoint, and a reachable store.
`exists_votes_and_confirmations_execution` gives an execution where one honest validator runs the rule at slot zero and votes in that slot.
No execution yet has a run at each slot, which needs the rule to succeed at every slot.
No theorem yet shows that, under the duty, the runs of a validator come at consecutive slots, so that the head that the rule records for the slot before is the head of the run before.

A safety argument moves ancestry facts from the store of one node to the store of another.
`Store.getAncestor_transport_or_collision` and `Store.isAncestor_transport_or_collision` (`Consensus/Proofs/ForkChoice/SharedAncestry.lean`) do that for any two stores, at every fork.
The second store must hold a block at each root that the walk of the first visits.
For ancestry, the second store must also hold the root of the ancestor.
The walk then gives the same result in both stores, or `Store.findBlockCollision`, run over a list of roots that holds the walk, names a root where the two stores hold different blocks.
For two reachable stores, `Store.findBlockCollision_valid` shows that those two blocks differ and both have that root as their hash tree root.
So the alternative is a collision of the hash tree root of blocks.
No theorem yet shows that the store of an honest node holds those blocks.

### Balance-weighted draws

`Consensus/Proofs/Accessors/DrawProbability.lean` samples one digest uniformly from the 32-byte values.
`evalDistEq_uniformSample_vector_map_getElem_injective`, in `Cryptography/Proofs/EvalDistEq.lean`, proves that distinct positions of a uniform vector give a uniform tuple of values.
`prEvent_drawAccepts_uniform_of_before_pectra` and `prEvent_drawAccepts_uniform_of_pectra` give the exact acceptance probability of the checked draw.
It is `(e * (2^b - 1) / M + 1) / 2^b`, with integer division inside the numerator.
Here `e` is the balance, `M` is the largest effective balance of the preset, and `b` is 8 before Electra or 16 from Electra.
They assume `0 < M`, `e <= M` and `M * (2^b - 1) < 2^64`.
These theorems do not model SHA-256 or a sequence of draws.

`Consensus/Proofs/Accessors/DrawRandomOracle.lean` exposes the hash call of `proposerDraw` as `queryProposerDraw`.
Answering it with SHA-256 gives `proposerDraw`.
With the cached random oracle, a draw whose hashed input is absent from the starting cache accepts with the probability above for a uniform digest.
These probabilities hold in the random-oracle model only; no theorem bounds the draw when SHA-256 answers.
The seed is fixed, and other inputs may already be cached.
For two distinct inputs absent from that cache, `prEvent_queryProposerDraw_pair_of_fresh` gives the product of their acceptance probabilities for uniform digests.
No theorem yet gives that product for draws that read different bytes of one digest, or for the whole search.
Seed derivation, including a seed chosen after the oracle answers are seen, is not part of this model.

### Honest validator duties

`Consensus/HonestValidator.lean` holds what an honest validator computes for its duties.
It finds the committee of a validator in an epoch, whether it proposes, and, from Altair, its sync committee seat and subnets.
It also signs each message that a validator sends, under the domain type and the epoch that the receivers check.
The theorems in `Consensus/Proofs/HonestValidator.lean` relate these duties to the checks of the transition and of gossip.

`isValidSignatureAtEpoch_of_signAtEpoch` shows that a duty signature passes the check of a signature at the same domain type and epoch, under the public key of the secret key.
`verifyBlockSignature_of_getBlockSignature` shows that a block signed by its proposer passes the check of the block signature.
`processRandao_ne_invalidRandaoReveal` shows that the RANDAO reveal of the proposer never fails the RANDAO check.
Both assume a block of the current epoch, and a proposer whose public key is that of the secret key.
The gossip checks of a selection proof and of an aggregate and proof read the target epoch, so their theorems assume it is the epoch of the slot.
`isValidSignatureAtSlot_getSyncCommitteeSelectionProof` shows that a sync committee selection proof passes the check at the epoch of its slot.
That check reads the selection data of the same slot and subcommittee, under the public key of the secret key.
`getContributionAndProof_spec` shows that a contribution and proof keeps its aggregator and its contribution.
Its selection proof passes that check for the slot and subcommittee of the contribution.

`getCommitteeAssignment_sound` shows that an assignment is a committee of the epoch that holds the validator.
`getCommitteeAssignment_unique` shows that no other committee of the epoch holds it.
It assumes that the registry stays within its limit, and that the active validators times the committees of the epoch fit in 64 bits.
`getCommitteeAssignment_ne_none` shows that an active validator never gets the answer that it has no committee, under the hypotheses of `exists_mem_getBeaconCommittee`.
The search can still fail, for an epoch after the next one or a committee without a value.
It also fails for the epoch whose first slot plus the length of an epoch reaches 2^64.
There the 64-bit sum of the guide overflows, as `getCommitteeAssignment_eq_error_of_overflow` shows.

From Gloas, a validator also finds the slot of its payload timeliness committee and the slots it will propose.
`getPtcAssignment_sound` shows that an assignment is the first slot of the epoch whose committee holds the validator.
`not_mem_of_getPtcAssignment_none` shows that no committee of the epoch holds a validator without one, when an epoch has a slot.
`getUpcomingProposalSlots_spec` shows which slots are the upcoming proposal slots, in increasing order.
They are exactly the slots after the slot of the state whose proposer in the lookahead is the validator.
`validatePtcMessage_getPayloadAttestationMessageSignature` covers a payload attestation message for the current slot that its validator signed.
It shows that the message passes the wire checks of the fork choice: its slot and its signature.
No theorem covers the other checks of the handler: a known block, the slot of the state and a seat in the committee.
It rests on `fastAggregateVerify_sign`: an honest signature passes the fast aggregate verification under its one key.

`isAssignedToSyncCommittee_ok_iff` states when the sync committee seat check succeeds.
Its answer is then whether the validator's key is in the current or the next committee.
`computeSubnetsForSyncCommittee_ok` shows that its sync committee subnets come once each, in increasing order, from the seats of its key.
`syncCommitteeAtNextSlot_eq` (`Consensus/Proofs/Gossip/SyncCommittee.lean`) states the committee that signs in the slot after a state.
It is the next committee of the state when that slot starts a period, and the current one otherwise; it fails with an overflow at the largest slot.
`getSyncSubcommitteePubkeys_eq` states that, for a subcommittee index below the number of subnets, the keys that gossip checks are the slice of that committee.
The Python suite checks each duty signature against py_ecc, on signing roots computed in the test, and each committee against the shuffle export.
It checks each payload timeliness assignment and the upcoming proposal slots against the window and the lookahead that it reads from a Gloas state.

### Honest aggregation

`Consensus/HonestAggregation.lean` holds the attestation data and the vote of an honest attester, and the aggregates that an honest aggregator builds from votes.
Before Electra the vote is an attestation with one bit, and from Electra it is a single attestation.
An aggregator joins the votes of one committee on the same data into one attestation.
From Altair, a sync aggregator joins the messages on one block root into the contribution of its subcommittee.
The construction theorems are in `Consensus/Proofs/HonestAggregation.lean`.
Each of them assumes only that the construction succeeds, except the theorem on signatures and the two that attestation data and the root of its target have a value.

An attester first builds attestation data from the head block and the state at its slot.
`getAttestationData_eq_ok_iff` states that data: its slot is the slot of the state, it votes for the root of the head block, its source is the current justified checkpoint and its target epoch is the current epoch.
`getEpochBoundaryBlockRoot_eq_ok_iff` states the root of the target.
At a slot that the length of an epoch divides, it is the root of the head block, and otherwise the root that the state records for the first slot of the epoch.
`target_epoch_eq_of_getAttestationData` shows that the target epoch is the epoch of the slot, which the processing of an attestation checks.
The index follows its fork: the committee index before Electra and zero from Electra (`attestationDataIndex_of_lt_pectra`, `attestationDataIndex_of_pectra_of_lt_glamsterdam`).
From Gloas it is zero for a head block of the slot, and otherwise 0 or 1 for an empty or a full payload, while a pending status fails (`attestationDataIndex_of_glamsterdam_of_eq`, `attestationDataIndex_of_glamsterdam_of_ne`).
`isValidDataIndex_of_attestationDataIndex` shows that from Electra the index passes the check of the index of a vote.
`exists_getAttestationData_eq_ok_iff` shows that the data has a value unless that index fails.
It assumes that the length of an epoch is positive and at most the number of recorded roots, and that the slot plus that number fits in 64 bits.
The data takes the head block and the status of its payload as arguments, since the fork choice computes them.
The slot of the data is the slot of the state, so the caller passes the state of the head block processed up to the slot of the duty, as the guide does.

`getAttestingIndices_constructAttestation` shows that the attestation of a validator has that validator as its only attester.
Before Electra, `getAttestingIndices_constructAttestation_getAttestationData` composes it with the data: the attestation names the committee of the slot at the index given, which holds the validator.
`mem_getAttestingIndices_constructAggregate` shows that the attesters of an aggregate are the attesters of its attestations with the same data.
From Electra, `mem_getAttestingIndices_constructAggregateOfSingleAttestations` shows that the attesters of an aggregate are the attesters of its single attestations with the same data and committee.
`getCommitteeIndices_constructAggregateOfSingleAttestations` shows that the committee bits of that aggregate name its one committee.
`constructSyncCommitteeContribution_spec` states the bits of a contribution.
The bit of a seat is set when its key is the key of the validator of a message on the slot and the root.
`fastAggregateVerify_getAggregateSignature` shows that honest signatures of attestations on one message aggregate to a signature that the fast aggregate verification accepts.
That theorem assumes that the secret keys do not sum to zero.
It verifies under the keys in the order of the attestations.

`isValidIndexedAttestation_constructAggregate` and `isValidIndexedAttestation_constructAggregateOfSingleAttestations` (`Consensus/Proofs/HonestAggregateSignatures.lean`) prove that successfully constructed honest aggregates have indexed forms that pass the signature check of an indexed attestation.
The selected signers must have distinct validator indices, use their registered keys and have a nonzero sum of secret keys.
From Gloas, their number must also fit the check's bound.
The proof derives the permutation from those signers to the sorted indices that the receiver reads.
The aggregate adds the signature of every vote, so a validator that votes twice counts twice in the signature but once in the keys.
The theorems avoid this case by requiring distinct signers.

`isValidContributionSignature_constructSyncCommitteeContribution` (`Consensus/Proofs/HonestContributionSignatures.lean`) proves that a contribution of honest matching messages passes its signature check.
The domain and signing root must compute successfully, and the messages must sign that root under their registered keys.
The sum of the secret keys for the selected seats must be nonzero.
A key counts once for each of its selected seats, and each seat takes the first matching message, so duplicate messages add nothing.
The gossip corollaries characterize acceptance of the aggregate's committee check and the contribution topic by their remaining conditions.
These include the checks of time, membership and the aggregator's signatures.
The corollaries assume that the head state of the receiver is the state of the construction.
`validateContributionAndProof_eq_accept_of_getContributionAndProof` removes the two signature checks of the aggregator from the conditions of the contribution topic.
It assumes instead that the aggregator made and signed the contribution and proof with the secret key of its registered public key.

The contribution takes the sync committee as an argument.
The caller passes the committee of the next slot, which gossip and the next block check.
The Python suite checks each vote and each aggregate against values worked out in the test from the guide, with py_ecc for the signatures.

### Honest proposer

`Consensus/HonestProposer.lean` holds what an honest validator computes to fill the block it proposes.
Before Heze it votes on the Eth1 data, and in Electra it counts the deposits of the deposit contract that the block holds.
It computes the state root of the block, and from Electra it joins the network aggregates of one vote and reads the requests of the execution layer from their bytes.
From Fulu it counts the custody groups of a node with validators.
The theorems are in `Consensus/Proofs/HonestProposer.lean`.

The Eth1 data of an Eth1 block is not specified, so the vote takes the timestamp and the Eth1 data of a block as functions, and every theorem about it holds for all of them.
`getEth1Vote_eq_or_candidate` shows that the vote is the data of the state or the data of a candidate block of the chain, and `depositCount_le_of_getEth1Vote` that its deposit count is never below that of the state.
`getEth1Vote_most_voted` shows that, when the state already holds a vote for a candidate, the vote is such a vote with the most copies.
`expectedDepositCount_eq_getEth1PendingDepositCount` shows that the pending deposit count of Electra is the count that block processing requires.
From Fulu that count is zero, as `expectedDepositCount_of_fusaka` shows, so the pending count is defined in Electra only.

`processBlock_stateRoot` shows that block processing never reads the state root of the block.
So `stateTransition_of_computeNewStateRoot` shows that a block that carries the new state root passes the full transition, checks included, and that the state after it has that root.
It assumes a signature that passes the block signature check.
`computeOnChainAggregate_spec` shows that the on-chain aggregate joins the network aggregates sorted by their first committee, and `committeeBits_computeOnChainAggregate` that its committee bits mark exactly those committees.
`getExecutionRequests_eq_ok_iff` shows that the requests read from a list are exactly the requests that give that list.
It rests on the canonical SSZ decoder and on the empty bytes being the only encoding of an empty list.
`signedHeader_eq_ok_iff` shows that the signed header of a block carries the root of its body, and `getValidatorsCustodyRequirement_bounds` that the custody requirement stays between its two bounds.
`totalEffectiveBalance_eq_ok_iff` shows that the balance behind that requirement is the sum of the effective balances of the validators, with a repeated index counted again.
From Altair, `processSyncCommitteeContributions_spec` states the bits of the sync aggregate of a block.
They are exactly the bits that its contributions set, each at the seat of its subcommittee.
It also shows that the contributions name distinct subcommittees below the number of subnets.

No theorem says that the on-chain aggregate verifies, which rests on BLS and on the disjoint committees of the network aggregates.
The Python suite checks the new state root against the state root of each valid sanity block case that the repository holds, at seven forks from Phase 0 to Heze.
It checks the Eth1 vote, the pending deposit count, the custody requirement, the on-chain aggregate, the sync aggregate and the execution requests.
The test works out the expected values from the guides, with py_ecc for the aggregate signatures.

### Payload preparation

`Engine/PreparePayload.lean` holds the forkchoice update that an honest proposer sends to the execution layer, from Bellatrix to Fulu.
The update names the parent of the payload as its head, and carries the payload attributes: the time of the slot, the RANDAO mix of its epoch and the suggested fee recipient.
From Capella the attributes add the withdrawals that the state expects, and from Deneb the root of the latest block header.
Before the merge the head is the terminal block of proof of work, which the proposer looks for in a chain that it is given as a list.
The module lives in the Engine layer because it builds the payload attributes of the Engine API from a beacon state.
The theorems are in `Engine/Proofs/PreparePayload.lean`.

The search for the terminal block reads the list in order, and finds a block by its own hash.
When two blocks share a hash it finds the first, and when two blocks are terminal it returns the first.
`getPowBlockAtTerminalTotalDifficulty_go_eq_ok_some` shows that a block it returns reaches the terminal total difficulty, and that its parent is the zero hash or a block of the chain below that difficulty.
`getPowBlockAtTerminalTotalDifficulty_go_eq_ok_none_iff` states exactly when it returns none, and `getPowBlockAtTerminalTotalDifficulty_go_eq_error` that it fails only on a block that reaches the difficulty with a parent the chain does not hold.
`prepareExecutionPayload_eq_ok_some` states each field of the update, and `prepareExecutionPayload_eq_ok_none_iff` when the proposer asks for nothing.
`payloadHeadBlockHash_of_merged`, `payloadHeadBlockHash_of_inactive` and `payloadHeadBlockHash_of_premerge` state the head before and after the merge.

The theorems that link the update to the checks of a block are the reason for the module.
`processBlockExecution_eq_error_of_prepareExecutionPayload` takes a block that passes the header step on the state of the proposer.
Its payload names the head of the update as its parent, and carries the mix, the timestamp and, from Capella, the withdrawals of the attributes.
The execution part of the block then fails only on the number of blobs, the execution layer, a hash or an accessor, and never on the parent, the mix, the time or the withdrawals.
It rests on `processExecutionPayload_eq_error_of_prepareExecutionPayload`, which assumes only that the checking state shares the slot, the genesis time, the RANDAO mixes and the latest payload header of the state of the proposer.
It also rests on `getExpectedWithdrawals_latestBlockHeader`, which shows that the expected withdrawals do not read the latest block header, and on `payloadInputs_processWithdrawals`.
From Deneb, `parentBeaconBlockRoot_newPayloadRequest_of_prepareExecutionPayload` shows that the request to the execution layer names the parent root of the attributes.

Before the merge, `validateMergeBlock_of_payloadHeadBlockHash_of_configured` and `validateMergeBlock_of_payloadHeadBlockHash_of_difficulty` show that the fork choice accepts a first payload on the head.
With a configured terminal block hash, the block must be of the slot of the state.
Without one, the fork choice must look blocks up in the same chain, its hashes must differ, and no block may name the zero hash as its parent.
The search of the guide accepts a terminal block whose parent is the zero hash, while the merge check of the fork choice looks that parent up, so the theorem leaves such blocks out.
No theorem covers the payload that the execution layer builds, or the safe and finalized blocks, which come from the fork choice.

The Python suite checks each case of the terminal block search, the configured terminal block hash, the withdrawals and the parent root against values worked out in the test from the guides.

From Gloas, `prepareExecutionPayloadGloas` reads the fork choice store and a head node.
The proposer builds on the full node of the head when the fork choice says so at the current slot.
It then applies the payload that the store holds for the head to a copy of the state, and reads the withdrawals of that copy.
Otherwise it keeps the state and the withdrawals that the state records.
From Heze it also reads the transactions of the inclusion lists of the slot before, which the payload attributes of the Engine API here do not carry.
`prepareExecutionPayloadGloas_eq_ok` states each field of the update.
`payloadParentGloas_eq_ok` states the two cases of the parent.

The theorems that link the update to a block assume that the bid of the block builds on the head of the update.
From a full parent the block must carry the requests of the payload that the store holds, and the two hashes of the latest bid must differ.
`slot_of_prepareExecutionPayloadGloas` shows that the state after the parent, header and withdrawal steps has the slot, the time and the mix of the attributes.
`parentRoot_of_prepareExecutionPayloadGloas` shows that the block names the parent root of the attributes.
`latestBlockHash_of_prepareExecutionPayloadGloas` also assumes that the latest block hash is the parent hash of the latest bid.
It shows that the state after those steps has the head as its latest block hash.
`payloadExpectedWithdrawals_of_prepareExecutionPayloadGloas` makes the same assumption.
It shows that this state records the withdrawals of the attributes.
It rests on `applyParentExecutionPayload_latestExecutionPayloadBid`, which shows that the payload of a parent keeps the latest bid.
`checkExecutionPayloadBid_of_prepareExecutionPayloadGloas` takes a bid built on the state of the proposer from a payload that follows the update.
It shows that the bid passes the checks of its parent hash, its parent root and its mix in the bid step.
It makes the assumptions of `latestBlockHash_of_prepareExecutionPayloadGloas`.
It also assumes that the state of the proposer records the root of its latest block header as the root of the slot before.
No theorem here covers the inclusion lists, which come from the store.

The Python suite builds the store of a fork choice case and checks the update on the full and the empty parent at Gloas and Heze.

### Honest builder

From Gloas, `Consensus/HonestBuilder.lean` holds the bid and the envelope of an honest builder, and the signatures on them.
The payload, its requests and the commitments of its blobs come from the execution layer.
The builder chooses the slot, the fee recipient and the value of its bid, and from Heze the bits of the inclusion lists.
`getExecutionPayloadBid` takes the parent hash, the block hash, the RANDAO mix and the gas limit of the bid from the payload.
Its parent root is the root of the latest block header of the state, and it asks for no payment on the execution layer.
`getSelfBuiltExecutionPayloadBid` gives the bid of a proposer that builds its own payload the reserved builder index, no value and the signature at infinity.
`getExecutionPayloadEnvelope` names the root of the block of the bid, the parent of that block and the builder of its bid.
The theorems are in `Consensus/Proofs/HonestBuilder.lean`.

`getExecutionPayloadBid_eq_ok_iff` states each field of a bid.
`getExecutionPayloadEnvelope_eq_ok_iff` states each field of an envelope.
`checkBidBuilder_of_getSelfBuiltExecutionPayloadBid` shows that a self-built bid passes the checks of the builder of a bid on every state.
`getExecutionPayloadEnvelope_checks` takes a block from Gloas that passes block processing, with a bid that a builder built from a payload.
The block must commit to the root of the state after it.
The theorem shows that the envelope of that payload passes the checks of the block root and of the parent root against that state.
It also shows that the envelope passes the checks of the builder, the mix, the gas limit, the block hash and the root of the requests.
It shows that the payload builds on the latest block hash, and that the slot of the bid is the slot of the state.
It rests on `BeaconBlock.hashTreeRoot_header`, which shows that a block has the root of its header.
It also rests on `latestBlockHash_processBlock`, which shows that from Gloas the latest block hash after a block is the parent hash of the latest bid.
`latestExecutionPayloadBid_processBlock` shows that from Gloas a block leaves its own bid as the latest bid.
`latestBlockHeader_processBlock` shows that at every fork a block leaves its header, with a zero state root, as the latest block header.
These rest on `PayloadInputs`, the fields that the checks of a payload and of a bid read.
From Gloas the parent, header, RANDAO and bid steps each change one of them, and the other steps keep them all.
No theorem covers the signature, the time or the withdrawals of the envelope, or the answer of the execution layer.

The Python suite builds the envelope of a fork choice case at Gloas and Heze from its block, payload and requests, and compares it with the envelope of the case.
It also builds the self-built bid of that block and compares it with the bid of the block.

### Slashing protection

`Consensus/SlashingProtection.lean` holds the slashing protection of a signer, and the interchange file of EIP-3076 that moves it between clients.
At the pinned text of the EIP its status is Last Call.
A signer checks a block against the first two conditions of the EIP, and a vote against the last three.
The theorems are in `Consensus/Proofs/SlashingProtection.lean`.

`checkBlockSigning_eq_ok_iff` and `checkAttestationSigning_eq_ok_iff` state exactly when each check passes.
`signBlocks` and `signAttestations` model a signer that checks each message against its record and then records it, from any starting file.
`signingRoot_eq_of_signAttestations` shows that two votes of such a signer that `isSlashableAttestationData` forbids together have the same signing root.
`signingRoot_eq_of_signBlocks` shows that two block headers of one slot that it signed have the same signing root.
`signingRoot_eq_of_processProposerSlashing` shows that the two headers of a valid proposer slashing, both signed by it, are different headers with one signing root.
These theorems hold for every function that gives the signing root of a message.
They assume only that every check of the signer passed.
So a slashable pair of signed messages needs two different messages of one type with one signing root.

When the node hash is a random oracle, `prEvent_signingRoot_le_two_pow` (`Consensus/Proofs/SigningRandomOracle.lean`) bounds the chance of finding such a pair whose counts fit their words, with the signing roots computed by the oracle.
The signer takes its signing roots as an argument, so no theorem composes the signer theorems with this bound.
Its adversary outputs two objects of one type, each with a domain, and the two domains may differ.
`computeSigningRoot_eq_hashTreeRoot` (`Consensus/Proofs/Signing.lean`) shows that the signing root of an object of a lawful type is the root of one value.
That value is the signing data with the object in place of its root.
So the experiment of the SSZ root bound runs on that value, and `prEvent_wins_le_two_pow` bounds a win by `Q^2 / 2^256`.
By `wins_signingValue_iff`, a win is two different pairs of an object and a domain whose objects fit one well-formed type, whose variable-size counts fit their 256-bit words, and whose signing values have one root.
`wins_of_computeSigningRoot_eq` shows that two such pairs of a lawful type with one signing root are a win, with SHA-256 roots.
It needs every variable-size count in them to fit its 256-bit word, which `BeaconBlockHeader.commitmentSized` and `AttestationData.commitmentSized` give for headers and votes.
The step from SHA-256 to the oracle is the idealisation of A4, not a theorem.
`Q` counts every call to the node hash in that experiment, the adversary's and the extraction's, repeats included.

`isSlashableWith_eq_false_of_signAttestations` shows that each signed vote is not slashable with a vote of the starting file, as a record sees it.
A record holds the epochs of a vote and maybe its signing root, not its data.
So that comparison reads a double vote through the signing root, and counts a record without a root as a different vote.

A file may also keep only the latest messages of a key, as the [minimal strategy](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3076.md#supporting-different-strategies) of the EIP does.
`lt_slot_of_signBlocks` shows that if each block of the file is after a slot, so is each block signed from it.
`processProposerSlashing_ne_ok_of_signBlocks` concludes that no valid proposer slashing pairs such an older block with a signed block, since both headers of one have the same slot.
`isSlashableAttestationData_eq_false_of_signAttestations` shows that no signed vote is slashable with a vote older than each vote of the file.
An older vote has a source at most, and a target before, those of each vote of the file.
Each of these theorems needs the file to hold one or more messages of its kind for the key.
A vote with the target of a kept vote is not older, so the theorem on votes says nothing about it.
The signer of these theorems records every message it signs, so a signer that prunes as it goes is not covered here.
A signer of blocks or votes that prunes is covered below.
`mem_blocksOf` and `mem_attestationsOf` show that the messages of a key are those of its own entries.
The proofs read conditions 2, 4 and 5 through `lt_slot_of_checkBlockSlot`, `le_sourceEpoch_of_checkSourceEpoch` and `lt_targetEpoch_of_checkTargetEpoch`.
Through the import steps of `importAndSignBlocks` and `importAndSignAttestations`, they also read the clause of conditions 1 and 3 that refuses each message at the slot or target of a record without a signing root.

Import follows the [minimal strategy](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3076.md#advice-for-minimal-databases) of the EIP, for the held record and for the file.
For each key it keeps one block limit, the greatest slot, and one vote limit, the greatest source epoch and the greatest target epoch, without signing roots.
The two epochs of the vote limit can come from different votes.
So after an import a block must be after the slot limit, and a vote needs a source at least the source limit and a target after the target limit.
Since no limit carries a signing root, no imported message can be signed again.
`lt_slot_of_importFile`, `le_sourceEpoch_of_importFile` and `lt_targetEpoch_of_importFile` show that a message accepted after one import is after every message of both inputs, in that sense.
`checkBlockSigning_of_foldl_importFile` concludes that a block accepted after any finite sequence of imports meets conditions 1 and 2 of every input file.
`checkAttestationSigning_of_foldl_importFile` does so for a vote and conditions 3, 4 and 5.
Both include the initial held file, allow repeated imports and duplicate-key entries, and assume only that the final check passes.
These two theorems cover a record built by imports alone.
The theorems on one import take any held record.

`importAndSignBlocks` models a signer of blocks that also imports files, from any starting file.
`importAndSignBlocks_map_signBlock` shows that a run without imports is `signBlocks`.
`signingRoot_eq_of_importAndSignBlocks` and `lt_slot_of_importAndSignBlocks` state `signingRoot_eq_of_signBlocks` and `lt_slot_of_signBlocks` for it, and the theorems on `signBlocks` follow from them.
`signingRoot_eq_of_importAndSignBlocks_of_processProposerSlashing` and `processProposerSlashing_ne_ok_of_importAndSignBlocks` are their proposer slashing corollaries.
Each holds whatever files the signer imports.
`signingRoot_eq_some_of_importAndSignBlocks` shows that a block of the starting file holds the signing root of each header that the signer signs at that slot.
So the signer signs nothing at the slot of a block of that file without a signing root, as condition 1 asks.
`lt_slot_of_importAndSignBlocks_of_importFile` shows that a header signed after an import is after every block of the file and of the starting file.
`checkBlockSigning_of_importAndSignBlocks` concludes that each header that the signer signs meets conditions 1 and 2 of the starting file.
`checkBlockSigning_of_importAndSignBlocks_of_importFile` concludes the same for each file imported before the header.
`importFile_of_data_eq_nil` shows that importing a file without entries puts the record in its minimal form, which prunes it.
So these theorems also cover a signer of blocks that prunes its record with the minimal strategy as it goes.

`importAndSignAttestations` models a signer of votes that also imports files, from any starting file.
`importAndSignAttestations_map_signAttestation` shows that a run without imports is `signAttestations`.
`signingRoot_eq_of_importAndSignAttestations`, `isSlashableWith_eq_false_of_importAndSignAttestations` and `isSlashableAttestationData_eq_false_of_importAndSignAttestations` state the three theorems on `signAttestations` for it, and the theorems on `signAttestations` follow from them.
Each holds whatever files the signer imports.

`checkAttestationSigning_of_importAndSignAttestations` shows that each vote that the signer signs meets conditions 3, 4 and 5 of the starting file.
`le_sourceEpoch_of_importAndSignAttestations` follows from it: if each vote of that file has a source at least an epoch, so does each signed vote.
`lt_targetEpoch_of_importAndSignAttestations` does the same for a target after an epoch.
Both need that file to hold one or more votes of the key.

`le_sourceEpoch_of_importAndSignAttestations_of_importFile` shows that a vote signed after an import has a source at least each source of the file and of the starting file.
`lt_targetEpoch_of_importAndSignAttestations_of_importFile` shows that the target of such a vote is after each target of both files.
`checkAttestationSigning_of_importAndSignAttestations_of_importFile` concludes that such a vote meets conditions 3, 4 and 5 of each file imported before it.
Since `importFile_of_data_eq_nil` makes a prune the import of an empty file, the theorems on `importAndSignAttestations` also cover a signer of votes that prunes its record with the minimal strategy as it goes.

`readUInt64_uint64Json` and `readBytes_bytesJson` show that each integer and each byte string of a file reads back as written.
`ofJson_toJson` shows that a whole file reads back as itself from the document that `toJson` writes, whatever its records.
No theorem says what `ofJson` does on a document that another client wrote.

The Python suite checks each condition and each malformed field against cases worked out from the EIP.
With release archives enabled, it runs the 38 interchange tests of `eth-clients/slashing-protection-interchange-tests` against their flags for the minimal strategy.
Its signer imports each file with the minimal strategy and records each message it signs with its signing root.

### Optimistic sync

`Consensus/ForkChoice/OptimisticSync.lean` holds the optimistic sync from Bellatrix: the blocks that a node imports before the execution layer judges their payload.
An optimistic store keeps their roots beside the blocks of the node, and the rules read only that store.
The theorems are in `Consensus/Proofs/ForkChoice/OptimisticSync.lean`, and most assume only that their function succeeds.

`isOptimisticCandidateBlock_eq_ok_iff` states when a block may be imported optimistically: its known parent carries a payload, or its slot is far enough before the clock.
`latestVerifiedAncestor_spec` shows that, before Gloas, the latest verified ancestor of a block is reached through optimistic blocks only.
The same theorem shows that this ancestor is not optimistic, or has the zero parent root.
`onValidPayload_spec` shows that a valid payload removes exactly the roots of its payload chain from the optimistic set.
`onInvalidatedPayload_spec` shows that the first invalid block removes exactly the optimistic roots whose payload chain holds it.
`payloadChain_of_lt_glamsterdam` shows that before Gloas the payload chain of a block is its whole chain, so these are its known ancestors and descendants.
`isOptimisticRestrictedDomain_iff` lists the seven domain types under which an optimistic validator may not sign.

The rule of the latest valid hash in `Consensus/ForkChoice/Optimistic.lean` names the first invalid block.
The theorems here take that block as given.
No theorem relates the optimistic set to the blocks that the store of the fork choice removes.
A node is optimistic when its head is optimistic, or when invalid payloads left its block tree with no viable branch.
`isOptimisticNode_of_isHeadOptimistic` shows that, at every fork, the first case alone makes an optimistic node.
`isOptimisticNode_of_not_isHeadOptimistic` shows that the second case needs a block that the fork choice dropped at or above the justified block.
So a tree that empties with nothing invalidated does not count.
This assumes that the optimistic store holds only blocks that the fork choice accepted.
The rule approximates the guide, which asks that every viable branch was invalidated: one invalidated block above the justified block is enough.
EthLib counts a dropped justified block as no viable branch, a choice of its own.
`hasNoViableBranch_eq_ok_true_iff` shows that, with the justified block known and the filter successful, no viable branch means that no leaf above it passes the viability filter.
`filterNodeTree_eq_nil_iff` gives the same fact for the filtered tree of any node.
The re-run of the merge block checks is not defined, nor the answer to an execution layer that fails to respond.

From Gloas a block carries a bid, and its payload arrives later in an envelope.
The optimistic sync guide has no Gloas text, and its tests stop before Gloas.
EthLib therefore reads the Bellatrix guide at Gloas, a choice of its own.
A root of the optimistic set then names a block whose payload was imported optimistically, as the Gloas gossip rules key a payload status by block root.
A block carries a payload when its bid names a nonzero block hash; `isExecutionBlock_of_glamsterdam` states it.
`payloadChain_of_glamsterdam` shows that the payload chain is the chain of the block, filtered by the block hashes that the bids name.
`payloadChain_links` shows that each root of a payload chain builds on the payload of the next one, as the fork choice sees a full parent.
`parentRoot_mem_payloadChain_iff` shows that the parent of a block is on its payload chain exactly when the fork choice sees the parent as full.
`payloadChain_suffix` and `mem_payloadChain_trans` show that the payload chain of a block holds the payload chain of each of its roots.
`payloadChain_of_find?_some` shows that the payload chain of a block goes on at the first ancestor whose bid names the parent block hash of its bid, with the chain and the payload chain of that ancestor found.
`payloadChain_of_find?_none` shows that it is the block alone when no ancestor is named.
So it reaches every payload that the block builds on among the known blocks of its chain, through any number of blocks, full or empty.
A payload that builds on an invalid payload in that way leaves the set.
A block built on its parent without the payload of the parent does not hold that payload on its payload chain.
So its own optimistic payload stays when only the payload of the parent is invalid.
From Gloas the head of the fork choice is a block with or without its payload, so the optimistic store keeps the status of the head.
A full head reads the payload of its block, an empty head the payload its block builds on, and a pending head both; `isHeadOptimistic_of_full`, `isHeadOptimistic_of_empty_of_named` and `isHeadOptimistic_of_pending_of_optimistic` and `isHeadOptimistic_of_pending_of_not_optimistic` state it.
The search of the head never stops at a pending node, so reading both for a pending head is a choice of EthLib, the cautious one.
`isHeadOptimistic_of_empty_of_unnamed` shows that an empty head whose bid names no known payload fails with `payloadNotVerified`.
That is the case of an empty first block of Gloas, whose bid builds on a payload of Fulu, which a store of one fork never holds.
The rule fails there rather than call that payload verified, so the head rule and the latest verified ancestor agree.
From Gloas the latest verified ancestor takes a node, and reads only the payloads that the node holds.
A full node holds every payload of its payload chain, and an empty or pending node holds all but its own.
`latestVerifiedAncestor_ne_root` shows that a node without its own payload is never its own verified ancestor.
So a pending node reads as full or empty for the head, and as empty for the ancestor: each reading is the cautious one.
The status of a node is an assumption: a full node must name a payload that the store holds, and the rules do not check it.
The optimistic store follows the fields of the guide, which do not record the payloads held; the search of the head returns a full node only for a held payload.
`latestVerifiedAncestor_of_glamsterdam` shows that the answer is the first of those payloads that is not optimistic, with every one before it optimistic.
`latestVerifiedAncestor_eq_error_of_optimistic` shows that it fails with `payloadNotVerified` when all of them are optimistic, or when there is none.
Before Gloas the walk returns an optimistic genesis block; from Gloas it never returns an optimistic payload, a choice of EthLib.
No published source says what an invalid payload removes from the store of the fork choice from Gloas.
EthLib defines it as follows, a reading of its own that follows the fork choice of Gloas.
A block and its payload are two nodes, and the state of a block does not depend on the block's own payload.
So an invalid payload leaves its block valid, and the node of that block without its payload stays.
A block whose bid builds on the invalid payload starts from a state that assumes that payload, so it leaves the store with its descendants.
The votes for the block with its invalid payload are dropped too, so their weight reaches neither that node nor its ancestors, as the guide asks of invalid blocks.
The records that the store keeps by block root, such as the votes of the payload committee, leave with each dropped block.
The latest valid hash names a payload, and each bid names the hash of the payload on which its block builds.
The walk climbs the chain and stops at the first block whose bid builds on the latest valid payload.
The parent of that block need not be known, so a hash that names the payload under the anchor of the store is found.
The walk assumes, as the execution layer promises, that the hash names a payload on the chain.
When the hash names the payload of the block itself, nothing is removed, as `onInvalidPayload_of_gloas_self` shows.
Otherwise the first invalid block is the earliest block of that walk whose payload is invalid; without a hash, or when the walk leaves the store first, it is the block itself.
The theorems below give each step of the walk, and its result over a whole chain of known parents for a block in the store.
For a block that the store does not hold, the step theorems reduce the walk to its parent, which the store holds when it is known.
`removeFullDescendants_eq` shows that the removal drops exactly the known blocks that descend from the first invalid block with its payload, and never that block itself.
`removeFullDescendants_self` shows that the first invalid block stays and loses its payload.
`removeFullDescendants_of_empty` shows that every block built on the first invalid block without its payload stays.
`removeFullDescendants_getSupportedNode` shows that no vote left supports the first invalid block with its payload.
`onInvalidPayload_of_gloas_none` shows that without a hash the removal starts at the block itself.
`firstInvalidPayload_of_named`, `firstInvalidPayload_of_orphan`, `firstInvalidPayload_of_full`, `firstInvalidPayload_of_empty` and `firstInvalidPayload_of_not_lower` give each step of the walk.
For a block in the store, when every known block sits at a later slot than its known parent, `firstInvalidPayload_of_absent` shows that the walk finds nothing when no block of the chain builds on the hash.
Otherwise take the nearest block of the chain that builds on the hash.
`firstInvalidPayload_of_chain_full` shows that the walk returns the earliest block, from that block on, whose payload the chain builds on.
`firstInvalidPayload_of_chain_empty` shows that, when the chain builds on no such payload, the walk returns its starting candidate, the block itself.
`onInvalidPayload_of_gloas_self`, `onInvalidPayload_of_gloas_unnamed`, `onInvalidPayload_of_gloas_parent` and `onInvalidPayload_of_gloas_full_parent` give the removal for a latest valid hash.
`onInvalidPayload_eq` shows that, at every fork, an invalid payload leaves the store as it was or applies the removal of its fork.
`Linked.onInvalidPayload` shows that the removal keeps the store linked at every fork.
From Gloas the second case of an optimistic node reads the dropped blocks as before.
`isOptimisticNode_of_not_isHeadOptimistic` shows that, at every fork, the second case needs a dropped block at or above the justified block.
An invalid payload of the justified block drops only the blocks built on that payload, so the node of that block without its payload can stay viable.
`isOptimisticNode_of_isHeadOptimistic_error` shows that it fails as the optimism of the head does.
The store holds the blocks of one fork, so a payload chain does not cross from Gloas into Fulu.
From Heze the store also records whether a payload satisfies the inclusion lists of the slot before.
The Heze guide derives that answer from the status that the execution layer gives a payload.
The verdict of the execution layer follows from the same status.
`BlockSources.withPayloadStatus` puts the status into the sources that the handlers read.
For a payload not yet validated, its execution layer accepts every payload and the payload satisfies its lists.
For an invalidated one, it rejects every payload and the payload does not satisfy them.
`Store.isPayloadInclusionListSatisfied_of_notValidated` shows the answer `true` for an envelope that the handler accepts.
`Store.onExecutionPayloadEnvelope_ne_ok_of_invalidated` shows that an invalidated payload is never kept.
A status outside the three of the guide counts as invalidated, a choice of EthLib: such a payload is never kept.
The export rejects such a status before any step runs.
`Store.recordValidatedInclusionListSatisfaction_satisfied` shows that a payload that turns valid takes the answer that the execution layer gives with its verdict.
`Store.recordValidatedInclusionListSatisfaction_eq` shows that nothing else in the store changes, and `Store.recordValidatedInclusionListSatisfaction_other` that every other answer stays, those of its ancestors among them.
The store of the fork choice does not keep the status of a payload, but the optimistic store does.
`OptimisticStore.onValidatedPayload_ok` shows that the move to valid succeeds only for an optimistic payload, which then leaves the optimistic set as a valid payload does.
The Python suite checks each rule on Bellatrix blocks built in the test, with roots from the SSZ export.
At Gloas it checks the execution block, the candidate rule, the two payload answers and the latest verified ancestor.
It checks the optimistic head of each status on a pinned Gloas fork choice case, and that the second case is refused.
At Heze it checks the answer on the inclusion lists for each status, and once the payload turns valid, on a pinned Heze case.

### Light client

A light client accepts an update that the sync committee signed, and moves its store by it.
`Consensus/Proofs/LightClient/Authenticate.lean` states what an accepted update proves.

`validateLightClientUpdate_proves` lists the checks that an accepted update passed.
At least the minimum of bits of its aggregate are set.
The signature check accepts the keys of those members on the signing root of the attested header.
The finality branch and the branch of a carried next committee verify against the state root of that header.

`validateLightClientUpdate_finalized` takes any value whose root is that state root, such as the beacon state of the attested block.
Its node at the index of the finality branch is the root that the update proves.
That root is the root of the finalized beacon header, or zero at the genesis slot.
Otherwise the search `findBranchCollision` over the two climbs returns two different messages with one SHA-256 hash.
`validateLightClientUpdate_nextSyncCommittee` states the same for the root of the next committee.
`lightClientGindices_eq` shows that each index is the generalized index of the path of its field in the type of the beacon state, at every fork from Altair and at every preset.
It joins two theorems that name the ordinals of the fields.
From Altair to the forks before Gloas, `lightClientGindices_eq_of_lt` shows the same three indices.
From Gloas the state is a progressive container, and `lightClientGindices_eq_of_glamsterdam_le` shows them too.
On a state of any fork from Altair, `BeaconState.nodeRoot_finalizedCheckpoint_root` reads the finality node as `state.finalizedCheckpoint.root` itself, since a 32-byte value is its own root.
`BeaconState.nodeRoot_nextSyncCommittee` and `BeaconState.nodeRoot_currentSyncCommittee` read the committee nodes as the roots of those fields, which always exist.
These theorems take the lawful SSZ type of the state as an argument, and the committee theorems also take a nonempty committee.
Instance search finds that lawful type at the mainnet and minimal presets.
`validateLightClientUpdate_finalizedCheckpoint` joins the finality result to these nodes.
Take an accepted update, and a beacon state whose root is the attested state root.
The proved root is then the root in the finalized checkpoint of that state.
Otherwise `findBranchCollision` returns a SHA-256 collision.
`validateLightClientUpdate_nextSyncCommittee_state` states the same for the next committee.
Both assume that the index of the slot is the index of the state's own fork.
The client then reads the state with the layout of that fork.
`initializeLightClientStore_currentSyncCommittee` states the same for a new store.
The store keeps the committee that its bootstrap proves.
Its root is the root of the current committee of the trusted state, or the search returns a collision.
It makes the same assumption on the index, at the slot of the bootstrap header.
`stateForkAtSlot_gindices` discharges that assumption from the fork schedule.
Take a slot whose scheduled fork is from Altair, and a store of that fork or later.
The schedule must start Electra no later than Fulu, and Gloas no later than Heze.
The client then reads the three nodes at the indices of the fork of the slot, so at the deeper indices of Electra from Electra.

From Capella a header also carries the execution data of its block, which `Consensus/Proofs/LightClient/Execution.lean` binds to the block.
From Capella to Fulu, `isValidLightClientHeader_executionPayload` takes a valid header at a slot from Capella.
It also takes a body of a fork from Capella to Fulu whose root is the body root of the header.
The execution root of the header is then the root of the execution payload of that body, or `findBranchCollision` returns a SHA-256 collision.
`BeaconBlockBody.nodeRoot_executionPayload` reads node 25 of such a body as the root of its payload.
Like the state theorems, these take the lawful type of the body.
`ExecutionPayload.hashTreeRoot_header` shows that before Gloas the header of a payload has the root of the payload.
So `isValidLightClientHeader_execution_eq` takes the binding to the fields, for a body of the fork of the header, at a slot from Capella, and from Deneb for a header from Deneb.
The execution header of the light client header is then the header of the payload of the body, field by field.
Otherwise a search over the two branch climbs, or one over the hash inputs of the two header roots, names a SHA-256 collision.
`isValidLightClientHeader_execution_binding` states this step once, for two payload headers of one fork whose roots are the execution root and the root of the payload header of the body.
From Deneb, `isValidLightClientHeader_blobGas` applies this to the blob gas used and the excess blob gas, at a slot from Deneb.
The schedule must start Capella no later than Deneb.
`isValidLightClientHeader_blobGas_zero` shows that a valid header of an earlier slot has zero for both.

A store of a later fork upgrades a header of an earlier fork before it checks it.
So the fork of a header can be later than the fork of its block.
`isValidLightClientHeader_execution_eq_upgrade_capella` takes a valid header from Deneb to Fulu at a slot from Capella and before Deneb, and a Capella body.
The execution header is then the upgrade of the payload header of the body.
So it has the fields of that payload header, and zero for both blob gas fields.
`isValidLightClientHeader_execution_eq_upgrade` takes a valid header from Deneb to Fulu at a slot from Capella and from Deneb, and a body of any fork from Deneb to Fulu.
The execution header is again the upgrade of the payload header of the body, which keeps every field.
`isValidLightClientHeader_blobGas_upgrade` applies this to the two blob gas fields, at a slot from Deneb.
Its schedule must also start Capella no later than Deneb.
`LightClientHeader.isValidLightClientHeader_upgrade_execution` takes the header and the body of `isValidLightClientHeader_execution_eq`, and the upgrade of the header to a fork before Gloas.
The upgraded header has the upgrade of the payload header of the body, by `LightClientHeader.upgrade_execution`.
In each of these theorems, the alternative is a SHA-256 collision that a search names.
The search is over the two branch climbs, or over the hash inputs of two execution header roots.

From Gloas, `isValidLightClientHeader_parentBlockHash` binds the block hash of a header at a slot from Gloas to the parent block hash of the bid of a Gloas body.
`isValidLightClientHeader_executionBlockHash` binds it, for an earlier slot from Capella, to the block hash of the payload of a body from Capella to Fulu that is from Deneb exactly when the slot is.
For such a slot, `getLcExecutionRoot_rebuild` shows that the execution root is rebuilt from the block hash.
The rebuilt execution header is a Deneb header for a slot from Deneb, and a Capella header before Deneb.
`rebuildLcExecutionRoot_eq` states the rebuilt root on every input.
At the genesis slot it is the root of the empty execution header of that fork.
Otherwise the block hash climbs as field 12 of the execution header, through a slice of the branch that ends before its last 4 nodes.
The slice has the 5 nodes before them from Deneb, and the 4 before them before Deneb; a shorter branch gives a length error.
These two are rewrite lemmas: no theorem yet binds the rebuilt root to the payload of a body.
The headers that the client checks are valid: `initializeLightClientStore_header_valid`, `validateLightClientUpdate_attestedHeader_valid`, and `validateLightClientUpdate_finalizedHeader_valid` after the genesis slot.
The index theorems `executionPayloadGindex_eq`, `payloadHeaderBlockHashGindex_eq`, `executionBlockHashGindex_eq` and `executionBlockHashGindexGloas_eq` hold at every preset.

The signature theorems assume `SignatureChecks.AggregateSound`, listed in A4.
Under it, `validateLightClientUpdate_signed` shows that every member whose bit is set signed the signing root.
`validateLightClientUpdate_signed_outside` adds that a set of keys holding fewer seats of the committee than there are signers leaves a signer outside the set.
`SignatureChecks.not_aggregateSound_acceptAll` shows that the assumption has content: the checks that accept every signature do not meet it.
`LightClientForgery.forgeAdvantage_le` bounds how often a forger makes the light client accept an aggregate with one designated honest member's bit set, on a root that member never signed.
It assumes the random oracle model, a proof of possession for every signer, and at most `q` and `qK` hash calls; the bound is small if co-CDH is hard and the solver built from the forger is efficient, which no theorem bounds.
It is not a proof of `AggregateSound`, and Ethereum's keys carry deposit signatures, not those proofs.
The bound protects that member's bit only.
Covering every honest member of a committee needs a guess among them, losing up to a factor of the number of honest seats; that step is not proved.
Updates signed by corrupted members alone are still accepted, so the safety of headers also needs an honest supermajority of the committee.
The reduction loses a factor `q`, the number of all message hash calls, and no theorem bounds its running time.
A deposit signature cannot simply count as a proof of possession here: it is a signature under the message hash, and Ristenpart and Yilek ([ePrint 2007/264](https://eprint.iacr.org/2007/264)) show that such proofs fail when the honest key signs chosen messages.
With the signing oracle of this game, the honest key's signature on the deposit message of a rogue key `x g1 - pk` gives that key a valid deposit signature.
The header slots of the store never move back.
`applyLightClientUpdate_finalizedSlot_le`, `processLightClientUpdate_finalizedSlot_le` and `processLightClientStoreForceUpdate_finalizedSlot_le` show that the finalized slot never decreases.
`applyLightClientUpdate_optimisticSlot_le`, `processLightClientUpdate_optimisticSlot_le` and `processLightClientStoreForceUpdate_optimisticSlot_le` show the same for the optimistic slot.
`applyLightClientUpdate_slot_order`, `processLightClientUpdate_slot_order` and `processLightClientStoreForceUpdate_slot_order` show that a finalized slot at or below the optimistic slot stays there.
`initializeLightClientStore_headers` shows that a new store starts with one header for both.
`LightClientStore.upgrade_beacon` shows that the upgrade of a store to a later fork keeps both beacon headers, so it keeps both slots too.
So every store that these four steps reach from a bootstrap keeps that order.
`processLightClientUpdate_optimisticHeader` gives the optimistic header after an update in full.
It becomes the attested header when that header is newer and more members signed than the safety threshold.
That threshold is half the larger count of signers, of the previous period and of the current one with the update.
A newer finalized header signed by two thirds of the committee then replaces it if that header is newer still.
`processLightClientUpdate_finalizedHeader` gives the finalized header after an update, which moves only with two thirds of the committee.
`processLightClientUpdate_maxActiveParticipants` gives both counts of signers after an update.
They move back a period when a newer finalized header enters the next period.
That needs two thirds of the committee, and a store that knows the next committee.
`SyncAggregate.participants_le` bounds the signers by the size of the committee, so their count fits in 64 bits.
No theorem links an honest signer to the canonical chain; that is a property of the validators, not of the protocol text.

### Casper FFG

Casper FFG finalizes checkpoints, each a block with an epoch, from the votes of validators.
The model in `Consensus/Proofs/Models/Ffg/` follows Casper FFG §2 and Gasper §4 and §8.6.
Each checkpoint has its own validator set, as each block has in Gasper §8.6, and a link counts the stake of the set of its target.
A supermajority link weighs its voters with one stake for each validator, as Gasper §8.6 assumes.
A constant validator set then gives the model of Casper FFG and Gasper §4.

A slack link weakens a supermajority link by a second set for its target: the bound adds twice the stake of the target set outside that second set.
The beacon chain needs that slack, since it weighs the attesters of the previous epoch against the active balance of the current one.
A slack link also lets each checkpoint have a set of weights, each a stake for every validator, and holds when its bound holds under one of them.
A refinement from the beacon state puts in that set the effective balances of each state at the last slot of the epoch of the checkpoint or of the next one, when that state records the root of the checkpoint for its epoch.
So a balance may change from one checkpoint to the next, and two branches that justify one checkpoint from two states both fit, where one stake function could not.
Nothing excludes other weights from a set, and the zero weights make every ordered link a slack link, so the bounds say something only when every choice of weights in each set stays close to the reference weights.
`accountable_safety_dynamic_slack`, `accountable_safety_reference_slack` and `accountable_safety_of_change_slack` (`AccountableSafety.lean`) take slack links, with a validator set and a set of weights for each checkpoint.
They measure every stake under reference weights, and lose the slack of the two links that they find and the change from the reference weights to the weights under which those links hold.
In that change a gain of weight counts once, like an activation, and a loss twice, like an exit.
Nothing ties the second sets to the validator sets, so these bounds say something only when the slack is bounded, as the exit churn would bound it; no theorem states that bound yet.
The churn would not bound the change of weights alone: the inactivity leak, penalties and slashings lower effective balances outside any churn, so a bound over a window also needs a budget for those losses.

`accountable_safety_dynamic` (`AccountableSafety.lean`) is Gasper Theorem 8.3.
It takes two finalized checkpoints whose blocks conflict.
Then two justified checkpoints, with epochs between those of the two finalized ones, have the following property.
Validators of both their sets broke a slashing condition, and their stake is bounded below.
The bound is two thirds of the stake of one set, less one third of the stake of the other, less the stake that activated into the first set or exited from the second since any reference set.
Gasper states it with a maximum and divisions by three; the theorem states its two terms, multiplied by three, in natural numbers.
If one of the two sets has no stake, both bounds hold with no slashable validator.
The reader does not choose the two checkpoints, so the theorem says something only when every justified checkpoint between the two finalized epochs has a set with positive stake.

`accountable_safety_reference` (`AccountableSafety.lean`) restates the first bound against one fixed reference set `V₀`, such as the set of a trusted checkpoint.
The stake of `V₀` is at most three times the slashable stake, plus the change of each of the two sets since `V₀`.
The change of a set counts the stake that joined once and the stake that left twice.
`accountable_safety_of_change` assumes that the change of every justified set between the two finalized epochs is at most `b`, and bounds the stake of `V₀` by three times the slashable stake plus `2 b`.
`accountable_safety_of_steps` assumes that every justified checkpoint between the two finalized epochs has a set reached from `V₀` in at most `n` steps.
Each step changes the set by at most `d` in that measure, so the stake of `V₀` is at most three times the slashable stake plus `2 n d`.
As above, the reader does not choose the two checkpoints, so the hypothesis covers every justified checkpoint between the two finalized epochs.
For a step of one epoch, `d` bounds the stake that activates plus twice the stake that exits, the source of a consolidation included.
The churn queues carry unused churn to later epochs, so such a bound can fail in one epoch while the total over a window holds; `accountable_safety_of_change` takes that total.
The model does not follow withdrawals; the specification covers them with the withdrawability delay in the weak subjectivity period.
These theorems take one stake for each validator, so a top-up, a consolidation or a penalty of a validator that stays in the set is outside them; the slack forms above count it as a change of weights.
No theorem yet derives those steps from the beacon state.

`accountable_safety` (`AccountableSafety.lean`) takes one validator set for every vote, and follows from `accountable_safety_dynamic`.
Then validators with at least one third of the stake broke a slashing condition.
With a total stake of zero this holds for every set of votes, so the theorem says something only for positive stake.

`plausible_liveness` (`PlausibleLiveness.lean`) takes honest validators in every validator set, with at least two thirds of its stake.
The votes so far are finite, the stake of each set is positive, and no honest validator is slashable.
Each honest vote comes from a justified source.

Then there is a justified checkpoint with the following property.
For every block whose chain contains its block, the honest validators can add votes that finalize that block.
The block is finalized at an epoch above every justified epoch so far.
The new votes come from justified sources, and no honest validator becomes slashable.

A vote names the validator that signed it, so both theorems assume that no one forges a vote.
Below, the votes of the model come from the attestations that the blocks of a chain apply, but neither theorem is yet applied to them, so neither is yet about what a client runs.

These pieces of that link exist.
`FfgVotes.lean` relates the slashing conditions of the beacon chain to those of the model.
`justificationTest_iff_stake` (`Consensus/Proofs/Transition/FfgStake.lean`) reads the test of justification as a comparison of stakes.
There the stake of a validator is its effective balance, and the indices count as a set.
It needs an active stake of more than one and a half increments.
Up to that bound, the beacon chain can justify with no vote at all, since a total balance is never below one increment.
`processAttestationAltair_targetFlag` (`Consensus/Proofs/Transition/TargetFlags.lean`) covers one attestation from Altair.
A timely target flag that it sets belongs to an attester of an indexed attestation that passed the checks of the step.
With the BLS checks, the aggregate signature verifies under keys that include the key of that attester.
Reading this as a signature by that attester assumes that BLS aggregate signatures cannot be forged.
The source of that attestation is the justified checkpoint of the epoch of the flags.
Its target is the checkpoint of that epoch, with the block root that the state records for its first slot.
A vote is a pair of a validator and attestation data.
An attestation casts a vote for each validator that its bits show in its committees, with its data (`attestationVotes`, `Consensus/Proofs/Transition/TargetVotes.lean`).
A block casts the votes of its attestations, read in the committees of the state before the block (`blockVotes`).
`processBlock_attestationSplit` (`ActiveKept.lean`) shows that the block reads those same committees when it processes each attestation.
The steps before the attestations keep activity up to the current epoch and write only the RANDAO mix of the current epoch, which the seeds of the previous and current epochs do not read.
That needs more than `MIN_SEED_LOOKAHEAD + 2` epochs of RANDAO mixes.
`voteFrame_processBlock` then shows that a block sets a target flag only from one of its votes, for the link of the epoch of the flag at the position of the flag.
The block keeps the slot, the block roots and the justified checkpoints.
So `TargetFlagsVoted.of_voteFrame` keeps each target flag backed by a vote for its link, from the earlier votes or those of the block.
`TargetFlagsVoted.of_advanceSlots` (`Consensus/Proofs/Transition/TargetSlots.lean`) carries the same fact across the slots, the epoch step included.
The slot step writes one block root, so the roots at the first slots of the current and previous epochs stay.
That needs at least one slot per epoch, and a buffer of roots that covers two epochs, as both presets do.
The epoch step moves the flags of the current epoch to the previous one, and justification moves the current justified checkpoint to the previous one.
Justification does not run in the first two epochs, so the theorem assumes the two justified checkpoints equal there, and the slots keep that.
The genesis state built from deposits has equal justified checkpoints, and the slots, the blocks and every upgrade keep that (`Consensus/Proofs/Transition/TargetUpgrades.lean`).
`TargetFlagsVoted.of_processUpgrades` carries the target-flag fact across the upgrades from Altair on.
Before Altair, `PendingVoted` (`Consensus/Proofs/Transition/TargetPending.lean`) says the same of each pending attestation of the two epochs, across attestations, blocks and slots.
It relies on the beacon committees of those epochs staying fixed while the epoch is recent (`Committees.lean`), which needs more than `MIN_SEED_LOOKAHEAD + 2` epochs of RANDAO mixes.
`TargetFlagsVoted.of_upgradeToAltair` (`TargetUpgrades.lean`) builds the target flags of the first Altair state from such pending attestations.
A vote of a block is evidence that its validator signed the data only with the BLS checks, and under the assumption that BLS aggregates with proofs of possession cannot be forged, since the block accepts the attestation only when the signature checks accept its aggregate signature.

`processJustificationAndFinalization_linkWithChurn` (`Consensus/Proofs/Transition/FfgJustification.lean`) refines one epoch step.
It takes the target-flag fact from Altair, the pending-attestation fact before Altair, and an active stake of more than one and a half increments.
The two facts are needed at the state after the slot step where justification runs; `advanceSlot_slackJustifiedCheckpoints` (`FfgSlack.lean`) reaches it from the state before the slot.
The validator set of a target is the active set of its epoch, as each checkpoint has its own set in Gasper §8.6.
Each validator weighs its effective balance in the state before the step.
The votes of the model must hold those of a set of votes from which the target flags and the pending attestations come.
The step keeps the current justified checkpoint, or replaces it by the checkpoint of the previous or the current epoch, whose test passes; the link goes from the justified checkpoint of that epoch to the new checkpoint.
Then twice the stake of the set of the target is at most three times the stake of the voters of the link, plus a term of churn.
The term is twice the stake of that set outside the active set of the current epoch, because the step divides by the active balance of the current epoch.
`linkWithChurn_of_test` gives the same bound for one epoch whose test passes, when each counted attester is active in that epoch and cast a vote of the set for its link.
`TargetFlagsVoted.attester` from Altair and `PendingVoted.attester` before it give that fact.
With them, `linkWithChurn_of_test` would give the bound for the previous epoch when both pass, whose bit the finalization rules read; no theorem states that yet.
For the current epoch the term is zero.
For the previous epoch, `exists_exitEpoch_eq_of_mem_sdiff_active` shows that it counts only validators that exit at the current epoch, when the registry stays within the limit of the preset.
The theorem reads the unchecked active indices, and the bound makes each index equal to its registry position.
The exit churn bounds that stake, but no theorem states that bound yet.
So one step gives the stake condition of a supermajority link of the model, up to that term.
The beacon chain leaves slashed attesters out, and the model counts them, so the converse does not hold.
The ancestry of the blocks of the link is not shown yet.

`processJustificationAndFinalization_slackJustifiedCheckpoints` (`Consensus/Proofs/Transition/FfgSlack.lean`) turns one step into a slack link of the model.
If the two justified checkpoints of the state before the step are slack-justified, so are those of the state after it.
A new current justified checkpoint must match the state of that step.
Its set is the active set of its epoch, its set of weights holds the effective balances, and each member of both of its sets is active in the current epoch.
In that single step, only the step that changes the current justified checkpoint reads them, so the effective balances may change before a later step.
Two branches can justify the same checkpoint in different states; its set of weights holds the balances of both, but its validator set must be the active set of its epoch in both states, and no theorem shows that yet.
That single step asks a match only for the new current justified checkpoint; the hypotheses of a chain step ask it for both recent epochs at each end of an epoch, since finalization also reads a previous target that the same step justifies.
The step also needs the previous justified epoch below the previous epoch once justification runs, and the source block of each recent link in the chain of its target block.
`slackJustifiedCheckpoints_of_chain` (`Consensus/Proofs/Transition/FfgSlackChain.lean`) carries these steps along a chain from the genesis state built from deposits, for a set of votes that holds the votes of each block step.
`slackJustifiedCheckpoints_activeSetAt_of_chainSteps` (`FfgSlackActive.lean`) takes the votes that the block steps of the run cast, the active sets and the effective balances.
Its step asks only the active stake, the order of the blocks and the preset.
The order of the blocks asks that the map from roots to blocks keeps in order the roots that a state records at two consecutive slots, and the zero root before the root of slot zero (`rootLinks`, `Consensus/Proofs/Transition/FfgRoots.lean`).
Two consecutive slots record the same root, or a block and its child, since the header check makes the parent root of a block the root recorded at the slot before it.

`rootLinks_cases_of_chainSteps` (`Consensus/Proofs/Transition/RootLinks.lean`) states that for a run of a chain, upgrades included.
A block step may skip the check of the state root, so the root of its block is that of the block with its state root replaced by the root of the state after the step.
The step that checks the state root leaves the block as it is.
The other cases are a pair that the first state records, the first pair, and a state of the run that hashes to the zero root.
The first pair is the pair that the first slot of the run adds: the root at the slot before the first state, or the zero root at slot zero, then the root of the first header filled with the root of the first state.
A state that hashes to the zero root leaves the header of the latest block unfilled at its slot.
So the next slot records the root of the header as it was.
The first state must be at slot zero, or have its latest header at its own slot, as after a block, or record the root of its latest header at the slot before it.
Genesis and every state that a block or a slot produces meet this, so a run may start at the state of a stored block.
`zeroPreimage_or_rootLinks_le_of_chainSteps` gives the `links` hypothesis of `RootsAbove.of_chainStep` for the last state of a run.
It takes a map from roots to a preorder that orders the parent root of each block step between the first and the last state before the root of its block, as `rootLinks_cases_of_chainSteps` computes it.
The map must also order the pairs of the first state and the first pair, and the result fails only on a zero preimage.
For one transition, `getBlockRootAtSlot_stateTransition_cases` shows that each root recorded from the slot of the state on is the parent root of the block.
The other case is that the state before the transition hashes to the zero root, and the root is that of the latest header as it was.
`getBlockRootAtSlot_stateTransition_of_lt` shows that the roots of older slots are those of the state before.

`ChainRoots` (`Consensus/Proofs/Transition/ChainRoots.lean`) says where the checkpoints of a state point, for a chain given as a predicate on slots and roots.
From an anchor slot on, each root that the state records is a root of the chain at its slot, and each checkpoint whose epoch starts above the anchor names a root of the chain at that start.
A state with the invariant agrees with every chain from its own slot on (`ChainRoots.of_invariant`).
A block keeps the agreement for the chain extended by its parent root, or, when the state before hashes to the zero root, by the root of its latest header (`ChainRoots.of_stateTransition`); slots with their upgrades keep it for the chain extended by the root of the header of the last state, and in the same zero case by the root of the first header (`ChainRoots.of_advanceSlotsAcross`).
These theorems on blocks and slots, and those on runs below, assume that the buffer of roots covers two epochs.
Along a run, the chain is the roots that the states of the run record (`ChainRoots.of_run`).
`Run.finalized_le_currentJustified` then puts the finalized block at or before the current justified block, for a map from roots that orders the links of each state of the run, when the first state has the invariant and the finalized epoch starts after the first slot of the run.
`Run.zeroPreimage_or_finalized_le_currentJustified` takes that order from `zeroPreimage_or_rootLinks_le_of_chainSteps`, so its only other case is a state between the first and the last state, by chain steps, that hashes to the zero root.
Its order on block steps covers every path of chain steps between those states, not only the blocks of the run.
This covers one chain; `accountable_safety` (`Consensus/Proofs/DirectSafety/Safety.lean`) treats two chains.
`Store.Reachable.chainRoots` (`Consensus/Proofs/ForkChoice/CheckpointBlocks.lean`) carries this agreement along the parents of each block of a reachable fork-choice store, where the chain of a block holds, at each slot, the root of its latest ancestor up to that slot.
`Store.Reachable.getCheckpointBlock_of_blockState` reads from it that each checkpoint of the state of a block after the anchor epoch, before or after justification and finalization, has the checkpoint block of that block as root, and that the store knows it.
`Store.Reachable.getCheckpointBlock_of_unrealizedJustification` gives the same for the unrealized justification of each block.
`Store.Reachable.checkpoints_known` shows that each of the four checkpoints of the store is the anchor checkpoint or names a known block.
These theorems have one other case, an anchor state that hashes to the zero root.
`Store.Reachable.finalized_ancestor_or_accountable` (`Consensus/Proofs/ForkChoice/CheckpointAncestry.lean`) ties together the two checkpoints of the store, which may come from the states of different blocks.
The finalized epoch is at or before the anchor epoch, or the finalized checkpoint is on the chain of the justified checkpoint at the first slot of its epoch.
Otherwise two runs from the anchor to the held states behind the two checkpoints bound the unslashed active stake at the anchor state by the accountable stake, or show hash evidence.
A checkpoint may come from one justification and finalization step on a held state, as fork choice runs it; `accountable_safety_justified_terminal` (`Safety.lean`) states direct accountable safety for such views.
The drift of that bound is counted from the anchor, so the bound loosens as the justified epoch moves away from the anchor epoch.
The theorem assumes that every block was imported with the setting of the signature checks of the run from genesis, and that no upgrade is due at a held slot.
It also assumes a run from a genesis built from deposits to the anchor state, and the stake floor at each held state up to one epoch past the justified epoch.

Without a collision of header roots, the pairs of consecutive slots order the roots by ancestry.
`RootsAbove.of_chainStep` then keeps each justified checkpoint below every root that the state records from its epoch on, which gives the source block of each recent link in the chain of its target block.
`slackJustifiedCheckpoints_chainRoot_of_chainSteps` (`FfgSlackActive.lean`) takes the roots themselves as the blocks of the model, ordered by the links of every state that genesis reaches (`ChainRoot`), so the order holds by construction and the step asks only the active stake.
That order does not depend on the last state, so two branches from one genesis share it.
It holds the links of every reachable state, so it also holds every collision of header roots among reachable headers, and such collisions exist by counting.
A collision of header roots makes two conflicting blocks comparable, so this order does not serve a safety theorem for two chains; that needs the order of the states of the given runs, with a named search for a collision.
`processJustificationAndFinalization_slackBits` and `advanceSlot_slackBits` (`Consensus/Proofs/Transition/FfgFinality.lean`) keep the finalized checkpoint slack-finalized through one step, by the four rules of finalization read as 1- or 2-finalization (Gasper Definition 4.9).
They carry two facts in the bits of justification: a set bit 0 gives a slack link from the previous to the current justified checkpoint, and a set bit 1 makes the checkpoint two epochs back slack-justified.
They need a buffer of roots of three epochs, which both presets have.
`slackFinalized_of_chainSteps`, `slackFinalized_activeSetAt_of_chainSteps` and `slackFinalized_chainRoot_of_chainSteps` (`FfgFinalityChain.lean`) carry this along a chain from the genesis state built from deposits, with the sets, weights and votes of the theorems on justified checkpoints.
The weights of a checkpoint then hold the effective balances of each state before a slot that ends its epoch or the next one, on a run between genesis and the last state, when that state records the root of the checkpoint for that epoch.
That genesis state exists only before Altair, so a chain whose genesis is later is out of scope.

Adding votes and allowed weights keeps slack links, justification and finalization (`Consensus/Proofs/Models/Ffg/Monotonicity.lean`).
`FfgFinalityMonotonicity.lean` puts the finalized checkpoint of a chain in such larger sets, with the same validator sets and second sets.
This does not identify validator indices or establish root ancestry across two chains.

The direct theorems of `Consensus/Proofs/DirectSafety/Safety.lean` do not go through the model.
They take two runs of the state transition from one genesis built from deposits, which share a prefix up to a state `x`.
A run keeps the inputs of each step: the slots, and the blocks with their state roots checked (`Run`, `Consensus/Proofs/Transition/Trace.lean`).
A key is accountable when the two runs accepted two of its votes that `isSlashableAttestationData` flags.
It is also accountable when a block of either tail, after `x`, applied a slashing that names it (`Accountable`, `DirectSafety/Conflict.lean`).
That slashing may be a proposer slashing, since two signed headers for one slot are slashable too.
The votes are those of the attestations that the blocks applied, read by public key in the registry before each block.
The weights are effective balances.
The reference set is the unslashed keys active at `x` (`unslashedKeys`), and the accountable keys are those of that set (`accountableKeys`).
A slashing in the shared prefix does not make a key accountable by itself.
A key that it slashed leaves the reference set and the accountable set.
The predicate `Accountable shared left right k` can still hold for such a key, but `accountableKeys` filters `unslashedKeys x`.
A prefix attester slashing can name a key without slashing it, because `slashIfSlashable` skips it.
Such a key can stay in the reference set, and it can still count through double votes or through evidence in a tail.
The stake of a prefix-slashed key is absent from the later drift and support only while its slashed flag stays set.
These theorems do not need that fact, because the drift is observed.
The flag does stay set: each step keeps every slashed flag at its position (`Frame`, `SlashedPersistence`), and the bound by sources below reads that.
Recent keys are unslashed too, and justification counts only unslashed voters, so the voters of each quorum stay inside the support (`quorum_voters_recent`, `DirectSafety/Core.lean`).
A key slashed at a call and unslashed at `x` has evidence in the tail of the call (`Run.slashed_evidence`, `DirectSafety/Evidence.lean`).
Two checkpoints conflict when the runs applied different block headers up to the first slot of the earlier of their two epochs (`Conflict`, `DirectSafety/Execution.lean`).
So, unless the roots of their headers collide, the runs disagree on the checkpoint of that epoch, even when one of the two finalized blocks is an ancestor of the other.
`accountable_safety` takes conflicting finalized checkpoints of the two last states.
The conflict implies that `x` is no later than the first slot of the earlier finalized epoch (`Run.slot_le_of_checkpointPath_ne`, `DirectSafety/Hashes.lean`).
So the theorem takes no separate premise on `x`.
Then the unslashed active stake at `x` is at most three times the accountable stake at `x`, plus twice the larger drift of the two tails.
The drift is zero when the active validators and their effective balances stay the same from the epoch before `x` to one epoch past the later finalized epoch.
Then the accountable keys hold at least one third of the unslashed active stake at `x`.
Otherwise the runs show evidence about the hash (`HashEvidence`), so no theorem assumes that the hash is injective.
The evidence is what two searches find among the objects of the runs.
`findMessageCollision` returns two different inputs of the SHA-256 node hash with one digest, read in the roots of the headers of the runs.
`findZeroRoot` returns a header or a state of the runs whose root is zero.
`hashEvidence_iff` says that the searches find something exactly when such inputs exist or such an object exists.
`findZeroRoot_valid` and `findZeroRoot_eq_none_iff` show that the zero search returns only such an object, and fails on runs that have none.
The drift of a tail is the largest over its states up to one epoch past the later finalized epoch.
At a state, it charges twice the unslashed stake at `x` that the state no longer supports, outside the keys slashed by then.
It charges once the recent stake of the state that the unslashed keys at `x` did not hold.
It charges twice the recent stake that is not active at the current epoch of the state.
It is observed, and the bound by sources below bounds it from what the run did.
The theorems need at least one slot per epoch, a buffer of roots of four epochs and more than `MIN_SEED_LOOKAHEAD + 2` epochs of RANDAO mixes.
Each run also needs an active stake above one and a half increments at epoch calls after epoch 1 through one epoch past the target horizon (`EnoughStake run high`).
The horizon is the finalized epoch of `b` for `accountable_safety`, which `ordered` makes the later one.
It is `j.epoch` for `accountable_safety_at_calls`, `accountable_safety_justified`, `accountable_safety_justified_terminal` and `accountable_justified_unique`.
A call in epoch `high + 1` can count votes targeting epoch `high`, so the floor covers that call too.
The terminal form also needs that floor at the last state of each view that takes a step.
The theorems take no bound on the fork, so a run may cross every upgrade that the transition of this revision defines, from a genesis before Altair.
`verifiedConflict_of_accountable` gives, for each accountable key, two checks of its conflicting messages.
Each is a call of `isValidIndexedAttestation` or `checkHeaderSignature` that a block of a run executed, and that accepted.
It assumes nothing about the signature checks, so it does not say who signed.

`source_safety` (`DirectSafety/SourceSafety.lean`) replaces the observed drift of `accountable_safety` by a source envelope for each tail (`sourceDrift`, `DirectSafety/IntervalBounds.lean`).
`derivedDrift_le_sources` shows that the drift of a tail is at most its envelope.
The envelope reads the reference state `x`, the balance replay of the tail up to the finalized epoch of `b`, and the largest exit cohort along the tail.
It charges twice the exits already scheduled at `x` and the unspent exit and consolidation balances.
If the window reaches Electra, it adds twice one exit churn and one consolidation rate per epoch.
From a state before Electra, it adds twice one count churn per epoch.
It charges once the validators that activate after `x` or were active only at its previous epoch, at the larger of their effective and actual balances.
If the window reaches Electra, it adds once the deposit balance left to consume at `x` and one deposit churn per epoch.
From a state before Electra, it adds once one count churn per epoch.
It charges twice the deficits of the unslashed keys active at `x`.
A deficit is the debits other than slashings beyond the balance above the effective balance, plus about one increment of rounding.
It charges once the credits of the replay that no churn limits, and twice the largest exit cohort.
For a window that reaches Electra, it charges once the balance above the effective balance at `x`.
For a window that ends before Electra, it charges each key active at `x` its excess and its deposits, at most its room below the cap.
Each tail must end before Gloas, `x` at most one epoch past the finalized epoch of `b`, and the withdrawal delay positive.
The preset must meet the parameters of `accountable_safety`, have at least two slots per epoch, order its caps and keep its largest effective balances whole numbers of increments; both presets do.
The envelope is an upper bound, and nothing says that a run attains it.
Withdrawals are debits, so a key that the withdrawal sweep reaches inside the window has a deficit of about its rewards since `x`, and is charged its rounding increment.
A payload withdraws from at most 16 keys, so over 225 epochs, about a day, at most about 115,000 keys are withdrawn from.
Then this rounding alone adds up to about 1.3% of a stake of 36 million ether to the bound, and a tighter deficit is open.
The premise on the withdrawal delay comes from the proof, which reads the invariant of pending consolidations, not from the bound.
The envelope is not yet put into the weak subjectivity margin of `accountable_safety_of_weakSubjectivityPeriod`.

### Engine API

The Engine API is the interface through which the consensus layer drives the execution layer.
`EthLib/Engine/` holds the checks of `engine_newPayload`, versions 1 to 5, and the choice of the head in `engine_forkchoiceUpdated`, versions 1 to 3.
It also holds the execution engine that the beacon chain calls.
The theorems are in `Engine/Proofs/`.

A payload and its block determine each other.
`ofBlock_toBlock` (`Proofs/Block.lean`) shows that a payload whose block hash is the hash of its header is the payload of its block.
`toBlock_ofBlock` shows that a block of the shape that a payload gives comes back from its payload.
`toBlock_shape` gives that shape: no ommers, a difficulty and a nonce of zero, and the RANDAO mix in place of the mix digest.

The checks of `engine_newPayload` answer by the version of the method and the fork of the payload.
`exists_acceptsFork_iff` (`Proofs/NewPayload.lean`) shows that some version takes a fork exactly when the fork is from Paris to Glamsterdam.
`validRequests_iff` states when the execution requests of version 4 and later pass.
Each request must have more than one byte, and their first bytes must strictly increase along the list.
`status_of_checkNewPayload` shows that a payload that fails the checks is `INVALID`, or `INVALID_BLOCK_HASH` only at version 1, with no latest valid hash.
So `status_of_newPayloadWithoutState` shows that the method without the parent's state never answers `VALID`.
One C export runs that method, and a second runs the method on a chain that holds the parent's state.
With the state of a chain, `valid_iff_of_newPayloadOnChain` shows that the answer is `VALID` exactly when a block and a state come back.
`of_newPayloadOnChain_some` adds that such a block passed the checks and the state transition, to that state.
`passesTerminalCheck_of_newPayloadOnChain_some` adds that its parent passed the terminal block check.
`newPayloadOnChain_of_stateTransition_ok` shows the converse for a block whose parent is the last block of the chain.
That parent must also pass the terminal block check of step 2 of payload validation, which a block from Paris on always passes.
The method takes the total difficulty of the last block as an input, since a chain does not record it.
`newPayloadOnChain_of_not_terminal` takes a parent of proof of work that fails the conditions of EIP-3675.
It shows that the payload is then `INVALID`, with the zero hash as the latest valid hash.
`isTerminalPowBlock_eq_isValidTerminalPowBlock` (`Proofs/TransitionConfiguration.lean`) shows that these conditions are those of the consensus layer, when both layers hold the same terminal total difficulty.
Only the last block of the chain is checked.
Step 2 also says that every descendant of an invalid terminal block must be `INVALID`.
The model keeps no invalid block, so a child of a payload rejected by the check is `SYNCING` instead.
A chain whose last block is from Paris on is taken as valid, its terminal block included.

Payload attributes of `engine_forkchoiceUpdated` answer by the version of the method and the fork of their timestamp.
`exists_attributesTakeFork_iff` (`Proofs/ForkchoiceUpdated.lean`) shows that some version takes a fork exactly when the fork is from Paris to Glamsterdam.
`attributesTakeFork_eq_true_iff` shows that a version takes such a fork exactly when it decodes the structure of the attributes at that fork.
So version 1 takes Paris, version 2 Paris and Shapella, version 3 the forks from Dencun before Glamsterdam, and version 4 Glamsterdam.
Version 0 reads as version 1, and a version above 4 as version 4.

The Engine API reads its base types with the readers that it shares with the execution JSON-RPC API.
The readers live below the Execution layer, in `Serialization/JsonRpc.lean`, and their proofs in `Serialization/Proofs/JsonRpc.lean`.
The readers read back the hex encoding of any bytes (`bytesOf_hexString`).
An address decodes exactly from `0x` and two hex digits for each byte, in either case, whose lowercase forms encode the address (`address_eq_ok_iff_map_toLower`).
A 64-bit number decodes to `x` exactly when the number read with the bound `2^64` is `x` (`uint64_eq_ok_iff`).
The encoder of numbers writes the only text that decodes to the number, at any bound `2^bits` above it (`quantity_eq_ok_iff`).
So two numbers never share an encoding (`quantityJson_inj`).
The error object of JSON-RPC 2.0 reads back from what its writer writes, whatever its data, `null` included (`rpcErrorOfJson_json`).
A withdrawal, and a list of withdrawals, decode back from their encodings (`withdrawal_withdrawalJson`, `array_withdrawal_listJson`, `Execution/Proofs/Rpc/Json.lean`).
An input that a shared reader rejects is an invalid parameter of the Engine API, for the same reason (`liftM_error`, `liftM_eq_ok_iff`, `Engine/Proofs/Json.lean`).
A payload of version 4 decodes exactly when it holds the fields of version 4 and each part decodes (`payloadV4_eq_ok_iff`).
A field that appears at a fork decodes exactly when it is present from that fork on and absent before (`exists_since_iff`, `Proofs/ExecutionEngine.lean`).
So a decoded payload takes a fork exactly when its version is that of the fork (`exists_atFork_iff_of_anyPayload`).
Version 1 takes the forks before Shapella, version 2 takes Shapella and version 3 takes the forks from Dencun.

The Engine API also writes its requests, so the specification states what a consensus node sends.
Each writer writes the canonical form of the encoding: lowercase hex, and numbers without leading zeros.
The decoder of the parameters of `engine_newPayload` reads back what their writer writes, for a version that takes the fork of the payload (`newPayloadParams_json`, `Proofs/NewPayload.lean`).
The extra data must hold at most 32 bytes, and the access list and the slot must be given exactly at version 5.
So do the decoders of `engine_getPayload`, `engine_getBlobs` and the two methods of payload bodies (`getPayloadParams_json`, `Proofs/GetPayload.lean`; `getBlobsParams_json`, `Proofs/GetBlobs.lean`; `bodiesByHashParams_json` and `bodiesByRangeParams_json`, `Proofs/PayloadBodies.lean`).
The decoder of payloads of versions 1 to 3 reads back the JSON of every payload at its fork (`anyPayload_executionPayloadJson`, `Proofs/Json.lean`).
The extra data must then hold at most 32 bytes.
The decoder of version 4 does the same from Dencun on, with the block access list and the slot number (`payloadV4_executionPayloadV4Json`).
The decoder of the forkchoice state reads back the JSON of every state (`forkchoiceStateOfJson_json`, `Proofs/ForkchoiceUpdated.lean`).
A version of `engine_forkchoiceUpdated` reads back payload attributes whose structure it takes, and they are the attributes at their fork (`payloadAttributesOfVersion_json`).
The decoder of its parameters reads back the state, and the JSON of the attributes or their absence (`forkchoiceUpdatedParams_json`).
From version 4 this holds whatever custody columns follow, and the custody columns read back too (`custodyColumnsOfJson_json`).
The theorems run the other way: a value that is written reads back.
The Python tests check the converse on examples: a request that decodes is written back as the same JSON.
They do it for the 239 requests of `tests/engine/new_payload.json` that decode, and for 17 request examples of the OpenRPC method files.
They also do it for a forkchoice state with each payload of `tests/engine/forkchoice.json` as the head, and no attributes.
The other 11 are among the 75 whose fixtures expect invalid parameters, and the decoder rejects them.
The 64 others of those 75 decode, and a later check rejects them.
Six of the OpenRPC request examples do not follow the specification, and the tests check that the decoder rejects them.
The other two examples are of methods that EthLib does not specify, and the tests check that they fail as unknown methods.

The answers have a JSON form too, written and read back.
The decoder of a payload status reads back what its writer writes, for every status and validation error (`payloadStatusOfJson_json`, `Proofs/Json.lean`).
The decoder of the response of `engine_forkchoiceUpdated` does the same for each status that the method answers (`forkchoiceUpdatedResponseOfJson_json`, `Proofs/ForkchoiceUpdated.lean`).
Every answer of that method is `VALID`, `INVALID` or `SYNCING`, the restriction of step 9 of the method (`forkchoiceUpdatedCall_status`).
So the decoder reads back the response of every call (`forkchoiceUpdatedResponseOfJson_call`).
Its response names a build exactly when the update applies a head and the attributes pass their checks (`forkchoiceUpdatedResponse_payloadId`).
The ID is then that of the head and the attributes.
The Python tests read the status examples of `engine_newPayload` and the response examples of `engine_forkchoiceUpdated` in the OpenRPC method files.
They also read back the status that EthLib answers to each request of `new_payload.json` that expects no error, and each response to the chains of `forkchoice.json`.

The result of `engine_getPayload` is read at a version of the method and the fork of its payload.
A blobs bundle reads back from its JSON exactly when it passes the length rules of its version (`blobsBundleOfJson_json_iff`, `Proofs/GetPayload.lean`).
Every bundle that decodes passes them (`blobsBundleOfJson_lengths`).
Versions 3 and 4 of the method return a bundle of version 1, and versions 5 and 6 a bundle of version 2.
Both versions of the bundle ask for one commitment per blob.
Version 1 of the bundle asks for one proof per blob, and version 2 for `CELLS_PER_EXT_BLOB`, which is 128, per blob.
From version 3, the bundle of every response passes the length rules of the bundle that the method returns (`getPayloadResultJson_bundle`).
The result of every response reads back at its version and its fork (`getPayloadResultOfJson_json`).
It holds the payload and each field of its version: the block value, the bundle, the override flag and the requests.
The method returns no payload with more than 32 bytes of extra data, the bound of the Engine API.
So `getPayloadResultOfJson_json` needs no hypothesis other than a successful call.
Hence what the execution layer writes is what the consensus layer reads.
The Python tests read back the result examples of versions 1 to 5 in the OpenRPC method files, and check each length rule.
At the pinned commit, the example of version 6 has no slot number in its payload, so the decoder rejects it.
The tests read back a result of version 6 built from the example of version 5 with an access list and a slot.

The results of `engine_getPayloadBodies` and `engine_getBlobs` are written and read in the specification (`Engine/PayloadBodies.lean`, `Engine/GetBlobs.lean`).
A body reads back from its JSON at its version, and so does each answer of each version (`bodyV1OfJson_json`, `bodyV2OfJson_json`, `payloadBodiesV1OfJson_json` and `payloadBodiesV2OfJson_json`, `Proofs/PayloadBodies.lean`).
The reader drops a field whose value is `null`.
So a missing field and a `null` field read the same, and the round trip needs no hypothesis.
A blob with its proof or with its cell proofs reads back (`blobAndProofV1OfJson_json`, `blobAndProofV2OfJson_json`, `Proofs/GetBlobs.lean`).
So do the selected cells of a blob and each answer of versions 1 to 4 (`blobCellsOfJson_json`, and `getBlobsV1OfJson_json` to `getBlobsV4OfJson_json`).
A blob with its cell proofs holds exactly `CELLS_PER_EXT_BLOB` proofs, by its type.
The selected cells decode only from two arrays of one length, with `null` at the same positions (`blobCellsOfJson_nulls`).
Step 4 of `engine_getBlobsV4` asks only that a `null` cell have a `null` proof; the reader also rejects a cell without its proof.
The writer keeps the rule by its type, which pairs each cell with its proof.
The Engine API does not give the size of a cell, so EthLib takes 2048 bytes, the size of the cells of its KZG cell proofs.
The Python tests read back every result example of `engine_getPayloadBodiesByHash` and `engine_getPayloadBodiesByRange`, versions 1 and 2, and of `engine_getBlobsV1` to `V4` in the OpenRPC method files.

`engine_exchangeTransitionConfigurationV1` of Paris exchanges the three settings of EIP-3675 that end proof of work (`Engine/TransitionConfiguration.lean`).
A configuration reads back from its JSON (`transitionConfigurationOfJson_json`, `Proofs/TransitionConfiguration.lean`).
The method succeeds exactly when the request holds one parameter that decodes as a configuration, and then answers the configuration of the execution node (`exchangeTransitionConfiguration_eq_ok_iff`).
So a successful answer never depends on the configuration in the request, as step 1 of the method says.
What the method leaves to clients is not modelled: reporting a mismatch to the user, polling every 60 seconds, warning after 120 seconds without a request, and whether the method still answers after Cancun.
The undecided terminal total difficulty of step 7, `2^256 - 2^10`, is a named constant.
EIP-3675 gives the mainnet terminal total difficulty but no mainnet terminal block hash or number, so EthLib gives no mainnet configuration.
The Python tests run the OpenRPC example, the undecided total difficulty, a block number of 0, malformed and missing fields, the wrong number of parameters, another method, and a configuration out of range.

`engine_exchangeCapabilities` and `engine_getClientVersionV1` tell each layer which methods and which program the other runs (`Engine/Capabilities.lean`).
Each method succeeds exactly when its one parameter decodes, and then answers what the execution node holds, whatever the request says (`exchangeCapabilities_eq_ok_iff` and `getClientVersion_eq_ok_iff`, `Proofs/Capabilities.lean`).
The parameters of `engine_exchangeCapabilities`, and a version object with a two-letter code, read back from their JSON (`exchangeCapabilitiesParams_json` and `clientVersionOfJson_json`).
A version object decodes only with a code of two ASCII letters (`isClientCode_of_clientVersionOfJson`), in either case, since the source states no rule on the case.
Which methods a node supports is its own choice, so the method takes the list to answer.
EthLib fixes one table, the last version of each method that it defines, and builds from it the list of every version of each; the C exports read the versions of their methods from it (`methodVersion_eq_some_iff`).
Every name in it has the form `engine_`, a method, `V` and a positive version, and no name appears twice (`isVersionedMethod_specifiedMethods`).
So it does not hold `engine_exchangeCapabilities`, as step 3 of that method requires (`exchangeCapabilities_not_mem_specifiedMethods`).
It holds a method at a version exactly when EthLib defines that method up to that version (`mem_specifiedMethods` and its corollaries for each method).
The decoder of `engine_exchangeCapabilities` takes any string as a name, since the source does not say how to treat a request name without a version.
What the methods leave to clients is not modelled: when to call them, logging, the reserved client codes, and the arrays that a multiplexer joins.
The Python tests check the shape of the answer to the OpenRPC request of `engine_exchangeCapabilities`, whose example result is one client's list, and the full list that EthLib answers.
They also run the example version and commit of `ClientVersionV1`, codes in either case, malformed and missing fields, and the wrong number of parameters.

The theorems about `engine_forkchoiceUpdated` are in `Proofs/ForkchoiceUpdated.lean`.
`forkchoiceUpdated_valid` shows that a valid answer selects a valid head that the execution layer holds, with its safe and finalized blocks on its chain.
The chain of that head also passes the terminal block check, and its safe and finalized hashes are not zero after the transition.
The exception is step 2 of the method, which `forkchoiceUpdated_of_belowFinalized` covers.
`onChain_of_forkchoiceUpdated` shows that an applied head is the head that the state names, and `mem_chainOf_of_onChain` that a nonzero safe or finalized hash then names a block of its chain.
A valid head below the finalized block that the execution layer knows, whose chain passes the terminal block check, is `VALID` there, and the head does not change.
`forkchoiceUpdated_of_invalid` gives the answer for an invalid head, and `latestValid_eq_some_iff` with `getElem?_succ_chainOf` shows that its latest valid block is the valid ancestor nearest the head.
That block gives the latest valid hash, which is zero when the block is of proof of work, as step 3 of payload validation requires (`latestValidHash_eq_some_iff`, `latestValidHash_spec`).

The tree that the execution layer knows may hold blocks of proof of work, each with its total difficulty and that of its parent.
The most recent block of proof of work on the chain of the head, the head included, must be terminal by the conditions of EIP-3675.
Step 3 of the method asks this of a head of proof of work, and step 2 of payload validation of a payload.
`forkchoiceUpdated_of_not_terminal` shows that a head whose chain fails the check is `INVALID`, with the zero hash, and that the head does not change.
`forkchoiceUpdated_of_pow_not_terminal` states the same for a head of proof of work that is not terminal, and `forkchoiceUpdated_of_parent_not_terminal` for a payload whose parent is such a block.
The model lets a chain with no block of proof of work in the tree pass the check.
It assumes such a chain is past the transition; the source would ask for the missing blocks first.
The check runs before step 2 of the method, so a head below the known finalized block must pass it too, since step 2 applies only to a valid block.
The forkchoice state allows zero safe and finalized hashes only until the transition block is finalized.
The model takes that block as finalized when the finalized block that the execution layer knows is a payload of the tree.
The finalized hash of the request itself does not count.
`forkchoiceUpdated_zero_after_transition` shows that a zero safe or finalized hash then gives `-38002`.
No step of the method names that error for this case, so the model reads it as an invalid forkchoice state of step 9.
In version 4, custody columns that decode never change the answer (`forkchoiceUpdatedCall_custody`), and without payload attributes every version gives the same answer (`forkchoiceUpdatedCall_of_null`).
`checkAttributes_eq_ok_iff` states when attributes pass their checks against the head: the version takes their fork, their structure is that of the fork, and their timestamp is above the head's.
A fork that the version does not take gives `-38005` (`checkAttributes_eq_error_of_unsupportedFork`).
A structure that is not that of the fork, or a timestamp not above the head's, gives `-38003` (`checkAttributes_eq_error_of_wrong_structure`, `checkAttributes_eq_error_of_not_after_head`).
When the update applies a valid head, attributes whose fields fit no structure of the version give `-38003` (`forkchoiceUpdatedCall_eq_error_of_attributes`, with `payloadAttributesOfVersion_eq_error_iff` and `payloadAttributesOfJson_wrong_fields`), and when it applies none they are not read (`forkchoiceUpdatedCall_of_no_head`).
Version 1 names no code for a wrong structure, and the model gives it `-38003`, the answer of its step 9 for invalid attributes.
The OpenRPC description of the method makes the payload attributes optional, but the model asks for them, as `null` when there are none.

`executionEngine_accepts_iff` (`Proofs/ExecutionEngine.lean`) states when the execution engine accepts a payload request of the beacon chain.
The request lists must be well formed, and the payload must have a block at the active fork of the chain, which must be before Glamsterdam.
From Deneb, the blob transactions of that block must carry the versioned hashes of the request.
The block must pass the state transition.
`executionEngine_accepts_newPayloadRequest_iff` states the same for the payload request of a block, from Bellatrix to Fulu, in terms of the block and the state.
From Electra, the request lists are those of the requests of the block.
From Deneb, the block of the payload reads the parent root of the latest block header of the state.
From Deneb, the blob transactions must carry the versioned hashes of the commitments of the block, in the order of the commitments.
The consensus test vectors fix the answer of the execution layer, so none of them checks the versioned hashes or the parent root that a block puts in its request.

Between the two clients of a node, a payload request travels as the JSON parameters of `engine_newPayload`, which `newPayloadRequestJson` writes.
It writes the payload with the fields of the structure for the fork of the beacon chain, then the values of the version that the beacon chain calls there.
`newPayloadOnChain_valid_iff_accepts` (`Proofs/ConsensusRoute.lean`) shows that, from Bellatrix to Gloas, the method on a chain answers `VALID` for that JSON exactly when the execution engine of the beacon chain accepts the request.
Besides the fork range, its one hypothesis is that the last block of the chain passes the terminal block check, which only the method makes.
The chain needs no hypothesis on the parent: without the parent as its last block, the method answers `SYNCING` or refuses earlier, and the state transition of the execution engine fails, so neither route accepts.
An execution that aborts gives `SYNCING` on one route and a refusal on the other, so it is not accepted either.
The JSON is part of the statement, so the execution engine accepts no request that has none.
The Python tests take the 175 vectors of `tests/engine/new_payload.json` that expect no JSON-RPC error.
They stop before execution, since the vectors hold no parent state.
Of these, 155 are requests that the beacon chain can form, and the JSON that EthLib writes for each is the vector itself.
For each, the method passes the checks before execution exactly when the execution engine accepts with the state transition taken as passed.
The 20 others hold request lists that the beacon chain never sends: empty, of an unknown type, out of order or repeated, or of a length that is no whole number of requests.

Between the two clients of a node, the consensus layer sends its payload attributes as JSON.
`forkchoiceUpdatedCall_payloadAttributesJson` (`Proofs/ForkchoiceUpdated.lean`) shows that the execution layer reads back the values sent.
It holds for any attributes, given a forkchoice update that applies the head of its forkchoice state.
The method then answers with that head and with attributes at the fork of the next block, which carry every value of the attributes sent.
The hypotheses are the checks of the attributes against the head: the active fork at the next number and the timestamp is a fork that the version takes.
That fork must have the structure of the fork of the attributes, and the timestamp must be above the head's.
The fork of the attributes and that of the next block can differ, as Bellatrix and Paris do, so the theorem compares their structures.
`forkchoiceUpdatedCall_payloadAttributesJson_of_gloas` states the same from Gloas at version 4, where the checks reduce to the next block being of Glamsterdam and the timestamp being above the head's.

The tree of known payloads and the known finalized block are inputs of each call, not state that the model keeps between calls.

### Execution JSON-RPC API

The execution JSON-RPC API is the interface through which wallets, indexers and test suites read an execution node.
EthLib follows commit [`3284ee8`](https://github.com/ethereum/execution-apis/tree/3284ee80c3da3e516c53782dde75157cccf1ebdc) of `ethereum/execution-apis`, which is ahead of release `v1.0.0-beta.7`.
The definitions are in `Execution/Rpc/`, and the theorems in `Execution/Proofs/Rpc/`.

Each reader of a base type reads back what its writer writes.
A number of any size reads back from its quantity, and that quantity is the only text that reads as it (`uint_quantityJson`, `uint_eq_ok_iff`, `Serialization/Proofs/JsonRpc.lean`).
A byte reads back from the hex digits of its value (`byte_byteJson`).
The schema of a byte also admits a leading zero, so `0x05` reads as the byte 5 but no writer writes it.
A decimal number reads back from its decimal digits (`uintDecimal_uintDecimalJson`).
A 32-bit and a 256-bit number read back from their quantities (`uint32_quantityJson`, `uint256_quantityJson`).
A storage slot, a number on 32 bytes, reads back from the hex of its 32 bytes (`bytesMax32_dataJson`).
The schema also admits fewer than 64 digits, so `0x1` reads as slot 1 but no writer writes it.

A block parameter names a block by its number, by a tag, or by its hash.
A number or a tag reads back from the writer (`blockNumberOrTag_number`, `blockNumberOrTag_tag`), and a range reads back every number (`blockNumberOrTagForRange_number`) and every tag but `pending` (`blockNumberOrTagForRange_tag`), which it rejects (`blockNumberOrTagForRange_pending`).
The schema for a number, a tag or a hash is an `anyOf`, so a string of 64 hex digits whose first digit is not `0` matches both a number and a hash.
The official fixtures read such a string as a hash, so the reader tries a hash first (`blockNumberOrTagOrHash_hashString`).
A tag, and a hash in the object of EIP-1898, read back (`blockNumberOrTagOrHash_tag`, `blockNumberOrTagOrHash_hash`).
A number reads back when its text is no hash (`blockNumberOrTagOrHash_number`), which holds below `2^252` (`hash32_quantityJson_of_lt`).

The request and the response objects of JSON-RPC 2.0 read back from their writers (`request_requestJson`, `response_responseJson`), a result of `null` included, and so does the identifier of a request (`requestId_requestIdJson`).
The error codes of the source come in groups.
Every code of a group that declares a range lies in that range (`code_mem_range`, `Proofs/Rpc/Errors.lean`).
No code appears twice (`codes_nodup`), and the code `4444` of pruned history is in no group (`prunedHistoryUnavailable_not_mem`).
The messages of the groups are not fixed: the official fixtures show other texts.

A query reads a *chain view* (`Execution/Rpc/View.lean`): the blocks that a node holds, with their states, receipts and logs.
`ChainView.Valid` says that the view follows the state transition.
Each block's hash is the hash of its header, and each canonical block after the lowest is what the transition and the body give on the chain before it.
The state of the lowest block and the recent blocks before it are inputs.
`Valid` asks only that this state have the state root of the lowest header, and that the last recent block be its parent.
The blocks off the canonical chain are checked for their hash and their fork only, so their states are trusted inputs.
The pending block is checked for its hash, its parent, its number and its fork; its contents are the node's choice.
A number resolves only to a canonical block of that number, and a hash only to a block of that hash (`resolve_number`, `resolve_hash`); with `requireCanonical`, only to a canonical one (`resolve_hash_canonical`).
In a valid view, every number from the lowest block to the head resolves (`Valid.resolve_number`), and the state of each canonical block has the state root of its header (`Valid.stateRoot_eq`).
Take a forkchoice update that sets a new head, and a view whose canonical chain is the chain of that head.
The head of the view is the head of the update (`head_hash_of_forkchoiceUpdated`, `Engine/Proofs/RpcView.lean`).
The view resolves `safe` and `finalized` to the blocks that the update named, when their hashes are not zero (`resolve_safe_of_forkchoiceUpdated`, `resolve_finalized_of_forkchoiceUpdated`).
A notification gets no response (`answerJson_notification`).

`eth_config` reports the current, next and last scheduled configurations of EIP-7910 (`Execution/Rpc/Config.lean`).
The current configuration is the last one the head has reached.
The next and last are those of the first and last fork times after the head whose forks the node supports, or both null when there is none (`ChainView.configReport_eq_ok`, `mem_configFutureTimes`, `ChainView.configReport_next_eq_none_iff`, `ChainView.configReport_current_le`, `ChainView.configReport_next_after`, `ChainView.configReport_last_after`).
The reported fork ID is the EIP-6122 `FORK_HASH` that the node announces at that configuration's activation (`configObject_forkId`, `Proofs/Rpc/Config.lean`).
The block that represents the Merge in the fork ID is an explicit input, distinct from the actual Paris activation block.
The report's precompile addresses are exactly those that transaction processing warms (`configObject_precompiles`).
Its blob schedule is `chainBlobSchedule` at the configuration's activation (`configObject_blobSchedule`).
The named BPO forks keep Osaka's precompile names and system contracts (`configPrecompiles_bpo`, `configSystemContracts_bpo`).

The precompile names through Osaka and the system-contract sets through Prague follow EIP-7910 at the pinned EIPs commit.
The Amsterdam set also lists the builder deposit and exit contracts of EIP-8282, whose constants name both addresses.
No meta-EIP at that pin lists the system-contract set after Prague.

The method declines reports before Cancun, and fails when the head is after Amsterdam, since no meta-EIP defines that report.
A fork scheduled after Amsterdam is one that the node does not support, so the report leaves it out.
When no supported fork remains, `next` and `last` are null, as EIP-7910 says.
It rejects a chain ID of zero.
A fork from Cancun on that activates at a block after genesis has no known time, so it is never a next or last configuration, as EIP-7910 says.
The method fails when such a fork is the current one, which cannot be left out, or when the head has not reached its block, on which the fork IDs depend.
It requires each chain blob schedule to start at genesis or at a fork time, as EIP-7892 ties each schedule to a fork.
It requires the head to have passed every fork block, so that each reported fork ID is the one of its activation.
It requires genesis context, which the export infers from block zero or reads as an input for a pruned chain.
For a pruned chain that context is trusted, and no theorem ties it to the retained blocks.

A signed transaction of every kind reads back from its JSON form (`transactionOfJson_transactionJson`, `Proofs/Rpc/Transaction.lean`).
A typed transaction holds its parity as a 256-bit number, while the schema types it as a byte, so the round trip asks that parity to be below 256.
That bound holds for every transaction whose signature names a sender (`parityIsByte_of_recoverSender`).
The object that the methods return reads back as its transaction too (`transactionOfJson_transactionInfoJson`).
The object of a transaction of a block holds the context of that block, the sender that its signature names, its hash, and its effective gas price at the base fee of the block (`BlockRecord.transactionInfo_eq_ok`, `Proofs/Rpc/TransactionInfo.lean`).
A lookup by hash returns only that object for a transaction of that hash, at its index in a block that the node holds (`transactionByHash_some`).
It reads a canonical block whenever one has such a transaction (`transactionByHash_canonical`), and finds nothing only when no block of the node has one (`transactionByHash_none`).
A lookup by block and index returns the object of the transaction at that index of the block that the parameter names (`transactionByBlockAndIndex_some`), and finds nothing exactly when that block is unknown or too short (`transactionByBlockAndIndex_none`).
In a valid view, take a canonical block after the lowest.
Its run started from the state of the block before, reached each of its transactions after those before it, and the inclusion check passed there.
The sender and the gas price of the object are those that this check gave (`Valid.transactionInfo_inclusion`).
The state transition calls the inclusion check, not the check of a transaction alone; both name the sender by the same recovery of the signature.
The lowest block, the blocks off the canonical chain and the pending block do not run, so their senders are recovered but not tied to a transition.

The header object holds the hash of a header and each of its fields, and the reader of its fork reads the header back (`headerOfJson_headerJson`, `Proofs/Rpc/Header.lean`).
Its names are exactly those of the fork (`keys_headerJson`, `names_headerFields`), so a field from a later fork never appears.
No name comes twice (`nodup_headerNames`), and there is one name more than the RLP form of the header has items (`length_headerNames`).
The schema requires none of the fields from a fork, so they stay optional after their fork too.
The object writes each one exactly from its fork on, as the fixtures do.
Only this direction of the round trip holds: the reader also takes a beneficiary in uppercase hex, and it ignores a field whose value is `null`.
The methods write the object with the hash that the view keeps for the block, so they compute no hash.
The header of `pending` is `null` (`headerByNumber_pending`), and any other block parameter gives the header of the block that it resolves to, or `null` for none (`headerByNumber_of_ne`).
In a valid view, the object of each block that the node holds is what the writer gives, so the theorems above apply to it (`Valid.headerJson_eq`).

The block object has exactly the names of the header object of its fork and `size`, `uncles`, `transactions` and, from Shapella, `withdrawals` (`keys_blockJson`, `Proofs/Rpc/Block.lean`).
No name comes twice (`nodup_headerNames_append_blockNames`).
On each name of the header, the block object of a block holds what its header object holds (`getObjVal_blockJson`).
The block object lists the transactions by their hashes, or by their objects when they are hydrated (`transactions_blockJson_false`, `transactions_blockJson_true`).
The objects carry those hashes in the same order (`transactionHashes_of_transactionInfos`).
Each list has one entry per transaction of the block (`length_transactionInfos`, `length_transactionHashes`), and the transaction count methods return that length by definition.
The `size` of the block object is the length of the RLP form of the block, in bytes, which the raw block method returns for the same block (`size_blockJson`).
Its `uncles` lists the hashes of the headers of its ommers, in order (`uncles_blockJson`).
These properties hold whenever the writer gives an object.
The writer fails with `-32603` when the node cannot compute the RLP form of the block, the hash of an ommer or a transaction, or a sender in it.
In a valid view, the writer gives the object of a canonical block after the lowest exactly when that block has an RLP form (`Valid.exists_blockJson_eq_ok_iff`).
Before Fusaka no check bounds the length of the RLP form of a block, and the RLP encoder fails on a payload of `2^64` bytes or more, so that form stays a hypothesis.
From Fusaka the size check of the block gives that form, of at most `8 * 2^20` bytes (`Valid.exists_rawBlock_of_fusaka_le`, `Valid.exists_blockJson_of_fusaka_le`).
A valid view does not run the lowest block, a block off the canonical chain or the pending block through the state transition.
So no theorem says that the writer succeeds on them.
For the tag `pending`, the header method answers `null`.
The block and count methods read the pending block of the view instead, since only the header methods of [`block.yaml`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/block.yaml) answer `null` for `pending`.
The schema gives `size` only the title "Block size"; here it is the length of the RLP form of the block, which the fixtures pin.

The raw getters of [`getters.yaml`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/debug/getters.yaml) return the consensus encodings of a header, a block, a transaction and the receipts of a block (`Execution/Rpc/Raw.lean`).
The bytes of a transaction hash to the hash that names it in the request (`keccak256_rawTransaction`, `Proofs/Rpc/Raw.lean`).
In a valid view, the raw header that the getter returns hashes to the hash that the node keeps for its block, and decodes back to the header (`Valid.rawHeader_eq_ok`, `Valid.rawHeader`).
The header and block objects report that hash (`getObjVal_hash_headerObject`, `getObjVal_blockJson`), so the raw header hashes to the hash of the block object (`Valid.hash_blockByNumber_rawHeader`).
The raw block decodes back to the block, with each transaction as its item in a body, when each ommer is at the fork that the decoder gives its own number (`decode_rawBlock`).
A valid view does not check the fork of an ommer against the schedule of the chain, so that condition is a hypothesis.
In a valid view, the raw receipts of a canonical block after the lowest have the receipts root of its header (`Valid.rawReceipts_eq_ok`, `Valid.rawReceipts_root`).
The receipts of the lowest block, of side blocks and of the pending block are inputs of the view, so no theorem ties them to a header.
No result schema of the getters allows `null`.
Here an unknown block or transaction gets `-32001`, the code that the getter of a block access list in the same file requires for an unknown block.

The block access-list methods of those same API files return the JSON list or its EIP-7928 RLP bytes (`Execution/Rpc/AccessList.lean`).
The JSON writer keeps all six account fields, including empty arrays, and writes storage keys and values as 32-byte data.
Every list reads back from its JSON form (`blockAccessListOfJson_blockAccessListJson`, `Proofs/Rpc/AccessList.lean`).
`ChainView.blockAccessList_eq_ok_iff` identifies the resolved record and its retained list for every successful non-pending JSON query, or the unknown block that gives `null`.
`ChainView.rawBlockAccessList_eq_ok_iff` identifies the resolved record, its retained list and its RLP encoding for every successful raw query.
For a non-pending query, successful JSON and raw answers both read back as the retained list of the resolved block (`ChainView.blockAccessList_forms`).
In a valid view, the raw answer for a canonical block after the lowest hashes to the `blockAccessListHash` of its header (`Valid.rawBlockAccessList_hash`).
The proof uses the list built by execution and the state transition's check of its hash.
`Valid.blockAccessList_answers` proves that both methods succeed when a non-pending query resolves to such a block with a retained list.
`Valid.check_accessList` derives the retained list's order, uniqueness and gas-limit checks from execution.
`call_blockAccessList` and `call_rawBlockAccessList` connect the public RPC method names to the view methods after parameter decoding.
`Valid.call_blockAccessList_answers` proves that both dispatched replies recover the checked retained list and that the raw bytes hash to its header.
The lowest block, side blocks and the pending block are inputs, so that hash guarantee does not cover their retained lists.

An unknown block gives `null` to `eth_getBlockAccessList` and `-32001` to `debug_getRawBlockAccessList`.
Both reject a block before Glamsterdam with `-32001`, and a missing retained list from that fork with `4444` (`retainedAccessList_of_lt`, `retainedAccessList_pruned`).
The JSON method always gives `null` for `pending` (`blockAccessList_pending`).
The source leaves `pending` open for the raw getter; it reads the pending record, as the other raw getters do.
The binding retains the list of each block it executes; the lowest block has no retained list.
Its `pruned_access_lists` argument removes lists at named block numbers while keeping the blocks.
`encode_block_access_list` reads a JSON list under the same schema and returns its RLP bytes, so callers can check a JSON answer against a header hash.
It does not check the order of the list, so only a list in canonical order gives the hash of the header.

The receipt methods return the object `ReceiptInfo` of [`receipt.yaml`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/receipt.yaml), with its logs as objects `Log` (`Execution/Rpc/Receipt.lean`).
The receipt objects of a block are one for each receipt, in order, each built from its transaction and its receipt (`receiptInfos_eq_ok`, `receiptInfo_eq_ok`, `Proofs/Rpc/Receipt.lean`).
Their logs are numbered `0, 1, 2, …` across the block (`logIndex_receiptInfos`), and the lookup of one receipt returns the object at its index among those of its block (`transactionReceipt_eq_ok`).
In a valid view, when that block is canonical, it is the object at that index among the receipts of the number of the block, so both methods give each log the same `logIndex` (`Valid.transactionReceipt_blockReceipts`).
A block off the canonical chain is checked for its hash only, so a receipt found there has no such guarantee.
A creation has the address that the sender makes at its nonce, and a call has none (`receiptInfo_contractAddress`).
A receipt object has `blobGasUsed` and `blobGasPrice` exactly for a blob transaction (`receiptInfo_blob`).
It reports `2^17` blob gas for each versioned hash.
From Dencun, its blob gas price is the base fee per blob gas that the blob schedule of the chain, at the fork, number and timestamp of the block, gives for the excess blob gas of its header.
No text of a receipt or a log defines `logIndex`; the section "Log index" of the [notes of `eth_simulateV1`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/docs-api/docs/ethsimulatev1-notes.mdx) states the rule and says that receipts use it.
These properties hold whenever the receipt objects of a block are built.
They fail with `-32603` when a block does not have one receipt for each transaction, or when the node cannot compute a sender, a hash or a contract address.
No theorem yet shows that they succeed on the blocks of a valid view.
From Byzantium, the outcome of a receipt object is a status, `true` exactly when the receipt is a success (`outcomeOf_of_byzantium`), which the object writes as `status` `0x1`; before Byzantium it is the state root, which the object writes as `root` (`outcomeOf_of_lt_byzantium`).
In a valid view, take a canonical block after the lowest.
Each receipt has the Bloom filter of its logs, and so does each receipt object (`Valid.bloom_receipts`, `Valid.logsBloom_receiptInfos`).
The cumulative gas of its receipts never decreases (`Valid.cumulativeGasUsed_receipts`), so the gas of the receipt objects adds up to the last cumulative gas (`Valid.sum_gasUsed`).
The base fee of the block is at most the maximum fee of each transaction (`Valid.baseFee_le_maxFeePerGas`).
So the effective gas price of each receipt object follows the formula of the description, read in integers (`Valid.effectiveGasPrice_receiptInfos`, `effectiveGasPrice_description`).
The run of the block reaches each transaction, and on the state that the transaction starts from its sender can buy the gas (`Valid.buyGas_receiptInfos`).
Buying it lowers the balance of the sender by exactly the gas limit of the transaction times `effectiveGasPrice`.
A blob transaction also pays `blobGasUsed` times `blobGasPrice`; other types add nothing (`receiptInfo_blob`).
The theorem states the purchase on that state; that the run of the transaction starts with it rests on the proof, not on the statement.
From Glamsterdam, EIP-7778 makes the cumulative gas of a receipt the gas that the senders paid.
As a choice of EthLib, the object copies it, so `gasUsed` is the gas that the sender paid, while the descriptions of `receipt.yaml` read "gas used".

`eth_getLogs` reads the logs that a filter of [`filter.yaml`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/filter.yaml) selects (`Execution/Rpc/Filter.lean`).
A filter names one block by its hash, or a range of canonical blocks by its bounds, and then the addresses and the topics at each position that it takes.
A range is valid exactly when its bounds resolve to numbers in order, the first at least the lowest block and the last at most the head (`filterBlocks_range_eq_ok_iff`).
It then reads exactly the canonical blocks between its bounds.
A number bound above the head makes the range invalid, whatever the other bound, as the method requires (`filterBlocks_aboveHead`).
So do bounds that resolve above the head or out of order, whatever the pruned history (`filterBlocks_invalid`).
So two equal bounds between the lowest block and the head are valid, and so is a last bound at the head, as the inclusive range of the method requires.
A block hash reads the one block of that hash (`filterBlocks_hash`).
The returned logs are the matching logs of the receipt objects of those blocks, in block order, then in their order in each block (`getLogs_eq_ok`).
Every returned log matches the filter and is a log of a receipt object of a block that the filter reads (`getLogs_sound`).
When the method answers, every such log that matches is returned, and so is every matching log of the receipts of those blocks (`getLogs_complete`, `getLogs_complete_log`).
In a valid view, take a canonical block after the lowest.
The logs of its receipts are its logs (`Valid.logs_receipts`), and the Bloom filter of its header is that of its logs (`Valid.logsBloom_eq`).
So the block has no log that a filter selects when its Bloom filter has none of the addresses of a nonempty list that the filter takes, or none of the topics of a nonempty list that the filter takes at some position (`Valid.not_selects_of_bloom`).
The source leaves several cases open: a block hash with a bound, an empty topic list at a position, an empty address list, a log with fewer topics than the filter, an omitted bound, the order of the results, a block below the lowest one (`4444` here) and an unknown block (`-32001` here).
The module header gives the choice for each, and follows the official fixtures where they decide.
A log with fewer topics than the filter has positions does not match, even when each extra position takes any topic (`Filter.selects_eq_false_of_length_lt`).
No fixture filter ends with a position that takes any topic, and no text of the source decides the case.

The account queries of [`state.yaml`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/state.yaml) read the state after the block that their parameter names, `latest` by default (`Execution/Rpc/Account.lean`).
`eth_getStorageValues` gives, for each key of each address of its request, the word that `eth_getStorageAt` gives for the same block (`storageValues_agree`).
An address with no account has balance and nonce zero and empty code (`balance_of_none`, `nonce_of_none`, `code_of_none`), as the fixtures expect, though no text states it.

`eth_call` of [`execute.yaml`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/execute.yaml) runs the message of a transaction on the state after a block, and commits nothing (`Execution/Rpc/Call.lean`).
The request is a `GenericTransaction`, whose fields are all optional and which has no field outside its schema.
A field of the schema whose value is `null` counts as absent.
The call prepares its message with the steps of a transaction, then runs it with `processMessageCall`, the function that the state transition runs.
`runTransaction` takes the same steps as `transactionStart` once it has bought its gas (`runTransaction_eq_transactionStart`), so a change to one breaks the build.
It answers data exactly when that message ends without an error, and that data is the output of the message (`ethCall_eq_ok_iff`, `Proofs/Rpc/Call.lean`).
It answers the revert error, code 3, exactly when the message reverts, and the data of that error is the output of the revert (`ethCall_eq_revertError_iff`).
The message runs on the state after the block that the request names, from the sender to the recipient (`prepareCall_message`).
It carries the value of the request, and the input of the request as its data when it has a recipient.
A request that names no fee takes no wei from its sender before its message (`prepareCall_balance_of_namesFee_false`).
Such a request, from a sender that holds its value, never fails with code 809 (`ethCall_ne_insufficientFunds`).
Since it pays no fee, that is how EthLib meets the rule of the source.
A sender that holds less than the value of its request gets no data (`ethCall_ne_ok_of_balance_lt_value`).

The source leaves most of the call to the node, and `CallChoices` takes those choices as one input:

- the fork and the block environment of the call, by default those of the header of the named block;
- the gas limit of a request that names none, by default the gas limit of that environment;
- the price per gas that the code sees when the request names no fee, by default 0;
- the sender of a request without `from`, by default the zero address.

The dispatcher serves `eth_call` with the default choices.
The other rules are choices of EthLib, and the header of `Execution/Rpc/Call.lean` lists them.
A request that names no fee pays none, and runs with a base fee of 0, as the fixture `call-callenv.io` expects.
A request that names a fee buys its gas with `buyGas`, as a transaction does, and the sender must hold that fee plus the value.
A transaction must hold its fee at its caps instead, and its blob fee cap is checked; a call checks neither.
The type must be active at the fork of the call, and the gas limit must cover the intrinsic gas and, from Pectra, the floor of EIP-7623.
The checks of the blobs, of the authorization list and of a sender with code do not run, and neither the nonce of the request nor that of the sender is checked.
The default gas limit is that of the block, which may exceed the cap of EIP-7825.
The hashes that BLOCKHASH reads are those of the canonical blocks that the view holds.
They leave out the blocks of the history, and they are not the ancestors of a block off the canonical chain.
A revert has the message `"execution reverted"`, the only text that the source gives, though the fixtures append the reason.
A halt that is not a revert has code 801 for a lack of gas, 4 for an invalid opcode, and `-32000` otherwise.
The error groups of the source define these codes, but no text assigns them to `eth_call`.

`eth_estimateGas` and `eth_createAccessList` run the same call as `eth_call`, with the same choices (`Execution/Rpc/Estimate.lean`).
Their block parameter is `latest` by default, as for `eth_call`.
Of the three methods, the source states that default only for `eth_call`.

The source asks `eth_estimateGas` only for "an estimate of how much gas is necessary to allow the transaction to complete".
EthLib answers a gas limit with which the call completes, which means that the call prepares and its message neither reverts nor halts (`Completes`).
The method fails exactly when `eth_call` fails, with the same error, and this includes the revert of code 3 (`estimateGas_eq_error_iff`).
Otherwise it runs a binary search below the gas limit of the request, or below the default one.
The estimate has no cap from EIP-7825.
When the request names a fee, the sender must hold the fee of its whole gas limit.

The answer completes and is at most the gas limit of the request, or the default one (`estimateGas_completes`, `Proofs/Rpc/Estimate.lean`).
It is the least positive limit that completes when the limits that complete form an interval (`estimateGas_least`).
Code that reads the gas left can break that hypothesis, and the answer may then not be the least.
Even without the hypothesis, the call does not complete with one gas less, unless the answer is at most 1 (`estimateGas_pred_not_completes`).
A call completes with a gas limit exactly when `eth_call` answers data at that limit (`completes_iff`).

The source fixes none of the contents of the result of `eth_createAccessList`.
EthLib lists each address and storage key that the call read or wrote, as the state tracker records them, a revert included.
It leaves out an address without a storage key that the transaction accesses from the start.
These addresses are the sender, the recipient or the created contract, the precompiles and, from Shapella, the beneficiary.
The list keeps the authorities and the delegate of EIP-7702, and the contracts that the code of the call creates.
EIP-2929 and EIP-7702 make these addresses warm, but they stay in the list.

The method then runs the call again with that list, as type 1 when the request has type 0.
Before Berlin no transaction has an access list, so the list is empty and the call runs once.
The result reports the gas used and the error message of that second call (`createAccessList_eq_ok`).
A rejection of the second call, such as a gas limit that no longer covers the list, is the error of the method.
The list is not iterated to a fixed point, so a call whose accesses change with its access list can report a list that the second call does not match.

`eth_simulateV1` of [`execute.yaml`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/execute.yaml) runs calls in a sequence of blocks on top of a base block (`Execution/Rpc/Simulate.lean`).
EthLib specifies its request, the checks before the execution, and the simulated blocks.
The reader rejects a key outside the schema of block or account overrides (`blockOverrides_unknown_key`, `accountOverride_unknown_key`, `Proofs/Rpc/Simulate.lean`).
It rejects an account override with both `state` and `stateDiff`, even when one is `null` (`accountOverride_state_and_stateDiff`).
A rejected override rejects the whole request (`simulatePayload_rejects` and the lemmas before it), with code `-32602` (`call_simulate_rejected`).
Each block keeps the number and the time that the request gives it (`planBlocks_number`, `planBlocks_time`).
Without these overrides, the order check passes (`checkOrder_planBlocks_of_none`).
It passes exactly when the numbers and the times strictly increase from the base block, gap blocks included (`checkOrder_planBlocks_iff`).
An account override sets each field that it gives, and keeps the others (`applyAccountOverride_nonce` and the lemmas after it).
`stateDiff` keeps the slots that it does not name, and `state` clears them (`applyAccountOverride_stateDiff`, `applyAccountOverride_state`).
The overrides of a block keep every account that they do not name (`applyOverrides_not_mem`), and act on each account they name as its override alone (`applyOverrides_mem`).
A call fills its defaults: its type, its nonce, its gas and the zero address as sender.
Filling them keeps every field that the call gives, and changes no other field (`GenericTransaction.withDefaults_type` and the lemmas after it).
The nonce is that of the sender after the earlier calls, and the gas is what the block has left.
The execution core takes four exceptions of a simulated block as optional overrides, whose defaults leave a real block unchanged.
They are a sender given in place of the signature, the precompile that a call to each address runs, a base fee per blob gas that the block sets, and rules of a transaction that the simulation lifts.
The lifted rules are the nonce check, the caps at `2^24` of EIP-8037, its cap at `2^32 - 1` on the gas limit, and the base fee of a transaction whose fee cap is 0.
A known sender that the signature names, and that passes the rule on its code, gives the same check of the transaction (`checkInclusion_of_knownSender`, `Proofs/Transactions/Overrides.lean`).
With the default map, a call runs the precompile at the address of its code (`precompileAddress_of_default`).
A move leaves the addresses that are warm at the start of a transaction unchanged, as the notes say.
Without a price that the block sets, the excess blob gas gives the base fee per blob gas (`blobBaseFee_of_none`).
Without the gas caps lifted, the gas that must fit in the block and the execution gas keep their caps (`executionCapacity_default`, `allocateGas_default`).
With the nonce check skipped, a sender whose nonce is `2^64 - 1` still fails, as the notes say (`checkSender_of_skipNonce`).
The nonce of the call itself stays below `2^64 - 1` in both modes, a rule the notes do not lift.
With the caps lifted, all the gas past the intrinsic gas is execution gas (`allocateGas_of_gasCap`).
The whole gas limit must then fit in the execution gas that the block has left (`executionCapacity_of_gasCap`).
Unless that rule is lifted, a transaction pays for its gas at the base fee of its block (`paidBaseFee_empty`, `paidBaseFee_default`).
Once it is, a transaction whose fee cap is 0 pays at a base fee of 0 (`paidBaseFee_of_zeroFee`).
The check of the base fee, the purchase of the gas and the settlement read that base fee, by definition.
The base fee of the block, which BASEFEE reads, stays unchanged, since the block environment is not modified.

Where the source is silent or conflicts with itself, EthLib follows the fixtures, else decides:

- a call without a type is type 2, and type 3 with blob hashes, as the fixtures show; a blob fee cap alone keeps type 2;
- the source is silent on a call without a type that type 2 cannot carry, so EthLib makes authorizations type 4, and a gas price type 0, or type 1 with an access list;
- a call without `from` comes from the zero address and one without `to` creates, as the notes say, though the schema gives the reverse;
- times strictly increase, as the notes say, though the schema lets a time stay the same;
- a block without a time comes 12 seconds after the block before it, as the notes say, though the schema says one second;
- a gap block comes a block time after the block before it, 12 seconds by default, and counts toward the limit of 256 blocks;
- an unknown base block, and a move of an address that is not a precompile, get `-32000`;
- a precompile moved to its own address gets `-38022`;
- the text of `-38023` is ambiguous, and the fixtures move two precompiles to one address without an error, so EthLib never gives it;
- `state` with `stateDiff` gets `-32602`, for which the source gives no code;
- an address or a slot given twice, in hex digits of another case, gets `-32602`;
- block and account overrides support no key beyond their schema, `difficulty` included, nor a key that differs from one only in case;
- the payload and each block ignore a key outside their schema, as the schema allows.

The simulated blocks run through the body of a real block (`simulateBlocks`, `Execution/Rpc/Simulate/Blocks.lean`).
A simulated block differs from a real one in these places:

- its header takes the defaults of the notes and the overrides of the request, and is not checked against its parent;
- without validation, its base fee and its base fee per blob gas are 0, unless the request sets them;
- each call runs from its given sender with `r`, `s` and `yParity` 0, so it needs no signature and may come from an account with code;
- the cap at `2^32 - 1` on the gas limit never applies, and without validation the nonce check and the caps at `2^24` of EIP-8037 do not either;
- without validation, a call whose fee cap is 0 pays nothing for its gas, apart from its blob gas, even below a base fee that the request sets;
- the overrides of the accounts change the state before the block, and are not in its access list;
- the default gas of a call follows the gas that its block has used, within a global budget of 50,000,000 that each call spends, and a call that overspends it gets `-38026`.

Each simulated block follows the last block of its chain at the number that it is given (`simulateBlock_links`, `Proofs/Rpc/SimulateBlocks.lean`).
Its parent hash is the hash of the header of that block, and its own hash is the hash of its header.
When the view holds the hash of each header, there is one block for each planned block and each gap block before it (`simulateBlocks_links`).
They have consecutive numbers after the base block.
The first has the hash of the base block as parent hash, and each other the hash of the block before it.
Without validation, a block whose base fee is not overridden has a base fee of 0, whatever the base fee of the block before it (`simulateBlock_baseFee`).
Its body runs in the environment of its header, whose base fee is then 0, and BASEFEE reads it (`simulateBlock_environment_baseFee`).
With validation off, every block of a simulation whose base fee is not overridden has a base fee of 0, gap blocks included (`simulateBlocks_baseFee`).
With validation and no overrides, a simulated block agrees with the state transition (`stateTransition_of_simulateBlock`).
The fork must be active at the block and come before Hegotá.
Its calls must be signed transactions whose signatures give their senders and name the chain.
Each gas limit must be at most `2^32 - 1` at every fork, and their blob gas must fit 64 bits.
The parent must be the last block of the chain, from London on, at a fork no later than the block's.
The block must be from Paris on, one number above its parent, later in time, and its time must fit 256 bits.
The parent's gas limit must be at least 5,000, and its excess blob gas and blob gas used must add up to less than `2^64`.
The block with those transactions and their root must fit the size limit, which depends on the signatures.
When the state holds the code of each account, its transition gives the state after the simulated block, or fails at a sender with code by EIP-3607, which the simulation skips.
The parent, fork, number, time, gas limit, blob gas and size hypotheses alone make the block with those transactions pass the checks of a block (`checkBlock_simulateBlock`).
Before Paris, the simulated difficulty is that of the base block, which the difficulty rule need not accept, so both theorems start at Paris.

Where the source is silent or conflicts with itself for the blocks, EthLib follows the fixtures, else decides:

- a block keeps the gas limit of the block before it, where the notes name the base block;
- after another simulated block, a block keeps its fee recipient, where the notes name the zero address;
- the extra data is empty, as the fixtures show, where the notes give 32 zero bytes, and the root of the parent beacon block is zero;
- after a block without a slot, the slot is 0, where the notes omit it;
- an override creates no account that it leaves empty, as the fixtures show;
- a blob fee cap on a call without blobs is ignored, as the fixtures show;
- a nonce at `2^64 - 1` gets `-32603`, as the fixtures show;
- a call that does not fit the gas or the blob gas left gets `-38015`, and a rule without a code of its own gets `-32602`;
- without validation, a fee cap of 0 passes at any base fee, as a fixture shows at a base fee of 10;
- a nonzero fee cap below the base fee still gets `-38012`;
- a blob fee cap below a base fee per blob gas that the request sets still fails, with `-32602`;
- the base block must be canonical, so that the hashes before each block are those of its chain;
- from Fusaka to BPO5, the default gas of a call is at most `2^24`, the cap of EIP-7825;
- before London, a call without a type or a fee cap is legacy, or type 1 with an access list from Berlin;
- before Paris, the fee recipient gets the block reward, as in a real block;
- `maxUsedGas` is the gas used with no refund, so from Pectra it is at least the call data floor, as the fixtures show;
- a failed call returns no data, and a revert puts its output in the `data` of its error, as the fixtures show, though the schema lists only a code and a message;
- a failure other than a revert gets `-32015` with a message of EthLib's choice, which the source leaves to the client;
- with `traceTransfers`, a transfer of 0 wei or from an account to itself gets no `0xeeee…eeee` log, as [EIP-7708](https://eips.ethereum.org/EIPS/eip-7708#specification) rules, which the notes leave open; this covers CALLCODE with value and SELFDESTRUCT to itself;
- no fixture of the pin covers the `0xeeee…eeee` logs, since every simulated block of the fixtures is from Glamsterdam, so hand-built tests check them;
- a revert error has the message "execution reverted", without the decoded reason that the fixtures add.

Each simulated block holds the result of each call: the output of its message, its gas used before the refund, and its error.
The body records them without changing anything else that it computes.
From Byzantium, the status of a call result agrees with its receipt: the receipt succeeds exactly when the result has no error (`applyTransaction_status`, `Proofs/Blocks/Transition.lean`).
A body has as many results as receipts (`applyTransactions_results_length`), and a refund never raises the gas used (`runTransaction_gasUsed_le`, `Proofs/Transactions/Process.lean`).

Each frame also records the logs that a simulation reports with `traceTransfers` (`Execution/Evm/Call/TransferLog.lean`).
They are its logs, with a log from `0xeeee…eeee` before Glamsterdam for each move of ether that EIP-7708 would log, in the order of execution.
A frame that fails drops them with its logs.
The flag is not an input of the blocks of a simulation, so they and their headers do not depend on it (`simulateBlocks_traceTransfers`, `Proofs/Rpc/SimulateCalls.lean`).
The code of the receipts, their root and the bloom reads only the logs; no theorem yet states that the logs never depend on the simulated logs.
Without the flag, a call reports the log objects of its receipt, with the same `logIndex` (`callLogInfos_false`).
From Glamsterdam, a message that starts with equal lists of logs ends with equal lists (`simulatedLogs_processMessage`, `Proofs/Evm/Call/SimulatedLogs.lean`).
So each result reports the logs of its receipt (`runBody_simulatedLogs`, `Proofs/Blocks/SimulatedLogs.lean`).
A simulated block from Glamsterdam is then the same with the flag or without (`simulateBlock_json_trace`); no theorem yet lifts this to the whole answer.

`eth_feeHistory` and `eth_baseFee` of [`fee_market.yaml`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/fee_market.yaml) report base fees, gas ratios and tips (`Execution/Rpc/Fees.lean`).
A history is the one of the blocks of its range, when its percentiles strictly increase and the node holds its newest block (`ChainView.feeHistory_eq_ok`, `Proofs/Rpc/Fees.lean`).
The base fee of each block of the range is that of its header, or 0 before London (`ChainView.feeHistory_baseFeePerGas`).
The last base fee is `expectedBaseFeeAcross` of the newest header, the rule that checks the base fee of a header, or 0 when the next block is before London.
In a valid view, take a canonical block that is not the head, and a next block and next fork from London on.
The last base fee is then the base fee in the header of the next block (`ChainView.Valid.nextBaseFee`).
That covers the first London block, which takes the initial base fee, and every block after a London block (`ChainView.Valid.london_le_next`).
`eth_baseFee` gives the last base fee of the history of the head alone (`ChainView.baseFee_eq_feeHistory`).
The lists of base fees have one more entry than the list of gas ratios (`ChainView.feeHistory_length`).
Each reward of a block with transactions, whose receipts match them, is the tip of one of them (`BlockRecord.mem_rewards`).
A block without transactions has rewards of 0 (`BlockRecord.rewards_nil`), and the rewards of a block do not decrease along the percentiles (`BlockRecord.rewards_sorted`).

The source leaves several points of the fee history open, and EthLib decides them.
The next timestamp is unknown, so the fork and the blob schedule of the next block are taken one second after the newest block, its earliest time.
That is exact for a fork that activates by number, as London does, but it misses a fork or a blob schedule that activates later than that.
The next base fee per blob gas uses the excess blob gas that the header rule gives to that block.
A percentile is a JSON number from 0 to 100, and the list must strictly increase; otherwise the request gets `-32602`.
The range holds the blocks that the node has, so it is shorter than the count when the node holds fewer blocks, as the source allows.
A count of 0 gives an empty range, whose oldest block follows the newest one, and an unknown newest block gets `-32001`.
The tip at a percentile is that of the first transaction, by ascending tip, at which the gas used so far reaches that share of the gas that the receipts record.
The comparison is exact.
Before London the base fee is 0, so a tip is the whole gas price.
A ratio is written with at most 18 decimal places, rounded down, and the rewards are left out when the request names no percentile.

`eth_sendRawTransaction` of [`submit.yaml`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/submit.yaml) submits a signed transaction in its raw form (`Execution/Rpc/Submit.lean`).
A blob transaction must come in its network form at the fork of the next block.
Before Fusaka that form has one proof per blob, and from Fusaka it has cell proofs.
The hash of an accepted submission is the hash of the transaction that the raw form holds, without blobs, commitments or proofs (`ChainView.sendRawTransaction_hash`, `Proofs/Rpc/Submit.lean`).
When the first byte is not 3, it is the Keccak-256 hash of the raw bytes (`ChainView.sendRawTransaction_keccak`).
The dispatcher reads the raw bytes and answers with that hash (`ChainView.call_sendRawTransaction`).
A network form is accepted only when its KZG proofs verify against the trusted setup of the view (`ChainView.proofsVerify_of_sendRawTransaction`).
Each code that `rpcCode` gives is in a group that the method lists, within the range of that group (`rpcCode_mem`).
Two errors with one code are of one kind (`rpcCode_injective`).
The mapping is: `insufficientGas` to 800, `gasAllowanceExceeded` to 803, `priorityFeeGreaterThanMaxFee` to 804, `insufficientMaxFeePerGas` to 806, `insufficientBalance` to 809, `nonceTooLow` to 1, `nonceTooHigh` to 2, and `invalidSignature` to 1001.
Two conditions are wider than their messages.
The code 800 also covers a gas limit below the floor of EIP-7623.
The cost behind 809 also counts the blob gas at its fee cap.
The method checks a transaction with no gas used before it, so the allowance of the block is exceeded exactly when the gas limit is above the block's, the condition of 803.

Which transactions a pool keeps is the choice of the node, and EthLib fixes one simple rule.
The rule accepts a transaction whose raw form decodes and whose blob counts, versioned hashes and KZG proofs are valid (`ChainView.validateNetwork_of_sendRawTransaction`).
The transaction must also pass the inclusion checks in the next block, against the state of the head.
That next block is one second after the head, its earliest time, as in the fee history.
It takes the fork, the base fees and the blob schedule of the fee history, and the gas limit of the head.
Its base fee is the last base fee of the fee history (`ChainView.baseFeeOf_nextEnvironment`).
A nonce above that of the sender is a future transaction, which the rule accepts.
The checks then read the head with the nonce of the sender raised to that of the transaction (`withFutureNonce_nonce`), so the code 2 never arises.
From Fusaka, the source lets a node accept proofs per blob and convert them to cell proofs; the rule takes the choice that this "may" leaves, and rejects that form.
A raw form that does not decode, or whose blobs fail their counts, their versioned hashes or their proofs, gets `-32000`.
A failed inclusion check without a code gets `-32003`.
The errors of EthLib without a code are `emptyTransaction`, `unsupportedType`, `decoding`, `encoding`, `initCodeTooLarge`, `gasLimitExceeded`, `nonceOverflow`, `wrongChainId`, `noBlobData`, `blobCountExceeded`, `invalidBlobVersionedHash`, `emptyAuthorizationList`, `blobGasLimitExceeded`, `insufficientMaxFeePerBlobGas`, `senderNotEoa` and `missingCode`.
`intrinsicGasAboveLimit` also has none.
The message of 800 is "Intrinsic gas too low / Intrinsic gas exceeds gas limit", and the cap of EIP-7825 is not a gas limit.
The code 802 names a minimum that the node configures.
The codes 805, 807 and 808 name values that the decoder already rejects.
The code 1000 names a transaction that the node already knows, and the codes `-32000` to `-32006` name no single condition.

`debug_traceTransaction`, `debug_traceBlockByNumber` and `debug_traceBlockByHash` of [`trace.yaml`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/debug/trace.yaml) return the trace of the opcode logger, whose shape [`opcode-tracer.yaml`](https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/opcode-tracer.yaml) fixes (`Execution/Rpc/Trace.lean`, `Execution/Rpc/TraceView.lean`).
The trace is an observer of the one interpreter: the frame loop, the message runs and the transaction runs take an observer of the steps, and the runs of the rest of EthLib are the instances with no observer (`processMessageCall_unfold`, `runTransaction_unfold`, `processTransaction_unfold`, `Proofs/Transactions/Unfold.lean`).
An observer that only records in a state leaves the run unchanged once the state is dropped (`processTransactionWith_modify`, `Proofs/Transactions/Observe.lean`), so the traced run gives what the run gives, for every configuration and bound (`traceRun_output`, `Proofs/Rpc/Trace.lean`).
Two recording observers related by a map of their states give related runs (`runFrameWith_map`, `processTransactionWith_map`).
With no bound, the trace has one entry for each step of a frame with code, as a counter of those steps sees the same run (`traceRun_count`).
That count includes the STOP past the end of the code, which the official fixtures record; a frame with no code has no step, so a plain transfer gives no entry.
Before Glamsterdam, between two consecutive entries at one depth, where the first starts no message and did not fail, the gas falls by exactly the cost of the first (`traceRun_gas`, `Proofs/Rpc/TraceGas.lean`).
A transaction that the body of a block runs has a trace (`traceTransaction_ok`), and from Byzantium its receipt says it succeeded exactly when the trace says it did not fail (`traceTransaction_failed`).
The Python suite runs the 13 vendored `tests/debug_trace*` fixtures; each success fixture is `speconly`, and EthLib matches it field for field, apart from `refund`, which the fixtures leave out.

The source leaves these points open, and EthLib picks:
- `failed` counts every exceptional halt, while the schema names a revert and a lack of gas.
- `gasCost` is the gas that the step removes from its frame; a step that starts a message counts the gas that it passes, and a call that starts none counts only its price.
- A step that fails counts all the gas left, which its halt burns: the schema asks for the price on success, which a failed step does not give.
- From Glamsterdam, `gas` and `gasCost` count execution gas only, without the reservoir of EIP-8037.
- `refund` adds the counters of the frame and of its callers, and is always given, as the schema recommends; it leaves out the refund of EIP-7702 authorizations, which no step shows, and a negative total counts as 0.
- `stack`, `memory` and `returnData` are those before the step; empty memory and empty return data are left out, as the fixtures do.
- `storage` holds, at SLOAD and SSTORE, every slot of the current account that the trace has seen, with its value after the last step that read or wrote it; a failed step adds no slot.
- A byte that is no opcode at the fork is `INVALID`, the name that EIP-141 gives to `0xfe`, and `0x44` is `DIFFICULTY` before Paris, by EIP-4399.
- The text of `error` is EthLib's own; the source fixes none.
- `gas` of the trace is the gas used after the refund.
- Block 0 fails with `-32000`, the code of the fixture `trace-genesis.io`; a block whose parent is not a canonical block of the view, and a number below its lowest block, fail with `4444`; an unknown block or transaction fails with `-32000`.
- A named tracer fails as an invalid parameter, since the source puts named tracers out of its scope; `timeout`, `debug` and `tracerConfig` change no answer.
- The traced block replays the start of the body, then each transaction twice, once traced and once plain; no theorem yet ties that replay to the body.

The Python suite replays the official test chain into a view and answers the official fixtures of the methods that EthLib serves.
That chain mines its blocks before the merge with a zero mix hash and a zero nonce, so the suite runs the transition without the proof-of-work check.

### Beacon API

The Beacon API is the HTTP interface of a consensus client, as release `v5.0.0-beta.0` of `ethereum/beacon-APIs` defines it.
EthLib specifies the consensus version that its responses carry and their JSON encodings; it leaves out the transport.

A response names the fork of its data by a consensus version, one name for each fork of the consensus layer.
`ConsensusVersion.ofName?_name` and `ConsensusVersion.name_of_ofName?` (`Consensus/Proofs/ConsensusVersion.lean`) show that the reader accepts exactly the eight names of the schema, spelled exactly.
`Fork.consensusVersion?_isSome_iff` shows that a fork has a version exactly from Phase 0 through Glamsterdam.
`Fork.fork_le_of_consensusVersion?` and `Fork.le_consensusVersion?_of_fork_le` show that a fork of the execution layer or of the blob schedule has the version of the latest consensus fork before it.
`Fork.consensusVersion?_forkVersion` shows that the version names the fork version of the fork, under every configuration.
So the name that a response carries determines the fork version of its fork.
`Fork.consensusVersion?_mono` shows that versions never move back along the timeline.
The source names no version for Heze yet, so Hegotá has none until a release of the source names it.

The data of a response is a value of the consensus layer, in the JSON mapping of SSZ.
`ofApiJson_toApiJson` (`Consensus/Proofs/BeaconApi/Encoding.lean`) shows that the reader gives back every value that the writer writes, for every lawful type and every spelling.
`toApiJson_total` shows that the writer never fails on a value of a lawful type, whatever its spelling.
It rests on `jsonOf_ok` (`Serialization/Proofs/Ssz/Codec/JsonTotal.lean`): a well-formed SSZ type writes every value that it admits, under every spelling.
A mark of the spelling has effect only where its shape allows it, so no mark makes the writer fail.
`ApiEnvelope.ofJson_toJson` shows that an envelope reads back as written, and `readVersioned_envelope` that a response reads as its data under its version, whatever its other metadata.
`readVersioned_version` shows that a response read under a version carries that exact name, so data of one fork never reads as data of another.
`valueOf_sameUpToCase` (`Serialization/Proofs/Ssz/Codec/JsonHexCase.lean`) shows that a document reads the same with any hex digits of its strings in uppercase, at every shape.
The patterns of the source allow either case.
`valueOf_sameUpToCase` holds for every spelling that writes no text, since the case of a URL is part of the URL.
`ofApiJson_uppercase` lifts it to the reader of the API, and `fieldSpelling_hasText` shows that every container spelled from its field marks, with no text mark among them, meets its hypothesis.
The error bodies read back as written (`ErrorMessage.ofJson_toJson`, `IndexedErrorMessage.ofJson_toJson`).

Each container declares its spelling in `Consensus/BeaconApi/Spelling.lean`, and none falls back to a default.
Before Gloas, participation flags have the SSZ type of a byte list, and their spelling writes them as a list of decimal strings, as the API does.
From Gloas, transactions and the block access list are progressive lists of one-byte integers, and their spelling writes them as hex, as the API does.
From Gloas, the URL of a builder entry is a byte list that its spelling writes as text, as the API does.
A container that holds one of these takes the spelling of the field that holds it.

The spellings are checked by tests, not by a proof.
Two exports write the JSON of a container from its SSZ bytes, and read it back, by preset, fork and name.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_json.py`) writes the JSON of each static SSZ vector that the `types` files of the API define.
It validates that JSON against the schema of the container at its fork; it checks the lengths of lists and strings only for the mainnet preset.
It reads the JSON back to the same bytes, with its hex in lowercase and in uppercase.
In one case of each container, it puts an example of the `types` files in place of one string of each type and shape, and reads the result.
It skips a hex string whose fixed length the example does not have.
It also reads the JSON examples of the builder specification to the bytes of those examples.
It checks that each integer string is the plain decimal form of a value in range.
It checks values against an oracle written apart from EthLib: a Gloas payload written by hand in SSZ and in JSON, and chosen participation flags of an Altair state.

A path names a state, a block or a validator by an identifier (`Consensus/BeaconApi/Identifiers.lean`).
`parseStateId_print`, `parseBlockId_print` and `parseValidatorId_print` (`Consensus/Proofs/BeaconApi/Identifiers.lean`) show that each identifier reads back from its text.
`parseStateId_error_code`, `parseBlockId_error_code` and `parseValidatorId_error_code` show that a text that is no identifier gets code 400.
`resolveBlockId_head` shows that the head of the API is the head of the fork choice, `getHead`.
`resolveBlockId_slot` shows that a slot names a known block at that slot, the ancestor of that head at the slot.
`isFinalizedRoot_of_slot_le` shows that a block of the chain of a head, at or below the finalized block of that chain, is reported finalized.
`parseUInt64_print_of_some` shows that a slot or an index reads only from its plain decimal text, so a sign or a leading zero is refused.
A state root names the state after the block whose `state_root` field it is.
That rests on the store, which checks the field of each block that it imports and of its anchor.
`stateRoot_blockStates` and `stateRoot_resolveStateId_root` state it for a store that the handlers reach.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_identifiers.py`) checks the resolvers against a Capella fork choice vector of the minimal preset, not by a proof.
The `execution_optimistic` flag reads the optimistic store; nothing exports or tests it.

The answers that describe the chain are in `Consensus/BeaconApi/Config.lean`: the spec map, the fork schedule, the deposit contract and the genesis.
The spec map writes each value of the configuration and of the presets under its name, from one enumeration that the preset and configuration exports also use.
`specMap_keys_nodup` (`Consensus/Proofs/BeaconApi/Config.lean`) shows that no name appears twice.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_config.py`) checks that the map equals the pinned configuration and preset files, in the form of the API.
The fork schedule lists Phase 0, with the genesis version twice and epoch 0, then each consensus fork up to Heze, with the version before it and its fork epoch.
`forkSchedule_upgrade` shows that an upgrade that is due writes into the state the entry of its fork in the schedule, when the state holds the version of its own fork.
`forkSchedule_lastStarted` shows that the last entry that has started at an epoch has the fork version at that epoch, for every configuration.
`forkSchedule_version` shows that the entry with the largest epoch that has started, the later one on a tie, has that version too, when the fork epochs do not decrease.
Without that order it fails: with Altair at epoch 10 and Bellatrix at epoch 5, at epoch 12 that entry is Altair's, while the fork version is Bellatrix's.
The genesis answer takes its time and its root from the genesis state, and its version from the configuration.
`genesisInfo_version` shows that the genesis state that deposits build holds that version.
`currentVersion_of_genesis_chainSteps` shows that along a chain from that genesis state, across forks, each state has the version of its fork as its current version.
It follows from `currentVersion_of_chainSteps`, which shows the same along a chain from any state that has it.
`forkVersions_mem_forkSchedule_of_genesis_chainSteps` shows that the fork versions of each state of such a chain are an entry of the schedule.
That genesis state is before Altair (`initializeBeaconStateFromEth1_frame`), and each fork before Altair has the genesis version, which the state holds (`genesisInfo_version`).
Its fork versions are the genesis version twice with epoch 0, the first entry of the schedule.
A slot with its epoch processing, or a block, keeps the fork versions at every fork (`advanceSlot_kept` in `Consensus/Proofs/Transition/TargetSlots.lean`, `frame_processBlock`).
An upgrade writes the version of the fork that it reaches as the current version (`upgradeFrame_upgradeNext`).
So each upgrade of such a chain starts from a state that holds the version of its fork, and `forkSchedule_upgrade` applies to it.

The answers that read one field of a state are in `Consensus/BeaconApi/StateQueries.lean`.
They are the root, the fork, the finality checkpoints, the RANDAO mix, the three pending queues, the proposer lookahead, and the pending payments and withdrawals of builders.
`stateRoot_blockStates` (`Consensus/Proofs/BeaconApi/StateQueries.lean`) shows that, in a store that the handlers reach, the root of the state kept for a known block is the state root of that block.
`stateRoot_resolveStateId_root` follows from it: a state named by its root has that root, as the source requires.
`finalityCheckpoints_genesis` shows that the genesis state that deposits build, which exists only at Phase 0, has its three checkpoints at epoch 0 with the zero root.
`finalityCheckpoints_of_genesis_chainSteps` shows, for each state that a chain from that genesis state reaches across forks, that each checkpoint at epoch 0 is reported with the zero root.
`GenesisCheckpointsZero.of_initializeBeaconStateFromEth1` is a corollary of `finalityCheckpoints_genesis`.
A state before finalization, whose finalized epoch is still 0, reports a finalized checkpoint of epoch 0 and the zero root, as the source says it should.
A justified checkpoint at epoch 0 is reported with the zero root too.
Both follow from `GenesisCheckpointsZero.of_chainSteps`, which shows that along a chain each checkpoint at epoch 0 keeps the zero root.
Justification returns the state unchanged when `getCurrentEpoch state ≤ GENESIS_EPOCH + 1`, as `processJustificationAndFinalization_reads` states.
Later it justifies only the previous or the current epoch, and copies the other checkpoints, by `weighJustificationAndFinalization_checkpoints`.
The current epoch is then at least 2, so both epochs are after epoch 0, by `getPreviousEpoch_toNat`.
The slot step, the rest of the epoch transition, each block and each upgrade copy the three checkpoints.
Their frames say so: `frame_processSlot`, `processEpoch_frame`, `frame_processBlock` and `upgradeFrame_upgradeNext`.
`pendingDeposits_error_iff` and the five theorems beside it show that each field that a fork adds gives the error with code 400 exactly when the state is before that fork.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_state_queries.py`) checks the root against the hash tree root of the state.
It checks each other answer against the JSON of the whole state, on one state of the minimal preset per fork, with a distinct value in each field that a query reads.

The statuses of validators and builders are in `Consensus/BeaconApi/Validators.lean`.
`validatorStatus_holds` (`Consensus/Proofs/BeaconApi/Validators.lean`) shows that the status of a validator meets the condition that the source gives for it.
`validatorStatus_unique` shows that it is the only status that does, when the activation, exit and withdrawable epochs of the validator do not decrease.
Each order is needed: `validatorStatus_order_needed` gives a validator with its exit before its activation that meets two conditions at once.
`validatorStatus_exit_order_needed` does the same with its withdrawable epoch before its exit.
No theorem yet shows that every validator of a reachable state meets that hypothesis.
`validatorStatus_active_iff` shows, with no hypothesis, that the group of the status is active exactly when the validator is active.
`builderStatus_unique` shows that the status of a builder of the state is the only one whose condition holds.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_validators.py`) checks each of the nine statuses and the three builder statuses on hand-made inputs.

The answers that read the registries of validators and builders are in `Consensus/BeaconApi/Registries.lean`: the validators, their balances, their identities, and the builders.
`stateValidators_mem` (`Consensus/Proofs/BeaconApi/Registries.lean`) says which entries the validators answer holds.
An entry is there exactly when the request names its index and its record and balance are those of the state.
Its status must also be the status at the current epoch, and pass the filter.
`resolveValidatorId_index` and `resolveValidatorId_pubkey` show that an identifier names an index below the size of the registry, or the first validator that holds a public key.
`stateValidators_balance` restates the balance part, and `stateValidators_nodup` shows that each index appears at most once.
`stateBalances_mem`, `stateIdentities_mem`, `stateBalances_nodup` and `stateIdentities_nodup` say the same of the two other answers, without the filter.
An entry of the balances answer needs only a balance, and an entry of the identities answer only a record.
`stateValidator_ok` says the same of the endpoint for one validator.
`stateValidator_error_code` shows that it answers code 404 otherwise: when the identifier names no validator, or names one without a balance.
The source gives no order, so the acceptance predicates take any permutation of the entries.
`IsValidatorsAnswer.mem_iff` and its three siblings show that such an answer has the same entries.
The reader of a request refuses more than 64 identifiers in a query string with code 414 (`readValidatorIds_too_many`), and a text that is neither an index nor a public key with code 400.
`StatusName.parse_status_name` and `StatusName.parse_group_name` show that the reader of a filter takes the name of each status and of each group.
From Gloas, the builders answer follows the same rule, with the status that the state gives each builder.
`stateBuilders_mem` says which entries it holds, and `stateBuilders_nodup` that each index appears at most once.
`resolveBuilderId_index` and `resolveBuilderId_pubkey` say which builder an index or a public key names.
`buildersResponse_before_gloas` shows that a state before Gloas gets code 400, and `BuilderStatus.parse_name` that the reader takes the name of each builder status.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_registries.py`) checks each answer against a hand-made registry of the minimal preset.
Its registry holds one validator of each of the nine statuses, and one builder of each of the three.
It covers a filter on each status and each group, the errors with codes 400, 404 and 414, and the SSZ body of the balances.

The answers that list the committees of a state are in `Consensus/BeaconApi/Committees.lean`: the beacon committees of an epoch, the sync committee and, from Gloas, the payload timeliness committee (PTC) of a slot.
`epochCommittees_mem` (`Consensus/Proofs/BeaconApi/Committees.lean`) says which committees the committees answer lists.
When the answer has a value, a committee is listed exactly when its slot is in the epoch, its index is below the count of committees of a slot, and it matches each filter.
Its members must also be those that `getBeaconCommittee` gives for its slot and index.
`epochCommittees_partition` shows that, without a filter, the members of the committees of an epoch are a permutation of its active validators, so each active validator is in exactly one committee.
It needs at least one slot in an epoch, and the number of active validators times the number of committees of the epoch must fit in 64 bits.
`committeesResponse_epoch_bound` shows that an epoch after the next one gets code 400.
`committeesResponse_epoch_old` shows that an epoch whose RANDAO mix the state no longer holds gets code 400 too.
That is an epoch whose sum with the length of the buffer of mixes is at most the next epoch plus the lookahead of seeds.
`epochSyncCommittees_validators` shows that each seat of the sync committee answer holds the first validator whose key is the key of the seat, in the committee of the period of the epoch.
`syncAggregates_pubkeys` shows that the slices cut the keys of a committee as the subcommittees of the gossip rules do.
`epochSyncCommittees_aggregates` shows that its slices, put end to end, give back that list, when the count of subnets divides the size of a sync committee.
`statePtc_ok_iff` shows that, from Gloas, the PTC answer is the committee that `getPtc` reads in the window of the state.
`statePtc_error_iff` shows that it is an error exactly when one of four conditions holds.
The state is before Gloas, or the epoch of the slot is before the Gloas fork epoch.
Or that epoch is before the epoch of the state minus one, or after the epoch of the state plus the lookahead of seeds.
It needs at least one slot in an epoch, and the last epoch of the lookahead and the length of the window must fit in 64 bits.
`statePtc_error_code` shows that each such error has code 400; writing the answer in JSON or SSZ can still give code 500.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_committees.py`) checks the three answers on the base states of the pinned fork vectors of the minimal preset.
It reads the active validators, the keys of the sync committees and the window of the PTC from the JSON of the state.
It checks each committee against the assignment that the honest validator guide gives each active validator.

The answers that read one signed block are in `Consensus/BeaconApi/Blocks.lean`: the block, its root, its attestations, its blinded form and its blobs.
`signedHeader_root` (`Consensus/Proofs/BeaconApi/Blocks.lean`) shows that the header of a block has the root of the block and carries its signature.
`blindedBlock_root` shows the same of the blinded block from Bellatrix to Fulu; it rests on `BeaconBlock.hashTreeRoot_blind`, and assumes that the logs bloom of the preset is not empty.
`blindedBlock_total` shows that such a block always has a blinded form.
So the root endpoint gives one root for the block, its header and its blinded form.
`blindedBlockResponse_before_bellatrix` shows that before Bellatrix the blinded block endpoint gives the block itself, and `blindedBlockResponse_gloas` that from Gloas it gets code 400.
`blobsOf_ok` shows that the blobs endpoint answers with `blockBlobs` over the commitments of the block, and `blockCommitments_before_deneb` that a block before Deneb has none.
`blockBlobs_sublist` shows that the blobs answer keeps the order of the blobs of the block, and `blockBlobs_none` that it gives them all without hashes.
`blockBlobs_versionedHash` shows that each blob it gives sits at the place of a commitment whose versioned hash is requested.
`blockBlobs_commitment` shows that each such blob commits to a commitment of the block whose versioned hash is requested, when each blob of the block commits to the commitment at its place.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_blocks.py`) checks the root of the random static block of each fork from Phase 0 to Heze against its pinned root.
It checks that the blinded block, encoded again, has that pinned root too.
It checks the block, the attestations and the blinded block against the JSON of that block.
It checks the blobs answer, with and without hashes, against versioned hashes that it computes with SHA-256 itself.

The same module gives the headers, the data column sidecars and the payload envelope of a block, and the SSZ bodies of the block and the blinded block.
`headers_canonical_head` shows that the header answer of the head block says that the block is canonical; it rests on `isCanonical_head`.
`isCanonical_of_unknown` shows that a block the store does not hold is not canonical.
`headerOf_ok` shows that a header answer carries its header and the root of its message, and `headerOf_blockRoot` that this root is the root of the block.
`headersOf_mem` shows that each entry of the headers answer is the answer for a held header at the requested slot, with the requested parent root.
`headersSlot_default` shows that without filters the headers answer reads the slot of the head.
`IsColumnsAnswer` accepts any order of the requested sidecars, so the selection in input order is one answer by definition.
`IsColumnsAnswer.mem_iff` shows that a sidecar is in an answer exactly when the node holds it and its index is requested.
`selectColumns_none` shows that without indices all are kept, and `selectColumns_some_nil` that an empty list keeps none.
`columnsResponse_before_fulu` shows that before Fulu the columns answer gets code 400.
`payloadEnvelopeOf_ok` shows that the envelope answer is the given signed envelope, from Gloas, and that its message has the root of the envelope that the store holds for the block.
`payloadEnvelopeOf_of_stored` shows the converse: such an envelope is the answer.
`payloadEnvelopeOf_before_gloas` shows that before Gloas the answer gets code 404, and `blindedBlockSsz_gloas` that from Gloas the blinded block has no SSZ body either.
The Python suite builds the store of a Gloas fork choice case with one block and its envelope.
It checks the header and headers answers of that block and of the anchor, with each filter, against headers that it builds from the JSON of the blocks.
It checks the envelope answer against the pinned envelope, and code 404 for the anchor and for another message.
It checks the columns answer and its SSZ body for Fulu and Gloas, with and without indices, and code 400 before Fulu.
It checks the SSZ bodies of the block and the blinded block against the JSON answers.
It checks code 400 for the blinded block from Gloas, and that the attestations answer has no SSZ body.

The duty answers are in `Consensus/BeaconApi/Duties.lean`: attester, proposer, sync committee and PTC duties, with their dependent roots.
`attesterDuties_committee` (`Consensus/Proofs/BeaconApi/Duties.lean`) shows that each attester duty names a committee of its slot.
The committee has the length of the duty and holds the validator at the position of the duty.
`attesterDuties_complete` shows that a requested validator with a committee assignment has exactly one duty, when the request repeats no index.
`attesterDuties_epoch` shows that each attester duty is in the requested epoch, with the count of committees per slot of the epoch and an index below it.
`attesterDuties_epoch_bound` and `ptcDuties_epoch_bound` show that a request for an epoch after the next one gets the error of an invalid epoch, code 400.
`attesterDuties_seed_gone` shows the same for an attester epoch too old for the mixes of the state to hold its seed.
It reads the clause of the epoch check that asks the mixes to still hold the seed.
`attesterDuties_nil` shows that the attester duties of a request with no index get the error of an empty request, code 400.
`syncDuties_nil` shows the same for the sync duties, from Altair.
`dutiesResponse_nil` shows that the answer to an attester, sync or PTC request with no index is an error with code 400.
`ptcDuties_eq` states the PTC duties whole, from Gloas, before the dependent root.
An empty request gets code 400, and so does an epoch outside a window.
The window runs from the previous epoch to the next one, and not before the Gloas fork epoch.
The mixes must also still hold the seed of the epoch.
In the window a repeated index gets code 400.
Distinct indices run the duty of each requested validator in turn, in request order, and the first index that fails ends the answer.
`proposerDuties_beaconProposer` shows that in the current epoch each proposer duty names the proposer of the state advanced to its slot.
`proposerDuties_current_slot` shows the same at the slot of the state itself.
`syncDuties_seats` shows that each seat of a sync duty holds the key of the validator, in the committee of the period, and that a duty has a seat.
`dependentRoot_genesis` shows that the dependent root of the first two epochs, with a lag of one, is the genesis root.
`dependentRoot_genesis_zero` shows the same for epoch 0 without a lag.
`dependentRoot_eq` unfolds the case past the underflow: the block root at the slot before the start of the epoch a lag before.
`dependentRoot_too_old` shows that a dependent root that has left the block roots gets the error of an invalid epoch, code 400.
It reads the clause of `getBlockRootAtSlot` that bounds the slot of the state by the slot asked for plus the length of the buffer.
`dutiesResponse_attester_too_old` shows that an attester request for an epoch whose dependent root has left the block roots gets that error too.
It needs at least one index, each naming a validator whose committee assignment succeeds.
`dutiesResponse_attester_unknown` shows that an attester index that names no validator gets the error of an invalid index, code 400.
It reads `requestedValidator`, which gives that error for an index past the registry.
It needs an epoch that passes the epoch check, and each earlier index to name a validator whose committee assignment succeeds.
`dutiesResponse_sync_unknown` shows the same for a sync index, from Altair, at an epoch of the current or the next period.
It needs each earlier index to name a validator.
`dutiesResponse_ptc_unknown` shows it for a PTC index, from Gloas, in the window of `ptcDuties_eq` and with no repeated index.
It needs each earlier index to name a validator whose PTC assignment succeeds.
`dutiesResponse_sync_outside` shows that from Altair a sync epoch outside the current and next periods gets code 400, when the request has an index.
It reads the last clause of `syncCommitteeOf`, whose error says that the epoch is outside the sync committee period of the state.
`dutiesResponse_proposer_not_current` shows that the first proposer answer gives the error of an invalid epoch, code 400, to any epoch but the current one.
So it refuses the next epoch even from Fulu, where the lookahead holds its proposers.
It shows the same for the second answer before Fulu, where `epochProposers` draws the current epoch alone.
`dutiesResponse_proposer_outside` shows that the second answer gives that error to an epoch before the current one or past the seed lookahead, on every fork.
It reads the clause of `epochProposers` that bounds the epoch from Fulu by the lookahead of the state.
`dutiesResponse_sync_of_lt_altair` shows that before Altair the sync answer is the error with code 400 that names Altair.
`dutiesResponse_ptc_of_lt_gloas` shows that before Gloas the PTC answer is the error with code 400 that names Gloas.
They read the fork branches of `dutiesResponse`, which come before any check of the request, so a request with no index gets these errors too.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_duties.py`) reads the minimal states of the committee tests.
It checks the attester duties against the committees answer, and the PTC duties against the assignments of the guide.
It checks the proposer duties against the lookahead of the state from Fulu, and against the proposer of each slot before Fulu.
It checks the sync duties against the keys of the committees in the JSON of the state.
It gives the state a different block root at each place, and checks each dependent root against it.
It checks code 400 for an empty request to the attester, sync and PTC answers.
For the attester answer it also checks code 400 for an unknown index, and for an epoch too far ahead or too old.
For the PTC answer it checks code 400 for a repeated index, and an epoch too far ahead or too old.
It also checks code 400 for a PTC request to an Electra state.
For the sync answer it checks code 400 for a request to a Phase 0 state.
It also checks code 400 for a sync epoch of the previous period and of two periods ahead.
For the first proposer answer it checks code 400 at the next epoch from Fulu.
For the second it checks code 400 at the next epoch before Fulu, and from Fulu at the previous epoch and two epochs ahead.
It never asks for PTC duties at the previous epoch or before the Gloas fork epoch; only `ptcDuties_eq` covers those two.
It sends no unknown index to the sync or PTC answer, so only the theorems cover those two.
No theorem states the errors with code 500, where the node cannot compute an assignment, a proposer, a slot or a root.
No theorem states the code 400 that the PTC assignment gives to an epoch past the seed lookahead.
It is reachable only at the next epoch, under a preset whose seed lookahead is zero.

The answers that hand a validator its data are in `Consensus/BeaconApi/ValidatorData.lean`: attestation data, payload attestation data, aggregates and sync committee contributions.
`produceAttestationData_head` (`Consensus/Proofs/BeaconApi/ValidatorData.lean`) shows that the attestation data votes for the head of the store, at the requested slot, and that the head is not optimistic.
`produceAttestationData_index` shows that for a store in Electra or Fulu the index of the data is 0.
`producePayloadAttestationData_block` shows that the payload attestation data names the block of its slot on the chain of the head, with the two flags given.
`aggregateAttestation_matching` shows that an aggregate has the requested data root and slot, and that its block is not optimistic.
`aggregateAttestation_construct_of_lt_electra` and `aggregateAttestation_construct_of_electra` show that an aggregate is the honest aggregate of the guide, over the messages with its data.
`aggregateAttestation_bits_of_lt_electra` shows that before Electra a bit of an aggregate is set exactly when that bit of an attestation with its data is.
`aggregateAttestation_attesters_of_electra` shows that from Electra the attesters of an aggregate are those of the single attestations with its data and committee.
`aggregateAttestation_committeeBits_of_electra` shows that from Electra its committee bits mark the requested committee alone.
`aggregateAttestation_valid_of_lt_electra` and `aggregateAttestation_valid_of_electra` show that an aggregate of distinct honest messages passes the check of an indexed attestation, when the registry holds each signer's key and the secret keys do not sum to zero.
`produceSyncCommitteeContribution_bits` shows that a bit of a contribution is set exactly when a message of the slot and root comes from a validator with the key of that seat.
`aggregateAttestation_error_iff_of_lt_electra` states when the aggregate answer refuses before Electra with a code other than 500, the code of an internal error.
It refuses with code 404 exactly when no attestation has the requested data root, slot and committee index.
It refuses with code 503 exactly when the block of the first match is optimistic, and never with code 400.
`aggregateAttestation_error_iff_of_electra` states the same from Electra, for the single attestations.
From Electra it also refuses with code 400 exactly when the block of the first match is verified and the index is out of range.
That is, the committee index is not below `MAX_COMMITTEES_PER_SLOT`.
A lower index never gives code 400, even when the epoch has fewer committees.
`produceSyncCommitteeContribution_error_iff` states when the contribution answer refuses with a code other than 500.
It refuses with code 400 exactly when the slot is not that of the state, or the subcommittee index names no subnet.
Else it refuses with code 503 exactly when the root is optimistic.
Else it refuses with code 404 exactly when no message of the slot on the root comes from a member of the subcommittee.
A member is a known validator with a key of the subcommittee.
That refusal also needs the sync committee of the next slot, which `syncCommitteeAtNextSlot_eq` gives at every slot but the last.
The three theorems share `checkVerified_bind_error_iff`.
After the check of a block, an answer refuses with code 503 for an optimistic block, and else as the rest does.
`aggregateAttestationResponse_error_iff` and `syncCommitteeContributionResponse_error_iff` lift these codes to the responses of the two endpoints.
`apiJsonOr500_error_code` shows that writing the value of an answer as JSON fails only with code 500.
`syncCommitteeContributionResponse_of_lt_altair` shows that before Altair the contribution response is the error with code 400 that names Altair.
The source requires code 503 when "the block identified by the response `beacon_block_root` is optimistic".
It requires code 404 when "no attestation is available for the requested `attestation_data_root`".
It requires the same when "no sync committee contribution is available for the requested `beacon_block_root`".
It lists code 400 only as "Invalid request syntax.", so the cases of code 400 are a choice of EthLib.
The source requires code 404 for the data root alone, so code 404 for another slot or committee is a choice of EthLib.
So is the order of the checks, which picks one code when two apply.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_validator_data.py`) builds stores from the pinned Gloas fork choice cases.
It checks the attestation data at the slot of the head and after it, where the index signals the payload, and codes 400 and 503.
It checks the payload attestation data of a slot with a block, and none for a slot without one.
It checks the attestation data index of Deneb, Electra and Fulu stores, and code 400 for payload attestation data before Gloas.
It checks the aggregates and contributions against bytes it builds itself.
It checks codes 404 and 503 for the aggregate, and codes 400, 404 and 503 for the contribution.
It checks the codes of the aggregate before Electra only, so only the theorems speak for the single attestations.
No theorem states when these answers refuse with code 500.
The issue's single matching and validity theorems are split by fork; from Electra the union of bits is stated as the set of attesters.

The light client answers are in `Consensus/BeaconApi/LightClient.lean`: the bootstrap of a block, the updates of a range of periods, and the latest finality and optimistic updates.
`bootstrapFor_valid` (`Consensus/Proofs/BeaconApi/LightClientBootstrap.lean`) shows that a bootstrap the node serves for a block starts a light client that trusts that block.
It assumes that the store holds the block under its root and the post state that the block names.
It also assumes that the schedule puts the forks from Capella to Heze in order.
It assumes a lawful state type and a preset whose sizes in the block and the state are nonzero.
The answer itself refuses a block whose fork is not the fork that the schedule gives at its slot.

`bootstrapFor_valid_of_reachable` (`Consensus/Proofs/BeaconApi/LightClientBootstrapReachable.lean`) shows the same for a store that the handlers reach from an anchor that the fork choice accepts, with no other assumption on the store.
It keeps the assumptions on the schedule, the state type and the preset.
Its proof reads `Store.Reachable.root`, which shows that each known block has its own root as its key.
The proof also reads `stateRoot_blockStates`, which shows that the state kept under that root has the state root of the block.

The handlers of `Store.Reachable` leave out `onInvalidPayload`, which runs when the execution layer finds a payload invalid.
From Heze they also leave out `Store.recordValidatedInclusionListSatisfaction`, which records whether a payload that turns valid satisfies its inclusion lists.
The first step removes a block only together with its state, and the second touches neither the blocks nor the states.
So both keep the two facts that the proof reads.
No theorem states that yet, so after either step only `bootstrapFor_valid` applies, with its assumptions on the store.

`bootstrapFor_error` shows that each refusal of the bootstrap is the error with code 404 that names the root, and `bootstrapFor_error_code` gives the code.
The file `apis/beacon/light_client/bootstrap.yaml` of release `v5.0.0-beta.0` lists that code when "`LightClientBootstrap` instance cannot be produced for the given block root".
`bootstrapResponse_of_error` shows that the JSON answer passes each refusal on unchanged.
`bootstrapFor_of_missing` shows that a root whose block or post state the store lacks gets that error.
`bootstrapFor_of_lt_altair` shows that error for a root whose post state is before the Altair fork epoch, for a store of any fork and under any schedule.
These points of the bootstrap answer have no theorem:

- which roots it refuses when their post state is from the Altair fork epoch on;
- whether a served bootstrap can get code 500, when it is written in JSON or in SSZ.

One such root is a block whose fork is not the fork that the schedule gives at its slot.

`IsUpdatesAnswer` is the rule of the source for the updates answer: known updates of the range, in increasing period order, starting with the earliest known one, at most `min(128, count)` of them.
`updatesInRange_answer` (`Consensus/Proofs/BeaconApi/LightClient.lean`) shows that the known updates of the range, cut to that limit, form such an answer.
`IsUpdatesAnswer.length_le` shows that no accepted answer holds more updates, and `IsUpdatesAnswer.length_le_limit` gives the limit itself.
`decodeUpdateChunks_encode` shows that the SSZ chunks of updates decode back to the updates, each with its fork, on a chain that passes the check of fork digests.
It assumes a preset with a nonempty logs bloom and sync committee, as the round trip of SSZ for these containers does.
The decoder also refuses a chunk whose digest is not the digest of the epoch of its update.
`encodeUpdateChunks_decode` shows the converse under the same assumptions: bytes that decode are the chunks of the updates they give.
`finalityUpdateResponse_notFound_iff` and `optimisticUpdateResponse_notFound_iff` show that each latest update answer refuses with code 404 exactly when the node knows no update of its kind.
The files `finality_update.yaml` and `optimistic_update.yaml` of that release list that code when "No `LightClientFinalityUpdate` is available" and "No `LightClientOptimisticUpdate` is available".
No theorem states whether a known update can get code 500 when it is written in JSON.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_light_client.py`) reads the pinned data collection cases of the light client.
It checks that the chunks of the best updates of each case carry the digests and the bytes that the case serves, and decode back to them.
It checks the start, the count and the limit of 128 of a range, the versions of the JSON answer, and the refusal of an update of another fork than its epoch.
It builds the store of a Gloas fork choice case, checks the bootstrap of the head and of the anchor, and starts a light client from each.
It checks code 404 for the bootstrap of an unknown block and under a schedule before Altair.
It checks code 404 for the latest finality and optimistic updates when the node knows none.

The answers that split the rewards of validators are in `Consensus/BeaconApi/Rewards.lean`: the attestation rewards of an epoch, and the ideal rewards of each effective balance.
`attestationRewardsResponse_ok` (`Consensus/Proofs/BeaconApi/Rewards.lean`) shows that an answer comes from a state at the last slot of an epoch past the first, for the epoch before, and that both lists are read from the state that the rewards step of the epoch transition reads.
`processEpoch_stateBeforeRewards` shows that the epoch transition runs its rewards step on that state, after justification and, from Altair, the inactivity scores.
`attestationRewards_indices` shows that the answer names the requested validators, once each and in order of index, and `attestationRewards_ok` that the total rewards exist whenever the rewards step succeeds; no theorem says the same of the ideal rewards.
`attestationRewards_parts_of_altair` and `attestationRewards_parts_of_lt_altair` show that each part is the reward minus the penalty of the deltas of its kind.
Before Altair the inclusion part is the attester's own reward; `attesterInclusionRewards_split` shows that the inclusion deltas are those parts plus the proposer shares, and `attestationRewards_inclusionDelay_le_of_lt_altair` that the part is at most the deltas.
`attestationRewards_sum_of_altair` and `attestationRewards_sum_of_lt_altair` show that the parts add up to what the transition applies; before Altair the inclusion deltas take the place of the inclusion part.
`attestationRewards_balance_of_lt_altair` and `attestationRewards_balance_of_altair` show that the rewards step moves the balance of the validator by exactly that sum.
Before Altair they assume that the balance plus the reward covers the penalty, and from Altair that the penalties do not exceed the balance: a balance stops at zero, so a larger penalty moves it by less.
From Altair the assumption bounds the sum of the penalties of the epoch, since the flags apply one after the other; it is sufficient, not necessary.
`idealAttestationRewards_sorted` shows that the ideal rewards list distinct effective balances in increasing order.
`attestationRewards_ideal_of_altair` shows that from Altair an eligible validator that set every flag earns the ideal parts of its effective balance.
`idealAttestationRewards_mem` shows that each ideal entry is read at a validator of the registry with the effective balance of the entry.
`idealRewardsOf_parts_of_lt_altair` gives each part of such an entry before Altair in closed form, from the base reward of that validator.
Each vote earns the base reward in a leak, and otherwise the base reward times the matched unslashed increments over the active increments, rounded down.
The inclusion earns the base reward less the proposer share.
The inactivity part is minus four base rewards plus the proposer share in a leak, and zero otherwise.
`attestationRewards_ideal_of_lt_altair` shows that before Altair an eligible validator whose three votes matched, first included one slot after its vote, earns those ideal parts.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_rewards.py`) reads the states of the pinned rewards vectors, at every fork from phase 0.
It takes each state to the last slot of its epoch, and checks each part of each validator against EthLib's deltas of its kind, which the rewards vectors check, on the state after justification and the inactivity scores.
It checks that a validator that earned a reward for every vote gets the ideal parts of its effective balance, and code 400 and 404, including a state that is not at the last slot of its epoch.
Before Altair it checks the inclusion part only as at most the ideal one, so the ideal inclusion part rests on `idealRewardsOf_parts_of_lt_altair` and `attestationRewards_ideal_of_lt_altair`.

The sync committee rewards of a block are in the same module, read from the state that the sync aggregate step of the block reads.
`syncCommitteeRewards_reward` shows that the reward of a member is the sum over its seats of the participant reward that the transition computes, counted for a seat that signed and against a seat that did not.
`syncCommitteeRewards_indices` shows that the answer names each requested member once, in increasing order of index.
`syncCommitteeRewards_balance` shows that the sync aggregate step moves the balance of a member that is not the proposer by exactly its reward.
`syncCommitteeRewards_balance_of_proposer` shows that the proposer moves by its reward plus its share of the reward of each seat that signed.
Both assume that the balance covers the participant reward once per seat of the member, since a balance stops at zero.
`syncCommitteeRewardsResponse_ok` shows that an answer comes only from a state of Altair or later, and lists the rewards of the request; `syncCommitteeRewardsResponse_of_lt_altair` shows code 400 before Altair.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_sync_rewards.py`) checks each reward against the balances of the pinned sync aggregate vectors, the proposer with its share.
It checks the selection of named members once each, by index or key, and code 400 for an invalid identifier and for a state before Altair.

The block rewards are in the same module, read from the state at the slot of the block, before it.
`blockRewards` runs the steps of the block before its operations, then the proposer slashings, the attester slashings and the attestations, as the block does.
Each of these three parts is the rise of the proposer's balance over its step; from Altair the sync aggregate part is the share of the proposer that the sync aggregate step computes, times the number of signatures.
`processBlock` itself runs these steps through `stateBeforeOperations`; `processBlock_stateBeforeOperations` shows that it then runs its operations and its sync aggregate on that state.
`stateBeforeOperations_ok_iff` shows that this state is the input that `processBlock` gives its operations, and `blockRewardsResponse_ok` that an answer is the JSON of `blockRewards`.
`blockRewards_total` shows that the total is the sum of the four parts and that the answer names the proposer of the block, as the source says.
`blockRewards_syncAggregate` shows that from Altair the sync part is the share of the step times the number of signatures, and `blockRewards_of_lt_altair` that before Altair the sync and attestation parts are zero.
`blockRewards_balance` shows that the operations and the sync aggregate raise the proposer's balance by exactly the total.
It assumes that the proposer has a balance, and that the block does not slash it, holds no deposit to its key before Electra and, from Electra to Fulu, no consolidation request from its key; the last three change the balance by other amounts.
It also assumes that the proposer holds no seat in the sync committee, whose reward or penalty its balance would add, and that the mixes span more than the seed lookahead plus two epochs, so that every step reads the same proposer.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_block_rewards.py`) runs the blocks of the pinned random, finality and sanity vectors.
It checks the total, the sync part against a share computed from the active balance, and, up to Fulu, the change of the proposer's balance less its withdrawals under the hypotheses above.

The consensus value of a produced block is in `Consensus/BeaconApi/Produce.lean`: the total of its block rewards, at 10^9 Wei per Gwei, as the source describes the value "in Wei paid to the proposer".
`consensusBlockValue_ok_iff` (`Consensus/Proofs/BeaconApi/Produce.lean`) shows that it is that total, and `consensusBlockValue_balance` that, under the hypotheses of `blockRewards_balance`, it is the rise of the proposer's balance over the operations and the sync aggregate, in Wei.
One Gwei is 10^9 Wei through one constant that the execution layer shares, in `Base/Denominations.lean`.
Its export is tested against the block rewards of the pinned random, finality and sanity blocks.

The choice between the local payload and a builder's payload is in the same module.
Through Fulu, `preferLocalV3` is the rule of the v3 endpoint, and `preferLocalV3_zero` shows that a factor of zero keeps the local payload.
From Gloas, the containers of the builder configuration of the v4 endpoint are in `Consensus/Containers/BuilderConfig.lean`, with the terms that each gives to a bid.
`selectPayload` drops the bids that their terms refuse, keeps the first one of largest weight, and commits to it only when its weight beats 100 times the local value.
`selectPayload_accepted`, `selectPayload_max` and `selectPayload_beats_local` show that a chosen bid is accepted, weighs the most and beats the local payload.
`selectPayload_eq_none_iff` shows that the local payload is kept exactly when no accepted bid beats it, so it wins a tie.
`selectPayload_map` shows that a change of bids that keeps their signers, terms and values keeps the choice.
`selectPayload_cap` shows that changing an execution payment at or above its cap to another at or above it keeps the choice, and `bidWeight_lt` that a weight fits in 128 bits.
The Python tests check the factors 0, 100 and 2^64 - 1 that the source names, and the saturation of a bid's value at 2^64 - 1.
Four points of the source are decided here, and a reviewer may question them:

- The v4 rule compares a bid in Gwei with the local value that the Engine API gives in Wei; the comparison multiplies the bid's weight by 10^9, so no value is rounded.
- A bid received on gossip has no cap in the source, so its terms count the whole execution payment, up to the saturation at 2^64 - 1.
- The source does not order two bids of the same weight; the first one in the list wins, which the Python tests check.
- What makes a builder payload safe in v3 is the node's choice, so the rule takes the two values once both are valid.

The URL of a builder entry is a JSON string, and its SSZ form holds the UTF-8 bytes of that string.
EthLib holds it as a Lean string, which is valid UTF-8, within the limit of 2048 bytes (`SszString` in `Serialization/Ssz/Typed/Text.lean`).
The JSON codec writes it with the text spelling, so a URL such as `"0x12"` is never read as hex.
`SszString.ofValue_toValue` (`Serialization/Proofs/Ssz/Typed/Text.lean`) shows that decoding the bytes of a URL gives it back.
`SszString.ofValue_bytes_notUtf8` in the same file shows that SSZ bytes that are not UTF-8 are refused.
So the type is not lawful, and `BuilderEntry.ofApiJson_toApiJson`, `BuilderConfig.ofApiJson_toApiJson` and the two `toApiJson_total` theorems (`Consensus/Proofs/BeaconApi/BuilderConfig.lean`) stand in for the general ones.
`jsonOf_ok` and `valueOf_jsonOf` hold for every value.
Bytes that are not UTF-8 have no text, so the codec writes them as one decimal string per byte.
It reads such an array only when its bytes are not UTF-8, which `valueOf_text_digits` (`Serialization/Proofs/Ssz/Codec/JsonLaws.lean`) shows for the decimal strings that the codec writes; the reader accepts no others.
A typed URL never has such bytes, so the reader of a builder entry accepts only a string.
The Python tests check that the example configuration of the source reads back from JSON and from SSZ.
An entry with an empty URL or empty authentication data, or whose authentication names another slot, gives no bid.
The other entries and the gossip terms still apply, since the source says that one bad entry never fails the request.
The source forbids two entries with one URL and one authentication data, and EthLib keeps the first of them.
A candidate bid takes its signer from the registry, for the builder that the bid names, so its signature must have been checked first.
The source limits a URL to 2048 characters in JSON and to 2048 bytes in SSZ, and EthLib follows the bytes.
So a URL of 1025 two-byte characters is refused in both encodings.
A body whose URL breaks a limit of its type cannot be decoded, so the whole request fails with 400, as the source says of such a body.
EthLib counts SSZ bytes that are not UTF-8 in the same way: they are not "UTF-8 bytes of `url`, exactly as in JSON", and no JSON body holds them.
A reviewer may question this, since the SSZ type of the source is a plain byte list, which would make such an entry fail alone.
The JSON parser reads a lone surrogate escape in a string as U+FFFD, so `"\ud800"` and `"\ufffd"` name one URL; RFC 8259 §8.2 leaves such strings to the implementation.
A URL is checked only to be non-empty, not to be a valid URI.

The topics and the messages of the event stream are in `Consensus/BeaconApi/Events.lean`, shared by the events of received objects (#2090) and of the fork choice (#2091).
`EventTopic.ofName?_name` and `EventTopic.name_injective` (`Consensus/Proofs/BeaconApi/Events.lean`) show that each of the 24 topics of the source has its own name, which gives it back.
`readEventTopics_names` and `readEventTopics_map_name` show that a request is read exactly as the topics that it names, and `eventStream_cons` that the stream is the message of the first event, if its topic was chosen, followed by the stream of the rest.

The events of the fork choice are in `Consensus/BeaconApi/ChainEvents.lean` (#2091).
`chainEvents` compares two stores: a head event comes when the head block changes, or when it stays and its payload moves from empty to full; a reorganization comes when the old head block is not an ancestor of the new head; a finalized event comes when the finalized checkpoint changes.
`chainEvents_head_iff` and `chainEvents_reorg_iff` (`Consensus/Proofs/BeaconApi/ChainEvents.lean`) show when a head event and a reorganization come.
`chainEvents_head` shows that a head event names the head of the later store, and `chainEvents_dependent_roots_duties` that its two dependent roots are those of the attester duties of its epoch and of the next one, read from the head state; the second needs the next epoch to fit in 64 bits.
`computeEpochAtSlot_succ_lt` shows that it does for every slot when an epoch has at least two slots.
`chainEvents_finalized_iff` shows that a finalized event comes exactly when the finalized checkpoint changes, and `chainEvents_finalized` that it names the block and the epoch of the new checkpoint.
`chainEvents_finalized_epoch` shows that the epoch of a finalized event is above the finalized epoch of the earlier store, when the finalized checkpoint advances from one store to the other.
`Store.CheckpointsAdvance` (`Consensus/Proofs/ForkChoice/Handlers.lean`) says that each of the justified and finalized checkpoints stays as it was or moves to one at a greater epoch.
A checkpoint is replaced only by one at a greater epoch.
So the tick, the block, the attestation, the attester slashing, the envelope and the inclusion list each relate the store before to the store after, by their frame theorems.
A vote of the payload committee changes only the votes (`onPayloadAttestationMessage_onlyPtcVotes`), so it relates them too.
`Handles.checkpointsAdvance` (`Consensus/Proofs/ForkChoice/Network.lean`) gathers these for every move of a store, and `chainEvents_finalized_epoch_of_handles` states the result after one move.
`fastConfirmationEvent_block` shows that the event of a run of the fast confirmation rule names its confirmed block and that block's slot.
The source leaves these points open, decided here:

- `epoch_transition` is given only by example; it is true when the new head is in another epoch than the old head, later or earlier.
- The `depth` of a reorganization is given only by example; it is the slot of the old head less the slot of the latest common ancestor of the two heads.
- The `epoch` of a reorganization is given only by example; it is the epoch of the new head.
- From Gloas, a reorganization compares blocks, not payloads: a new head built on the old head block without its payload is no reorganization.
- The `state` of a finalized event is the state root of the checkpoint block, not the state of the checkpoint.
- From Gloas, the `state` of a head event is the state root of the block, also when its payload is full.
- Emission on other payload transitions is optional, so a head event comes only on the transition from empty to full that the source requires.

The optimistic flag of each event is an input, since it depends on what the node has verified.
The event of the payload attributes is in `Engine/BeaconApiEvents.lean`, since it needs the types of the Engine API.
`payloadAttributesEvent_fields` (`Engine/Proofs/BeaconApiEvents.lean`) shows that the Engine API and the event write the fields of the attributes from one list.
The event writes each name in snake case and each integer as decimal text, where the Engine API keeps the name and writes the integer in hexadecimal.
`payloadAttributesEvent_spec` shows that the event names the slot of the state, the proposer that the state gives, the root of its latest block header and the head of the forkchoice update.
`payloadAttributesEvent_prepareExecutionPayload` shows that before Gloas, for the update of a proposer, the event names the head that the proposer chose, from Deneb the parent root of the attributes, and the slot that gives their timestamp.
`payloadAttributesEvent_prepareExecutionPayloadGloas` shows the same from Gloas, for the event of the state that the attributes read: it names the parent on which the proposer builds, the safe and finalized blocks given, the parent root of the attributes, and their slot number, which gives their timestamp.
Until Gloas, the number of the parent execution block is that of the latest payload header of the state.
Before the merge the parent is a block of proof of work, which the state does not describe, so the caller gives its number.
The event covers Bellatrix to Gloas (the forks before Heze), and these gaps remain:

- From Heze, the fifth version of the attributes adds the transactions of the inclusion lists, which the attributes of EthLib lack, and the pinned API names no consensus version for Heze, so the event is not defined there.
- The parent root is the root of the latest block header of the state, which is right only for a state at the slot of the proposal, after its empty slots; the event takes that state as given.
- How often the event is sent may depend on the node, so only its content is specified.

The Python suite (`bindings/python/tests/consensus/test_beacon_api_chain_events.py`) compares the events between two checks of the head in five pinned fork choice cases, from Capella to Gloas, with the events that the checks call for.
A case with more than 20 checks of the head compares only the pairs of checks that call for an event, and the first pair without an event after them.
It works out the dependent roots, the reorganization depth and the state roots from the blocks of the case.
It also checks the event of each run of the fast confirmation rule in three pinned cases against the confirmed root and the clock of the checks, also when the clock moves on after the run.
The Python suite (`bindings/python/tests/engine/test_payload_attributes_event.py`) checks the event of the payload attributes from Bellatrix to Fulu, before and after the merge, and at Gloas on the full and the empty parent of a pinned fork choice case.
It compares each event with the forkchoice update of the same proposer, spelled again in Python with snake case keys and decimal integers, and with the proposer and the parent root that the state gives.
The light client events and the event of an available payload depend on what the node has received, and are not defined here.

The events of received objects are in `Consensus/BeaconApi/ObjectEvents.lean` (#2090).
An object from a peer and one from a client take the same path: the gossip dispatch, then, for a block or an envelope, the handler of the fork choice.
`eventsOfGossip_accept` (`Consensus/Proofs/BeaconApi/ObjectEvents.lean`) shows that an object whose topic has an event gives it exactly when gossip accepts the object.
`receiveGossip_accept` shows that any event of a received message means that the dispatch accepted it.
`receiveGossip_of_pass` and `publish_receiveGossip` show that a message which passes the gossip check of an endpoint, or which a publish endpoint does not refuse, gives the events that it gives from a peer.
`itemEvents_singleton_of_pass` and `itemEvents_singleton_of_fail` show that the gossip event of an item of one message follows the same check.
`eventsOfBlockImport_block` shows that a block event names a block that is new to the store and that the store then holds, and `eventsOfBlockImport_new` that such a block gives it.
`blockEvent_gloas` shows that from Gloas a block event names the builder and the block hash of the bid of its block, and none before.
`eventsOfEnvelopeImport_ok` and `eventsOfEnvelopeImport_of_accepted` show that an envelope is imported exactly when the envelope handler accepts it, and that the store then counts its payload as verified.
`envelopeEvent?_eq_some` shows that it gives a payload event exactly when its payload is new to the store.
`publishBlock_eventsOfBlockImport` and `publishEnvelope_eventsOfEnvelopeImport` show that an object that a publish endpoint integrates gives the store and the events of an import.
`publishBlockEvents_integrated` and `publishEnvelopeEvents_integrated` show that such an object gives its gossip event, then its import event; `publishBlockEvents_of_fail` and `publishEnvelopeEvents_of_fail` show that an object that fails gossip gives none.
The source leaves these points open, decided here:

- The payloads are fixed only by examples; the field names and kinds come from them, and an object that an event carries is written whole in the JSON of the API.
- The source does not say whether an object gives two events when it arrives twice. Each acceptance by gossip gives one gossip event; the rules of a topic ignore a copy whose keys they have seen. A block that the store already holds gives no block event, since the block handler then leaves the store as it was; an envelope whose payload the store already holds gives no payload event.
- An object that passes gossip at a publish endpoint gives its gossip event even when a later check of its level refuses it, since the source names only the rules of the topic.
- The example of the `attestation` event has the form of Electra, with committee bits, but from Electra the attestation subnets carry single attestations. Turning one into an attestation needs its committee, which the source does not specify for the event. So the `attestation` event comes before Electra, and the `single_attestation` event from Electra.
- The source lists only the network as the origin of the payload attestation event, unlike the other gossip events. Here a payload vote submitted through the API gives it too, since it passes the same rules.
- The aggregate, sync committee message and inclusion list topics have no event in the source, so they give none. The release removed the blob sidecar event, so blob sidecars give none at Deneb and Electra.
- The slot of a payload event is the slot number of its payload, which gossip and the envelope handler check to equal the slot of its block.
- The bid, payload vote and proposer preferences events name the consensus version of the fork, as their examples do. The source names no version for Heze, so from Heze these events carry none.

The optimistic flag of a block is an input, as for the events of the fork choice.
The pool and publish export gives the events of each request, and another export gives the event of one object that gossip accepts.
The Python tests check that each example of an object that an event carries whole is the event of that object.
They check the block, payload and column events against the gossip vectors, with block roots that the SSZ export computes where the object holds none.
The pool tests check that a request gives the event of its topic exactly for the objects that gossip accepts, and the publish tests check the events of blocks and envelopes.
The import events come only through the publish endpoints; the fork choice and gossip exports give no events.
The execution layer of the export accepts every payload, so no event there is optimistic.
The `attestation` example is checked without its committee bits, before Electra.

The debug answers show the tree of the fork choice and its leaves (`Consensus/BeaconApi/Debug.lean`).
`mem_treeNodes` (`Consensus/Proofs/BeaconApi/Debug.lean`) shows that the listed nodes are exactly the nodes of the tree, and `nodeViews_nodes` shows that the views follow that list, by root and status as the API names them: one per block before Gloas, and from Gloas the pending and empty nodes of each block, with the full node once its payload is verified.
`treeParent_eq_some_iff` shows that a node of the tree names another as its parent exactly when that node is in the tree and the store gives the first as one of its children.
`nodeView_parent` shows that a view reports that parent, by root and by status.
`nodeViews_preGloas_full` shows that before Gloas the views are one per block, and that each has the status full, as the source says.
`chainHeads_head` shows that when some leaf below the justified block is viable, the block of the head is among the chain heads.
`mem_chainHeads_iff` describes the list exactly: a root is listed exactly when one of its nodes is a leaf of the tree, and `chainHeads_nodup` that each root is listed once.
`nodeView_ptcCounts` shows that the three counts of the payload committee in a view are those of its block, so every node of one block has the same counts.
`ptcCounts_le` bounds each count by the size of the committee, and puts the votes for on time among the recorded votes; `ptcCounts_preGloas` gives zero before Gloas.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_debug.py`) builds the stores of pinned fork choice cases of Capella, Deneb and Gloas.
It checks the blocks, slots and parent roots against the bytes of the cases, the checkpoints, the full nodes and the committee counts against their steps and checks, the heads before Gloas against the blocks without children, and the validity of an optimistic block.
It checks that the weights before Gloas lead from the justified block to the head of the case.

The pool endpoints validate each submitted object by the gossip rules of its topic (`Consensus/BeaconApi/Submit.lean`).
They call the same dispatch as gossip, `validateGossipMessage` (`Consensus/Gossip/Message.lean`).
`validateGossipMessage_outcome` and `validateGossipMessage_eq_error` (`Consensus/Proofs/Gossip/Message.lean`) show that the dispatch returns the outcome of the validator of the topic, and fails only when that validator fails.
`validateGossipMessage_of_not_accept` shows that an ignored or rejected message leaves the keys seen as they were, and `GossipMessage.record_of_accept` that the keys of an accepted message can always be recorded.
`messageFailure_of_ok` (`Consensus/Proofs/BeaconApi/Submit.lean`) shows that a message fails exactly when gossip does not accept it, with the reason of gossip and the same keys after it.
`messageFailure_of_error` shows that an error of the fork choice fails the message, with the keys from before it.
`validateItem_single` shows that an item of one message answers as that message, and `validateItem_cons` that an item fails with the reason of its first message that fails.
`submitList_failures` shows that the entry of the answer at a position is the failure of its item, given the keys after the items before it.
`submitList_failures_pairwise` shows that the answer names the failed positions in increasing order, so each once, and `submitList_failures_lt_length` that each lies within the list.
`submitList_accepted_iff` shows that the answer is a success exactly when no item fails, and `submitList_failed_ne_nil` that a failed answer names at least one item.
`PoolRequest.ne_nil_of_mem_items` shows that every item of a request has at least one message.
`syncSubnets_pairwise` shows that the subnets of a sync committee message come once each, in increasing order.
`mem_syncSubnets_of_seat` shows that a validator that holds a seat gets the subnets of its seats.
`syncSubnets_of_no_seat` shows that any other validator gets subnet 0 alone, as does a message whose head state, validator or sync committee cannot be read.
`validateItem_syncSubnets_seat` shows that an item of a sync committee message passes only if its validator holds a seat in the sync committee of the slot after the head state.
It rests on `seat_of_validateSyncCommitteeMessage_accept` (`Consensus/Proofs/Gossip/SyncCommittee.lean`): gossip accepts a message only on a subnet of a seat of its validator.
`submitPool_syncCommitteeMessages_seat` shows the same for each message of an accepted request.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_pool.py`) submits each object of the pinned gossip cases of the pool topics to its endpoint.
It checks that the object fails exactly when gossip does not accept it, with the reason of the case.
It leaves out the cases whose reason is a wrong subnet, since the node picks the subnet itself, and the cases that send objects of another topic.
No case submits a sync committee message from a validator with no seat; only the theorems above cover it.
Every case of the bid topic also sends the envelopes of payloads, so those cases run in the suite of the publish endpoints.

The publish endpoints of blocks and of payload envelopes check an object at the level that the client asks, before the node broadcasts it (`Consensus/BeaconApi/Publish.lean`).
The gossip checks of its topic run at every level, through the same dispatch as gossip.
The consensus level adds the checks of the object against the state before it, with its signatures.
For a block that is the state transition, with no verdict of the execution layer on the payload; for an envelope, the checks of the envelope with that verdict.
The highest level also checks that the store holds no other block of the same slot and proposer.
`publishBlock_refused_store` (`Consensus/Proofs/BeaconApi/Publish.lean`) shows that a refused block leaves the fork choice store and the messages seen as they were.
`publishBlock_gossip` shows that every other answer means that gossip validation accepts the block, with its slot and proposer seen after it.
`publishBlock_consensus` shows that above the gossip level such an answer also means that the consensus checks of the block pass.
`publishBlock_noRival` shows that at the highest level the store then holds no other root with the slot and proposer of the block.
`hasRival_iff` describes such a rival exactly.
`publishBlock_integrated` shows that an integrated block gives the store of the block handler of the fork choice.
`publishBlock_broadcastNotIntegrated` shows that a block broadcast but not integrated fails that handler, and that the node keeps its store.
`publishBlock_of_pass` shows the converse: a block that gossip accepts and that passes its level is broadcast, and integrated exactly when the handler succeeds.
The envelope endpoint has the same theorems, from `publishEnvelope_refused_store` to `publishEnvelope_of_pass`, against the gossip checks and the handler of envelopes.
`levelFailure_eq_none_iff` shows that an object passes its level exactly when its gossip checks pass and, above the gossip level, the later checks of its level pass.
The Python suite (`bindings/python/tests/consensus/test_beacon_api_publish.py`) sends each object of the pinned gossip cases of blocks, envelopes and bids to its endpoint, in turn, against one store.
It checks that a block or an envelope is refused exactly when gossip does not accept it, with the reason of the case, and that a bid fails exactly then.
It checks that a valid block and a valid envelope get 200 at every level, and that a second copy is then refused as already seen.
It checks that the consensus levels refuse a block with a wrong state root that gossip accepts, and that the default level is the gossip level.
It checks that the highest level refuses a valid block whose rival the store holds, and that the consensus level does not.
The export behind it (`Consensus/Exports/BeaconApiPost.lean`) runs a node whose clock reaches the time of each request, which holds no blobs, and whose execution layer accepts every payload.
So a block with blobs before Fulu gets 202, while from Fulu the node takes the data on trust; it never integrates the block of the merge, and from Heze every payload satisfies the inclusion lists.

Points that remain open:

- The reader refuses a key that a container does not declare, while the source says that a field may be added to the data without a new version.
- The source types the codes of the error bodies as JSON numbers; EthLib reads a number whose value is a natural number.
- The source writes each integer leaf as a string, and its pattern for `Uint8` admits leading zeros; the JSON mapping of SSZ also reads a bare number, and refuses leading zeros.
- The source defines no schema for Heze, or for containers such as `SigningData`, so their spellings are checked by review only.
- The API defines no inclusion list yet, so the hex form of its transactions follows the form of a transaction in the API.
- The source does not say whether `finalized` and `justified` name the state after the checkpoint block or the checkpoint state; EthLib reads the state after the block, which may sit before the checkpoint epoch.
- The source does not say which state a slot without a block names; EthLib names none, so such a request gets no state, and the root of such a state names none.
- The source does not say whether a slot or an index may carry a sign or leading zeros; EthLib refuses both.
- The source does not say whether blocks outside the fork choice store are canonical; EthLib resolves only the blocks that the store holds.
- A store anchored after genesis names no block at genesis, or below its anchor; a head that cannot be computed makes the head, genesis and slot identifiers name nothing.
- The source says that the spec map should include the constants of each known fork, and its example has a domain; EthLib gives only the configuration and the presets, and leaves the choice of constants to the maintainers.
- The source does not say whether a fork scheduled at the farthest epoch is one that the node "is aware" of; EthLib lists it.
- The source does not say which state answers a query for the attestation rewards of an epoch; EthLib takes the state at the last slot of the next epoch, before its slot step and its epoch transition, since the slot step changes no root that the rewards read, and refuses a state of the first epoch, whose transition applies no rewards, with code 404.
- The source defines the ideal rewards only as "Ideal rewards info"; EthLib gives, for each effective balance of the eligible validators, the parts of a validator that voted right, included one slot after its vote before Altair, and leaves the definition to the maintainers.
- Before Altair, the inclusion deltas also hold the shares a validator earned as the proposer that included votes; the source calls the part the attester's inclusion reward, so EthLib leaves those shares out of it.
- The request body of the attestation rewards and of the sync committee rewards is a set of identifiers; EthLib accepts a repeated identifier and answers for it once, and an identifier that names no validator, or no member, gets no entry.
- The ideal rewards cover only the effective balances of the eligible validators, whichever validators the request names.
- The source does not say which state answers a query for the sync committee rewards of a block; EthLib takes the state that the sync aggregate step of the block reads.
  It does not check the signature of the aggregate, which the block passed.
- The source does not say whether the reward of a member whose balance a penalty takes to zero is the nominal penalty or the change of the balance; EthLib reports the nominal amount, so the penalty in the entry of such a member can exceed what its balance lost.
- The source answers for every member when no array is provided; EthLib cannot tell an absent body from an empty array, and answers both for every member.
- The source requires the topics of a subscription; EthLib reads an empty list as a subscription to no topic, and refuses an unknown name with code 400 and the example message of the source.
- The source declares the topics of a subscription unique; EthLib accepts a repeated topic, and sends each event once.
- The source does not say which state answers a query for the block rewards; EthLib takes the state at the slot of the block, before it, and does not check the signatures of the block, which was imported.
- The source does not say what the attestations of a block before Altair pay; their proposer earns its share at the end of the epoch, so EthLib reports zero for them.
- A slashing part is the rise of the proposer's balance; for a block that slashes its own proposer that rise can be less than the whistleblower reward, or zero.
- The proposer is the whistleblower of the slashings of its block, so a slashing part holds the whole whistleblower reward, not only the share that the transition calls the proposer reward.
- The source lists codes 400, 404 and 500 for the block rewards; EthLib answers a block that fails its steps with code 500, since the block was imported.
- The block rewards run the block only up to its attestations, and from Altair its other operations; they do not run the sync aggregate step, so an aggregate that the step would refuse still gets a sync part.
- From Gloas the block also records a payment to a builder; the source does not say whether the total includes it, and EthLib leaves it out, since it does not change the proposer's balance in the block.
- The reward of a member that is also the proposer leaves out the proposer share of each signature, which the block rewards count.
- The source does not say what a block before Altair, which has no sync aggregate, gives; EthLib answers with code 400 and the example message of the source.
- The source does not order the entries of the sync committee rewards; EthLib lists them in increasing order of index.
- The source does not say whether the genesis fork version is the one of the configuration or the one that the genesis state holds; EthLib reads the configuration, which the domain of a deposit uses, so a chain that starts at a later fork reports a version that its genesis state does not hold.
- `forkSchedule_upgrade` assumes that the state before the upgrade holds the version of its own fork.
  `currentVersion_of_chainSteps` shows it for each state of a chain whose first state holds the version of its fork.
  `currentVersion_of_genesis_chainSteps` discharges that for the genesis state that deposits build, which is before Altair.
  `Store.Reachable.blockStatesFromParents` links each state that a store keeps to the state of its parent by a state transition.
  No theorem yet shows that this transition keeps the fork versions, or that an anchor holds the version of its fork.
  So the answers of the API are not covered.
- The format rule of the spec map names hex, numbers and arrays only; EthLib writes the names of the preset and of the configuration as text, as the files do.
- The source has the `randao` query answer "Invalid state ID or epoch" with code 400, and its example message is "Epoch is out of range for the `randao_mixes` of the state", but it names no range.
  EthLib reads the circular buffer at the epoch modulo its length and refuses no epoch.
  So an epoch outside the window that the buffer holds gives the mix of another epoch.
- The source says that a state before finalization reports epoch 0 and the zero root.
  `finalityCheckpoints_of_genesis_chainSteps` covers each state that a chain from the Phase 0 genesis state of deposits reaches.
  No theorem yet ties the states that a store keeps, from any anchor, to such a chain, so the answers of the API are not covered.
- The source puts the `Eth-Consensus-Version` header on the SSZ answers too; the SSZ export gives the bytes only, and the version is the one of the JSON answer.
- The source fixes the proposer lookahead at 64 items, the mainnet value; EthLib follows the preset, as the SSZ type of the source does, so the minimal preset gives 16.
- The schema describes the nine validator statuses in words only.
  EthLib takes their conditions from the validator status document that the schema links, which is not a pinned file.
- The source asks for updates "in consecutive order (by period)", which may mean increasing periods or periods with no gap; `IsUpdatesAnswer` asks only for increasing periods.
- The source writes the context of an updates chunk as the digest of a fork version and the genesis validators root, the form before Fulu.
  EthLib takes the digest of the epoch of the attested header, which from Fulu also depends on the blob schedule.
- The source bounds the range of the updates answer by the period of the head; the answer leaves that bound to the updates that the caller gives.
- Which update is the best of a period, and which update is the latest, depend on what the node has seen; the answers take them as input.
- The source names no consensus version for Heze, so the answers on a Heze state carry no version, although the schemas list it as required.
- A value that the node cannot encode or compute has no error of its own in the source.
  EthLib gives code 500, the code of the source for an internal error.
- A public key names the first validator of the registry that holds it; the source does not say which validator a key held twice names.
  A deposit adds a validator only for a key that the registry does not hold, so this matters only for a state built by hand.
- The schema marks the lists of identifiers and of statuses as unique, but gives no code for a repeated item.
  EthLib accepts a repeated item, and gives each entry once.
- The source names no epoch for the status in the validators answer; EthLib takes the current epoch of the state.
- The source gives no list type for the SSZ body of the identities answer, so EthLib defines its JSON only, and no answer for a request of SSZ.
- A state whose balances are fewer than its validators gives no entry for an index without a balance, in the validators and balances answers.
  The transition keeps one balance per validator, so this too matters only for a state built by hand.
- The reader of a request checks the count of identifiers before it reads them, so a long list with a bad identifier gets code 414; the source does not fix this order.
- The source does not say which epochs the committees answer accepts.
  EthLib accepts the epochs up to the next one, as the honest validator guide does for an assignment.
  It also refuses an epoch whose seed would read a RANDAO mix that the state has overwritten, since its committees would use the mix of another epoch.
  Both refusals get code 400.
- The committees answer gives code 400 for a slot filter outside the epoch, as the example of the source does.
  An index filter only restricts the list, so an index that names no committee gives an empty list.
- The sync committees answer does not compare the epoch with the Altair fork epoch.
  When Altair starts inside a period, an epoch of that period before the fork gets the committee that the upgrade made.
- The PTC answer gives the same message for a slot before the Gloas fork epoch and for a slot outside the window; both get code 400.
- A key of a sync committee names the first validator of the registry that holds it; the source does not say which validator a key held twice names.
  A key that no validator holds gives code 500.
- The source has the sync committees answer read "the current sync committee", but takes an epoch; EthLib answers the committee of the period of the epoch, the current one or the next, and gives code 400 for any other period.
- Every error of the PTC answer has code 400, since the source names no other code for a slot that the window does not hold.
- The blinded block endpoint "only supports forks through Fulu" and names no code for a later block; EthLib gives code 400.
- The blobs answer reads an empty list of versioned hashes as a request for no blob, since the parameter is then specified.
  The schema marks the hashes as unique but gives no code for a repeated one; EthLib accepts it.
- The block answers take the signed block as an input, since the store of the fork choice keeps blocks without their signatures.
- The blobs answer takes the blobs of the block as an input, one for each commitment; another count gets code 500.
  Which blobs a node keeps, and whether it rebuilds them from columns, is its own matter.
- The headers endpoint fetches "current head slot blocks" by default; EthLib reads this as the slot of the head block, not the slot of the clock.
  It uses that slot only when neither filter is given.
  With only a parent root, it keeps every slot.
  A store without a head then gets code 500.
- The headers answers take the signed headers that the node holds, of any fork, as an input.
  A block is canonical when it is the ancestor of the head at its own slot.
  Canonicity is decided against the blocks of the store, so a block below the anchor is reported as not canonical.
- The columns answer takes the sidecars that the node holds for the block as an input, and names the consensus version of the fork.
  It gives the order of the input, which the source leaves free.
  An empty list of indices requests no sidecar, since the parameter is then specified.
  The input is assumed to hold at most one sidecar for each index, the sidecars of one block.
  The source lists the versions Fulu and Gloas only; EthLib gives code 400 before Fulu.
- The envelope answer takes the signed envelope as an input, since the store keeps envelopes without their signatures.
  It compares the hash tree roots of the two messages, and gets code 404 when they differ.
  It does not check the signature of the given envelope; the caller vouches for it.
  Before Gloas it gets code 404, since no envelope exists; the source names only the version Gloas.
- From Hegotá the envelope and columns answers carry no version, since the source names none for that fork yet.
- The source gives no SSZ body for the attestations answer; EthLib gives none.
- The source does not say which state answers a duty request; the duty answers take the state as an input.
- The attester epoch "Should only be allowed 1 epoch ahead"; EthLib refuses a later epoch with code 400.
  The PTC epoch "Must not be greater than the next epoch"; EthLib refuses a later one with code 400 too.
  Both answers also refuse an epoch whose seed the mixes of the state do not hold, as the committees answer does.
  The PTC answer also refuses an epoch before the previous one, or before Gloas, which the window of the state does not hold.
  An epoch too old for the block roots of the state gets code 400 when its dependent root is read.
- The source asks for at least one index in the attester, sync and PTC requests; an empty request gets code 400.
- The proposer duties read the lookahead of the state from Fulu, for the current epoch and the seed lookahead.
  Before Fulu they are drawn for the current epoch only, since later effective balances are not known yet.
  Another epoch gets code 400.
- The second version of the proposer endpoint uses a lag of one for its dependent root at every fork, as the source writes it.
- The first version of the proposer endpoint answers for the current epoch only, since the root at the last slot before a later epoch is not known yet.
- The dependent root is read from the block roots of the state, which must be past that slot and still hold it; otherwise it gets code 400.
  The caller supplies the genesis block root, which EthLib does not check.
- An index that names no validator of the state gets code 400; a validator with no duty in the epoch is left out.
  The PTC request asks for distinct indices, so a repeated one gets code 400.
  The attester and sync requests do not, so a repeated index gives its duty once for each time it is named.
- The sync duties answer for the current period or the next, since the state holds only those committees; another period gets code 400.
- The attestation data takes the status of the head payload from the fork choice, as the guide does, since the source leaves it to the node.
  The deprecated committee index is read before Electra only, and a request without one passes 0.
- The source does not say which slots the attestation data accepts; EthLib takes the state of the head through the empty slots.
  It gives code 400 for a slot before the head, or after the current slot of the store.
  A head whose payload is not yet verified gets code 503 before the slot is checked against the current slot.
- The payload attestation data takes its two flags as inputs, since they record what the node has seen; its 503 for a syncing node is out of scope.
- The aggregate and contribution answers take the collected messages and the state as inputs; which messages a node keeps is its own matter.
  The aggregate takes the data of the first matching message, and joins every message with that data, and from Electra with the requested committee.
  Before Electra, overlapping aggregates in the pool give an aggregate whose signature does not verify.
  Each fork reads one of the two lists of messages: the attestations before Electra, the single attestations from Electra.
- The store of the fork choice holds one fork, so a slot of a later fork gets attestation data under the rule of the store's fork.
- Before Electra the attestation data does not check the committee index against the count of committees of the slot.
- The payload attestation data does not check that its block is verified.
- The payload attestation data answers code 204 when the chain of the head has no block at the slot, even if the store holds one off that chain.
- From Electra a committee index out of range with no matching message gets code 404, since the match comes before the range check of the aggregate.
- The source names no code for a subcommittee index that names no subnet; EthLib gives code 400.
- The contribution answer requires the slot of the state, and joins the messages of the sync committee of the next slot, as gossip checks them.
  It keeps only the messages of validators with a key of the requested subcommittee, so the messages of other subcommittees do not refuse the request.
  A message of a validator that the state does not know is left out too.
- The weight of a view is "the raw stored weight" of the node; EthLib gives the weight of the head computation, with the votes of the justified state and the proposer boost.
  From Gloas that weight is zero for the empty and full nodes of a block of the previous slot.
- The checkpoints "recorded for this fork choice node" are read as those of the state after the block, not the unrealized ones that the store keeps.
- A view never has the validity `invalid`, since the store drops the blocks that build on an invalid payload.
  A pending or empty node from Gloas reads the payload that its block builds on, as its block hash does; a payload before the anchor counts as valid.
- The attester count reads the votes on time: a vote of the committee records both of its answers.
- The chain heads are the nodes without a child, each block once; from Gloas the leaf can be the empty or the full node of the block.
  So from Gloas a block whose children all build on its full node is listed, through its empty node, although it has children.
  The source gives the heads as the "leaves of fork choice tree" and names no payload status, so EthLib keeps that literal reading.
  The flag of a head is set when a leaf of its block ends at an optimistic payload, as the validity of that leaf in the fork choice answer.
- The execution block hash is zero before Bellatrix, where a block has no payload.
- The fork choice answer fails with code 500 when the store lacks a state after a block, the justified checkpoint state, or another input of the weights of the head computation.
  The heads answer fails only when the optimistic store cannot read the payload chain of a block; the exports build that store from the blocks of the store.
- The store holds the blocks of one fork, so a store at the Gloas transition, with a full node for each block before Gloas, is out of reach.
- The extra data "may differ between clients"; EthLib gives an empty object.
- The source does not say whether a gossip `ignore` counts as a failure of a pool submission; EthLib counts it, since an ignored object is not published.
- The source fixes the position of a failed item, not its message; EthLib gives the reason of the gossip rule that failed.
- The pool endpoints take the items in order, and the keys of a valid item apply to the next ones, so a list that repeats an object fails at each copy after the first.
- The node picks the subnet of an attestation from its head state, and validates a sync committee message once on each subnet that holds a seat of its validator.
  When it finds no subnet, it validates the object on subnet 0, where gossip fails at or before its check of the subnet.
  The order of the checks of the validators gives this.
  For a sync committee message, `syncSubnets_of_no_seat` and `validateItem_syncSubnets_seat` state that such an item goes on subnet 0 alone and fails.
  No theorem states which check fails, and none covers an attestation.
  For a sync committee message, the first check of gossip reads the keys seen on that subnet.
  So with keys seen under another head, the reason on subnet 0 can be "already seen" where another subnet would give a wrong subnet.
- A sync committee message is validated on every subnet, and each subnet where it passes keeps its keys; the item fails with the reason of the first subnet where it fails.
- An error of the fork choice on one message, such as a slot whose time leaves the 64-bit range, fails that message alone, with the keys seen before it, so the other items keep their answers.
  The source names no code for it; EthLib reports it among the failures of the 400 answer.
- The source excludes the transactions of a payload from the consensus checks of a block, and does not say which checks of the payload that removes.
  EthLib keeps the checks of the payload hash and of the versioned hashes, and the refusal of an empty transaction.
  It skips the verdict of the execution layer on the payload, and assumes that the layer answers from its checks.
- The source does not say whether the consensus level adds to the gossip checks or replaces them; EthLib runs both, since a success means that the gossip checks passed.
- The source does not say which blocks the equivocation check compares against; EthLib compares against the blocks of the fork choice store, by slot and proposer.
  For a block, the gossip check that it is the first of its slot and proposer covers the blocks that the node saw on gossip.
  For an envelope, a rival block that gossip ignored, and that the store does not hold, goes undetected.
- The source does not say how the node answers an object that gossip ignores; EthLib refuses it with 400, as the source ties a success to passing gossip validation.
  So an object that the node already holds, and saw on gossip, is refused.
  An error of the fork choice during the gossip checks refuses the object too.
- Some checks run only when the node integrates the object, so their failure gives 202, not 400.
  For a block, these include the verdict of the execution layer, the clock of the store, the availability of its data, its terminal block at the merge, and from Gloas the payload of a full parent; for an envelope, they include the data of its payload.
- The source says to integrate the block into the state; EthLib runs the block handler alone, so the votes and the slashings that the block carries do not decide its answer.
- The bodies of the endpoints may carry the blobs and the proofs of the object; EthLib reads them through the sources of the node, and leaves their broadcast out.
  The 400 for an envelope sent without its blob data, to a node that holds none, is out of scope too.
- The endpoints of attester slashings, proposer slashings, voluntary exits and bids take one object, and the others take a list.
  The source answers a failure of a single object with a plain error body; EthLib reports it at position 0.
  The source bounds the SSZ form of each list; EthLib does not enforce these bounds.
- The source asks validator clients to submit the preferences of proposers one epoch before Gloas; the topic exists only from Gloas, so EthLib accepts them only from Gloas.
- The debug state endpoint gives the state that a state identifier names, in the encoding of every other state answer, so it needs no answer of its own.

### Builder API

The Builder API connects a proposer to the builders that bid for its payload, as `ethereum/builder-specs` defines it.
EthLib cites commit `fce64468` of that repository.
For Bellatrix to Fulu, its specification text matches release `v0.6.1`; the changes are formatting, `deprecated` flags and notes that point to the Gloas replacements.
EthLib specifies the messages, their signatures, their SSZ encodings and the version names of their JSON bodies; it leaves out the transport.

A JSON response names the fork of its data by the consensus version of the Beacon API, from Bellatrix on.
`builderVersion?_isSome_iff` (`Consensus/Proofs/BuilderApi/Encoding.lean`) shows that a fork has such a version exactly from Bellatrix through Glamsterdam.
At Glamsterdam the version names the Gloas bodies, not the bid and the blinded block of the earlier forks.
`builderVersion?_names` shows that two forks with the same version give a bid the same top-level field names, and a blinded body too.
It does not compare the nested containers.
`isBuilderVersion_iff` shows that the Builder API names exactly the consensus versions from Bellatrix on.
`versionHeaderStatus_eq_none_iff` shows that the version header passes exactly when it is the exact name of such a version.
Any other header, or none, gets 400, as the Gloas builder document requires for every request with a body.
Before Gloas, only the SSZ body of a signed blinded block requires the header.
`versionHeaderStatus_builderVersion?` shows that the version of every fork from Bellatrix up to Hegotá passes.
The body of a registration request is a list of signed registrations, bounded by the registry limit of the preset.

From Bellatrix to Fulu, the proposer signs a blinded block, and the builder then reveals the payload.
`BlindedBeaconBlockBody.unblind_blind` and `BeaconBlockBody.blind_unblind` (`Consensus/Proofs/BuilderApi.lean`) show that unblinding with the payload undoes blinding, and the converse.
`BlindedBeaconBlockBody.unblind_eq_headerMismatch_iff` shows that unblinding fails exactly when the header of the payload differs from that of the blinded body, and `BlindedBeaconBlockBody.unblind_ne_header` that no other failure occurs.
`verifyBlockSignature_unblind` shows that the one signature of the proposer verifies on the full block exactly as on the blinded block, when the block names the proposer of the state.

From Bellatrix to Fulu, a builder keeps a registration only when five rules hold, in the order of the source.
`processRegistration_ok_iff` (`Consensus/Proofs/BuilderApi/Registration.lean`) states them on the inputs.
The key names a validator of the state; that validator is active or pending in the current epoch; the time is at most ten seconds ahead of the builder's clock; it is not earlier than the registration kept for the key; and the signature verifies.
The source adds the ten seconds to the clock as a 64-bit integer, which fails past `2^64 - 11`, so EthLib refuses such a clock too.
`processRegistration_signature` shows that a kept registration carries a valid signature, and `processRegistration_monotone` that keeping it does not move the time of its key back.
`processRegistration_exited` shows that a validator that has activated and exited by the current epoch is refused.
The source keeps only the message of each registration; EthLib keeps the signed registration, which holds that message.
The Relay API serves the signed registration of each upcoming proposer ([`responses.yaml`](https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/types/responses.yaml)), so a relay needs the signature too.
`Registry.find?_insert_self` shows that the registry gives back the signed registration just inserted for its key.
The pseudocode of the source has two defects, which EthLib reads by their evident meaning:

- `process_registration` reads `pubkey`, which it never binds; EthLib reads the key of the registration.
- It rebinds `registration` to the message, then passes it to the signature check, which takes the signed registration; EthLib checks the signed registration.

The endpoint takes a list of registrations.
The source does not say whether one invalid entry rejects the whole list, nor whether earlier entries of the same list count as kept registrations.
EthLib specifies one registration and leaves the list open.

From Bellatrix to Fulu, a builder serves a request for a bid only when four rules hold, and a proposer accepts a bid only when three rules hold.
`isEligibleForBid_ok_true_iff` (`Consensus/Proofs/BuilderApi/Bid.lean`) states the builder's rules: the slot is that of the state, the key has a kept registration, the key is that of the proposer of the slot, and the parent hash is the latest block hash of the state.
`isEligibleForBid_proposer` shows that a served request names the proposer, and `getHeaderStatus_wrong_slot` that a request for another slot gets 400.
The source gives 400 for an invalid request, 204 when the builder cannot produce a header, and 200 with the bid otherwise.
EthLib answers 500, the internal error of the source, when the proposer of the slot or its validator cannot be found; the source does not say which response that case gets.
`processBid_ok_iff` states the proposer's rules: the parent hash of the header is the latest block hash of the state, the fee recipient is the registered one, and the signature verifies.
`getBid_header` shows that the bid on a payload carries the header of that payload.
`processBid_getBid` shows that such a bid is accepted when the payload extends the state, pays the registered fee recipient, and the signature verifies.
The source gives the bid of a builder for Bellatrix only.
From Deneb the commitments to the blobs, and from Electra the requests, are inputs, since the source gives no function that fills them.
The pseudocode of the source has three defects, which EthLib reads by their evident meaning:

- `get_bid` takes `execution_payload` but reads `payload`; EthLib reads the argument.
- `verify_bid_signature` computes its signing root from `signed_registration.message`, a name it never binds; EthLib uses the message of the bid, as `get_bid_signature` does.
- `process_bid` calls `verify_bid_signature` without asserting its result, so read literally it accepts any signature; EthLib refuses a bid whose signature does not verify.

From Gloas, a builder checks a request for a bid with six rules, and a proposer checks a bid it fetched with eight rules and the signature.
`isEligibleForBidGloas_ok_true_iff` (`Consensus/Proofs/BuilderApi/GloasBid.lean`) states the builder's rules.
The slot is that of the state, and the key is that of the proposer of the slot, which is active.
That proposer sent preferences on gossip, the parent hash is that of the parent with or without its payload, and the parent root is the root of the latest header.
`isEligibleForBidGloas_proposer` shows that a served request names the active proposer.
The source asserts each rule, and EthLib answers false where an assertion fails.

`validateBid_ok_true_iff` states the proposer's rules, in the order of the source.
The builder is active, and the slot, the fee recipient, the parent hash, the parent root and the RANDAO mix match.
The gas limit moves toward the proposer's target, the builder can pay a bid of positive value, and the signature verifies.
The source asserts the eight rules and returns the signature check, so EthLib names the first failed rule as an error and returns the signature check as the result.
`validateBid_zero_value` shows that a bid of value zero is never refused for the funds of its builder.
`validateBid_not_selfBuild` shows that a bid naming the index of a self-built payload is never accepted, while the registry of builders is shorter than that index.
The cap that a proposer sets on the execution payment limits how much of it counts when a bid is valued; it is not a rule of validity.

From Gloas, a proposer authenticates a request for a bid, and a request that submits preferences, with a signed message.
`authFailures` and `preferencesFailures` (`Consensus/BuilderApi/RequestAuth.lean`) list every check of the authentication that fails, in the order header, data, slot, signature.
The source also refuses a malformed body and a request for a bid without its timing headers; those rules are outside these checks.
The version header must name the fork of the body's type, and these bodies exist from Gloas only, so EthLib requires `gloas` there, which is stricter than the version check of other bodies.
`authFailures_nil_iff` (`Consensus/Proofs/BuilderApi/RequestAuth.lean`) shows that a request for a bid fails no check exactly when the header is `gloas`, the data is not empty and equals the agreed data, the slot is that of the path, and the signature verifies.
`authFailures_signature_only` shows that a request for a bid whose only failed check is the signature fails with that check alone, and `allowedStatus_badSignature` that such a request gets 401 and no other status.
`preferencesFailures_of_passed` shows that preferences for a slot before the builder's current slot fail whenever the checks run, and `PreferencesStore.submit_of_passed` that such a submission leaves the store as it was.
`PreferencesStore.submit_of_accepted` and `PreferencesStore.get_keep` show that a submission that fails no check keeps its preferences under the key of the path and the slot of the request, and that no other entry changes.
`bidHonorsPreferences_keep` shows that a bid honors preferences kept for its proposer at its slot exactly when its execution payment is within their cap.
When no data was agreed out of band, `agreedData` takes the default data of the builder's URL, `defaultAuthData` (`Consensus/BuilderApi/AuthData.lean`).
The source takes the host with Python's `urlsplit` in its pseudocode, not by a standard, so EthLib states the grammar that it reads:

- The URL starts with a scheme by [RFC 3986 section 3.1](https://www.rfc-editor.org/rfc/rfc3986#section-3.1), a colon and two slashes; a URL without them has no host.
- The authority runs to the first `/`, `?` or `#`, and the userinfo ends at its last `@`, as in [RFC 3986 section 3.2](https://www.rfc-editor.org/rfc/rfc3986#section-3.2).
- A port is a colon and decimal digits, possibly none, by section 3.2.3.
- A host in brackets must be an IPv6 address in the text of [RFC 4291 section 2.2](https://www.rfc-editor.org/rfc/rfc4291#section-2.2).
  Its last two groups may be an IPv4 address in the dotted form of RFC 3986 section 3.2.2.
  An IPvFuture literal or a zone identifier is refused.
- Any other host must be non-empty, and hold only the unreserved characters and sub-delimiters of a registered name by RFC 3986 section 3.2.2, without percent-encoding.
  A character that is not ASCII is refused, and EthLib then lowercases the ASCII letters.
- The userinfo is dropped, and EthLib reads none of its characters.

The seven examples of the source agree with this grammar.
The source's `urlsplit` accepts some URLs that EthLib refuses, and for them it signs a host:

- a URL with leading spaces or control characters, or a tab, CR or LF up to the end of its host, which it removes;
- a host with other ASCII characters outside a registered name, such as a space, `"`, `\` or `{`, which it keeps;
- a host with a percent sign, whose text after the sign it does not lowercase;
- a port that is not decimal digits, which it ignores;
- a host whose Unicode lowercase is ASCII, such as one with the Kelvin sign U+212A;
- an IPvFuture literal, which it signs without brackets;
- a URL without a scheme that starts with two slashes.

EthLib refuses them, so that a proposer and a builder never sign different bytes without an error.
For a zone identifier in brackets, `urlsplit` gives the host, but the source does not say how to compress it, and EthLib refuses it.
In the other direction, recent versions of `urlsplit` raise an error on brackets in the userinfo, or on userinfo whose NFKC form holds `/`, `?`, `#`, `@` or `:`, while EthLib drops that userinfo and signs the host.
The default data has no bound of its own, but a request carries at most 4096 bytes of data, so a longer host can never authenticate.
`parseIpv6_compressIpv6` (`Consensus/Proofs/BuilderApi/AuthData.lean`) shows that the compressed text of an address reads back as that address.
`defaultAuthData_eq_iff_of_ipv6` shows that two URLs whose hosts are IPv6 literals give the same data exactly when they name the same address, so every spelling that EthLib reads as an address signs the same bytes.
`urlHost_eq_of_defaultAuthData_eq` shows that two URLs that give the same data have the same host.
`defaultAuthData_nonempty` and `defaultAuthData_ascii` show that the default data is never empty, so it never fails the rule against empty data, and that each of its bytes is ASCII.
The source leaves two points open:

- When a request fails a check that gives 400 and the signature, which gives 401, the source does not say which status wins; `AllowedStatus` allows both.
  When no check of the authentication fails, the other rules of the source decide the status.
- A slot that "has already passed" is defined no more precisely; EthLib reads it as a slot before the builder's current slot.

The signature covers the data and the slot, not the preferences of the request; `preferencesFailures_preferences` shows that a request with the same authentication and another cap passes the same checks.
So a replay before its slot passes, or a copy with another cap, is accepted and replaces the kept preferences, although the source means the slot rule to stop a replay from rolling them back.

From Deneb to Fulu, a builder reveals the payload with a blobs bundle: the blobs, their commitments and their proofs.
`BuilderBlobsBundle.names_nodup` and `ExecutionPayloadAndBlobsBundle.names_nodup` (`Consensus/Proofs/Containers/BuilderApi.lean`) give both containers distinct field names, so they decode back from their bytes when the logs bloom has a byte.
The response is the payload alone before Deneb and the payload with its bundle from Deneb, one type that the fork chooses.
`RevealedPayload.deserialize_of_deneb` and `RevealedPayload.deserialize_of_not_deneb` (`Consensus/Proofs/Containers/BuilderApi.lean`) show that its bytes decode as the form of the fork.
`RevealedPayload.executionPayload_ofBundle` and `RevealedPayload.executionPayload_ofPayload` show that the payload taken from a decoded form is the payload of that form.
From Fulu the Fulu builder document bounds the proofs by `FIELD_ELEMENTS_PER_EXT_BLOB * MAX_BLOB_COMMITMENTS_PER_BLOCK`, 2^25 in the mainnet preset.
A bundle holds at most `MAX_BLOB_COMMITMENTS_PER_BLOCK` blobs, so it needs at most `CELLS_PER_EXT_BLOB * MAX_BLOB_COMMITMENTS_PER_BLOCK` cell proofs, 2^19, and the bound is 64 times larger.
EthLib keeps the bound as written: it admits bundles with more proofs than any blob needs, and it sets the depth of the Merkle tree of the proofs.
Whether the builder specification intends this bound is an open point.

### Relay API

The Relay API, as `flashbots/relay-specs` defines it, lets a builder submit blocks to a relay, and lets anyone read the relay's data.
The source has no tag and no release, so EthLib cites commit `a4e0a50d`, its Fulu update; it has no Gloas part.

From Bellatrix to Fulu, a builder submits a block as a bid trace, the payload, from Deneb the blobs bundle, from Electra the requests, and its signature.
The source restates the payload, the withdrawals, the requests, the blobs bundle and their bounds; EthLib uses its own containers for them.
`SubmitBlockRequest.names_nodup` (`Consensus/Proofs/Containers/RelayApi.lean`) gives a submission distinct field names at every fork, so it decodes back from its bytes when the logs bloom has a byte.
`BidTrace.serialize_size` (same file) shows that every bid trace serializes to 236 bytes.
The Python suite computes the roots of the restated containers from the documents of the source, and compares them with EthLib's.
They agree, except for the requests, where the source has a defect:

- The Electra document of the source bounds the consolidation requests of a payload by 1, where the mainnet preset of the consensus layer bounds them by 2.
  The bound sets the depth of the tree of the list, so a relay that follows the document gives the requests, and the submission, another root than EthLib.
  Such a relay also refuses a payload with two consolidation requests, which the consensus layer accepts.
  EthLib keeps the bound of the preset, so the requests of a submission are those of the payload.

The source leaves two points about the containers open:

- It defines a container whose one field, named after the fork, holds the submission, but it does not say where it is used.
  Its Fulu note says that the new field replaces "the `bellatrix` field", where it replaces the Electra one.
  EthLib defines the container, with the field named after the consensus version of the fork.
- The JSON examples of its submissions are not complete vectors.
  Their bid traces lack `proposer_pubkey`, so EthLib refuses them.
  The source says that missing fields default to zero when a container is instantiated.
  EthLib reads that as a rule of the source's Python notation, not of its JSON, so its reader requires every field.
  The blobs of the Deneb and Electra examples hold 32 bytes instead of 131,072, so EthLib refuses those bundles too.

The source says that a new submission by a builder replaces the previous one by the same key, "even if it is less profitable".
The rule names no slot, so EthLib keeps the submissions of one slot in a store, which ignores a submission for another slot.
`SubmissionStore.submit_overwrites` (`Consensus/Proofs/RelayApi.lean`) shows that after a submission for its slot the entry of its builder is that submission, whatever the value of the entry before.
`SubmissionStore.submit_other` shows that the entries of other builders do not change, and `SubmissionStore.submit_other_slot` that a submission for another slot changes nothing.

From Bellatrix to Fulu, a relay serves a submission to proposers as a bid of the Builder API.
`SubmitBlockRequest.bid_total` shows that the bid always computes, and `SubmitBlockRequest.bid_header` that it holds the header of the payload.
`SubmitBlockRequest.bid_value_pubkey` shows that it holds the value of the bid trace and the key it is served under.
`SubmitBlockRequest.bid_commitments` shows that from Deneb it holds the commitments of the blobs bundle, as the [Deneb bidding rules](https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/deneb/builder.md#bidding) require.
`SubmitBlockRequest.bid_requests` shows that from Electra it holds the requests of the submission.
`SubmitBlockRequest.bid_unblind` shows that a blinded body that carries the header of the bid unblinds to a body that holds the payload of the submission.
The source does not fix the key that signs the served bid, so it is an input.
From Deneb, the [block scoring rules](https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/deneb/builder.md#block-scoring-1) forbid a relay to serve a submission whose value fails the check of the bid value.
That check needs the balance change of the fee recipient from a simulation of the payload.
It also subtracts withdrawal amounts in Gwei from that change in Wei, with no conversion, so EthLib does not yet say which submissions a relay may serve.

The source leaves four points about a submission open, and EthLib specifies none of them:

- The signature check of a submission: the source says only that the "builder signature is over the SSZ encoded `message`", and names no domain.
- What a submission with `cancellations=1` changes, beyond "opt into bid cancellations".
- The order of submissions that reach the relay at the same time.
- The simulation of the payload, which the relay runs "to verify properties and proposer payment".
  So EthLib does not check that the bid trace agrees with the payload, and the served bid takes the value of the bid trace as it is.

A relay lists for builders the validators "scheduled to propose in the current and next epoch", each with its slot, its index and its signed registration ([`validators.yaml`](https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/apis/relay/builder/validators.yaml)).
"Slots without a registered validator are omitted."
`ValidatorsResponse.Sound` (`Consensus/RelayApi.lean`) states this for any schedule of proposers: every entry lies in the two epochs and names the proposer of its slot with the registration kept for its key, and every slot of the two epochs whose proposer has a registration has exactly one entry.

`scheduledEntries_sound` (`Consensus/Proofs/RelayApi.lean`) shows that the entries built from a schedule satisfy it, for any schedule.
The source does not say how a relay learns the schedule.
From Fulu, the state holds the proposers of the current and next epoch in its lookahead ([EIP-7917](https://eips.ethereum.org/EIPS/eip-7917#specification)), so EthLib builds the list from it.
`validatorsResponse_sound` shows that this list satisfies the rule with the lookahead as the schedule.
`validatorsResponse_proposer` shows that each entry after the slot of the state names the proposer that the state reaches at that slot, when the slots of the transition succeed.
`validatorsResponse_proposer_self` shows that an entry for the slot of the state names the proposer of the state.
The entries for earlier slots of the current epoch are tied to the consensus layer only through the lookahead, by `validatorsResponse_sound`.
Before Fulu, the state does not hold the proposers of the next epoch.
They can change with the balances until that epoch starts, so the agreement with the consensus schedule is proved from Fulu only.
The export gives the list at Fulu only, because the relay source has no part after Fulu.

The data API lists the payloads that a relay delivered to proposers and the bids from builders that it received and verified ([`proposer_payload_delivered.yaml`](https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/apis/relay/data/proposer_payload_delivered.yaml), [`builder_blocks_received.yaml`](https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/apis/relay/data/builder_blocks_received.yaml)).
A delivered payload is a bid trace with `block_number` and `num_tx`, and a received bid adds `timestamp` and `timestamp_ms` ([`bids.yaml`](https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/types/bids.yaml)).
`BidTraceV2.ofApiJson_toApiJson` (`Consensus/Proofs/RelayApi.lean`) shows that the JSON of a delivered payload reads back as that payload.
`BidTraceV2WithTimestamp.ofJson_toJson` shows the same for a received bid.
`BidTraceV2WithTimestamp.toJson_total` shows that the writer of a received bid never fails.
The source gives each timestamp the type `Int64`, a string ([`misc.yaml`](https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/types/misc.yaml)), and EthLib writes it in decimal, as the source's example does.
`BidTraceV2WithTimestamp.int64Json_of_readInt64` shows that a timestamp is read only from the string that the writer gives for it.
So a plus sign, a leading zero and `-0` are refused.

A query keeps an entry when each filter that it gives equals the field of the entry.
The source of delivered payloads says so ("Query arguments are used as filters"), and EthLib reads the query of received bids the same way.
`DeliveredFilter.keeps_empty` and `ReceivedFilter.keeps_empty` show that a query with no filter keeps every entry.
`DeliveredFilter.keeps_slot` and `ReceivedFilter.keeps_slot` show that a query whose only filter is a slot keeps exactly the entries of that slot.
A query may sort delivered payloads by value, lowest or highest first ([`misc.yaml`](https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/types/misc.yaml)).
`sortBy_descending` shows that a sort by `-value` gives the payloads with values that never increase, and keeps every payload.
`sortBy_ascending` shows the same for `value`, with values that never decrease.
`sortBy_stable` shows that, in either order, payloads of equal value keep their input order.

The source leaves three points about the data API open, and EthLib specifies none of them:

- What `cursor` means, beyond "A starting slot for multiple results", and in which direction it reads.
  EthLib models neither the cursor nor the limit of a query.
- The order of the results without `order_by`, and the order of payloads of equal value with it.
  EthLib's sort keeps payloads of equal value in their input order, as stated above.
- Which field of a payload `block_number` and `num_tx` come from.
  Their names suggest the number of the block and the count of its transactions, but the source does not say so.
  So they are fields of the entry, not values computed from the payload.

### What cannot be proved yet

Some definitions cannot be unfolded by the kernel, so the kernel cannot evaluate them, and their intended computational properties remain unproved.
They come in three kinds.
A `partial` definition is defined by `partial` recursion.
An `opaque` one is an opaque constant.
A `reaches-opaque` one unfolds to an opaque constant, such as `Loop.forIn`, which `while` compiles to.

`lake exe check-decls` reports each one, and `scripts/check_decls_baseline.txt` lists those that remain, with the reason for each group.
The list below is generated from that file, and it is empty when none remains.

<!-- generated: unfoldable -->
<!-- end generated -->

## Gap A: does the definition say what the source and the client need?

### A1. A wrong definition

A definition can differ from its source while every theorem about it holds, because the theorems are proved about the definition, not about the source.
Three things guard against that.
Each definition is named and shaped after its source, so that a reader can compare them line by line.
The KZG and BLS vectors in `tests/cryptography/` match consensus-specs `v1.7.0-alpha.12` and `ethereum/bls12-381-tests` `v0.1.2` byte for byte, and EthLib produced none of them.
Finally, the consistency theorems on the constants, listed under BLS12-381, catch a wrong digit.

Two definitions also do what their sources do not.
The PeerDAS custody search fails after `2^16` node IDs in the export, where its source loops on, and no theorem bounds the steps it needs.
BLS key generation fails after 16 attempts, a bound that EthLib chose.
[The IRTF BLS draft, version 4, §2.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-2.3) and `HKDF_mod_r` of [ERC-2333](https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#hkdf_mod_r) loop until the key is not zero.
The ERC-2333 master and child derivations reuse key generation, so they share the bound.
An attempt fails only when its 48-byte output is a multiple of `r`.

A run of slots of the consensus state transition divides by constants of the preset and of the configuration, such as the slots of an epoch, the increment of an effective balance and the quotient of the churn limit.
Python's integer division and remainder raise an error on a zero divisor, so the specification fails there.
In Lean a division of 64-bit integers by zero returns zero and a remainder returns the dividend, so with such constants a step can succeed in EthLib where the specification fails.
`Preset.DivisorsPositive` and `Config.DivisorsPositive` (`Proofs/Transition/Totality/Bound.lean`) name the presets and configurations whose divisors in a run of slots are positive, and the mainnet and minimal ones are proved to be such.
Block processing divides by further constants, such as the quotients of the slashing penalty and of the whistleblower reward, which these predicates do not list.
A theorem that a step succeeds takes a predicate only where its proof needs a positive divisor.
For a preset or configuration with a zero divisor, any theorem about a step that divides by it describes EthLib's transition, not the specification's.

The accessor that lists the active validators keeps a result where the specification fails.
The specification lists the active validators of an epoch by their indices, and builds each index as a `ValidatorIndex`, a 64-bit integer.
That construction rejects a value of `2^64` or more, so the specification fails when a validator at a registry position of `2^64` or more is active.
`getActiveValidatorIndices` returns a plain list and never fails; at such a position it would take the position modulo `2^64`.
Before Gloas the type of the registry bounds it by the limit of the preset, a 64-bit integer (`2^40` in the mainnet and minimal presets), so no position reaches `2^64`.
From Gloas the type of the registry has no length limit ([EIP-7688](https://eips.ethereum.org/EIPS/eip-7688#converted-types)).
A new validator still gets the size of the registry as its index, and that index must be below `2^64` (`getIndexForNewValidator_ok_iff`).
So a transition never adds a validator at a position of `2^64` or more, and only a starting state built outside the transition can hold one.

`getActiveValidatorIndicesChecked_eq_ok_iff` in `Consensus/Proofs/Accessors.lean` states the divergence exactly.
The checked read converts each active position as the specification does, and it gives EthLib's list exactly when every active position is below `2^64`.
The specification also converts the number of active validators to a 64-bit integer, and rejects a count of `2^64`, which a registry of `2^64` positions allows.
Such a registry can arise through the transition from Gloas, at least in principle.

The transition reads the active validators through `getActiveValidatorIndicesChecked`, which fails at an active position of `2^64` or more, as the specification does.
The shuffle of the beacon committees and the committee count of an attestation also fail at `2^64` active validators, so the transition agrees with the specification on the count of committees.
The churn limit of validators before Electra and the Phase 0 weak subjectivity period still convert the count of the pure list without a check.
Both run only before Electra, where the type of the registry keeps it within the limit of the preset (`BeaconState.registryWithinLimit_of_lt`).
There the count is below `2^64` (`length_getActiveValidatorIndices_lt`), so the conversion keeps its value (`toNat_length_getActiveValidatorIndices`) and agrees with the specification.
The genesis validity check, fork choice, gossip and the honest-validator duties call the pure list directly, and keep the difference.

Some official vectors expect more than a source says.
The transaction tests of ethereum/tests reject 43 results whose gas limit is `2^64`, or whose gas limit times gas price exceeds `2^256 - 1`.
No rule of the Yellow Paper rejects such a transaction alone, and EIP-7825 caps the gas limit only from Fusaka on.
EthLib accepts them, and the suite asserts that it does, as `tests/execution/ethereum_tests/README.md` explains.

### A2. Hypotheses inside theorems

A conditional theorem is only as strong as its hypotheses.
The ceremony theorem `checksSufficient_of_subgroupChecks` is one, and its hypotheses are listed under KZG.
Only the lemmas in `Proofs/Bls/PairingLaws.lean` and `Proofs/AltBn128/PairingLaws.lean` take `PairingLaws` as a hypothesis.
The BLS signature, consensus, KZG, PeerDAS, EIP-2537 and EIP-197 theorems need no such hypothesis.
`PairingLaws` is a `Prop`, never an axiom, so `lake exe check-decls` still sees only the standard axioms.
`pairingLaws` proves the law for BLS12-381, and `AltBn128.pairingLaws` proves it for alt_bn128.

The theorems in `Proofs/Transition/Totality/` show that the steps of a run of slots succeed, and each takes hypotheses that the specification does not state.
Each hypothesis narrows the states, presets or runs that the result covers.
Justification and finalization need two slots an epoch and a buffer of block roots that reaches the epoch before (`Preset.RootsReachPreviousEpoch`).
With one slot an epoch the specification itself can fail there.
Before Altair they also assume that the committees of the pending attestations can be computed (`PendingResolved`), which a block checked when it included them.
From Altair the rewards and penalties need `RewardsFit`, a set of bounds on the preset, the configuration, a budget of Gwei and a bound on the inactivity scores that the step reads.
They also need each effective balance at most the largest cap, the finalized epoch at most the previous epoch, and each balance and the sum of the effective balances within the budget.
The inactivity penalty multiplies an effective balance by an inactivity score, and a score grows by at most the score bias in each epoch.
So the bound on the scores limits the length of the run that the theorems cover.
On mainnet the bounds hold for a budget of `2^57` Gwei, about `1.44 * 10^8` ETH, and scores up to `2^23`.
From a score of zero, a score reaches `2^23` only after `2^21` epochs of missed targets, about 25 years at 32 slots of 12 seconds an epoch.
The specification itself overflows there: at 2048 ETH the product fails once a score passes about `9.0 * 10^6`.
The bound on the reward of a flag does not use the square root of the total active balance.
The validators that set a flag in the previous epoch include those whose exit epoch is the current epoch.
So their effective balance can exceed the total active balance of the current epoch, and only the budget bounds it.
The budget of `2^57` Gwei is about 84% of the largest that this bound allows.
Before Altair the rewards and penalties need `RewardsFitBeforeAltair`, a set of bounds on the preset, a budget of Gwei and a bound on the current epoch.
They read the root of the block at the slot of each vote that matches the target.
So they assume that each recent pending attestation is as inclusion in a block stored it (`PendingWellFormed`).
Its slot is then in the epoch of its list, its inclusion delay is not zero, and its proposer is a validator of the registry.
No theorem yet shows that this holds along a run: the preservation must be stated over the slot advance and block processing, and the nonzero delay needs a least inclusion delay of one slot, as mainnet and minimal have.
The inactivity penalty before Altair multiplies an effective balance by the delay of finality, which is at most the current epoch.
So the bound on the current epoch limits the length of the run that the theorem covers.
A proposer can earn a share of the base reward of each signer that it included.
So the bound on its reward is the bound on base rewards at the whole budget, as the effective balances of its signers sum to at most that.
On mainnet and minimal these bounds hold for a budget of `2^57` Gwei and `2^21` epochs.
The bound on the current epoch multiplies it by the largest cap at any fork, 2048 ETH, so it is conservative before Altair, where the cap is 32 ETH.

Before Electra, registry updates need a ceiling for the first activation epoch and every exit epoch other than `FAR_FUTURE_EPOCH`.
The ceiling plus the registry size and the withdrawability delay must be below `2^64`.
Each ejection raises the ceiling by at most one, and activation leaves the exit epochs unchanged.

From Electra, pending consolidations succeed when their source and target indices are in the registry, balances match the registry, and the sum of balances is below `2^64`.
The current epoch plus one must fit in 64 bits.
The source is debited before the target is credited, so the budget also covers equal source and target indices.

From Altair, the sync committee update succeeds (`processSyncCommitteeUpdates_ok`) under the assumptions of `SyncDrawable`, asked only when the next epoch starts a period.
One validator active in the next epoch must have the largest effective balance of the draw (`drawCap`), and no validator may have more.
Before Electra that balance is 32 ETH, and from Electra it is the cap of a compounding validator, 2048 ETH.
This is an assumption on the registry, not a bound that an epoch keeps: such a validator may never join, or may exit.
The draw accepts such a validator on every pass over the candidates, so the committee fills within as many passes as members; `balanceWeightedSearch_ok` proves it.
Without such a validator, whether the draw ends before its counter reaches `2^64` depends on the hashes, and the theorem says nothing.
Before Electra, every effective balance must be at most 32 ETH, which the bound of 2048 ETH in the other totality theorems does not imply.
Every key of the registry must also pass key validation, as each deposit checks before a validator joins; no theorem yet proves that along a chain.
The registry holds at most `2^40` validators, and the committee size times the registry size stays below `2^64`.
The next epoch plus the length of the history of mixes must fit in 64 bits, and the seed lookahead must be shorter than that history.
The products of the draw must fit in 64 bits (`DrawFits`), and the preset must give a sync committee of at least one member.
The keys of an empty committee have no aggregate, so with no member the update would fail at every period.
`drawFits_presets`, `seedLookahead_lt_presets` and `syncCommitteeSize_ne_zero_presets` prove the three facts on the preset for mainnet and minimal.

From Gloas, builder payment settlement succeeds when an epoch has at least six slots.
The registry must also be within its limit, and the sum of effective balances below `2^64`.
Mainnet and minimal have 32 and 8 slots an epoch.
With fewer than six, the specification itself can overflow when it multiplies the balance of one slot by six.
The step changes only the pending payments and the withdrawals of the builders, so it keeps the bounds on the amounts of a run of slots (`WithinBudget`).

The builder payments of Gloas carry four hypotheses and one restriction.
`chainSteps_paysQuorum` proves that along a chain through the last slot of an epoch, each payment of the previous epoch that reaches its quorum is paid exactly once.
Paid means that the withdrawal of the payment joins the queue of the withdrawals of the builders.
The last slot of the epoch queues the withdrawals of exactly those payments.
A run of slots and blocks over the whole chain (`PaymentChain`) releases each of them, and releases no payment twice.
The withdrawals of such a run are fixed by the states that each step computes.
Its payments are fixed too, up to their order: a slot lists only payments that reach the quorum, and a block only the payment of its parent.
`paymentChain_of_chainSteps` proves that every chain inside one fork is such a run, and `PaymentChain.nodup` gives "at most once" for any such run.
The facts on the payments must hold at the first state, as `paymentFacts_upgradeToGloas` proves for the upgrade to Gloas.
These theorems also take a positive payment quorum (`PaymentQuorumPositive`), at least two slots in an epoch, and at most 2^40 entries in each registry at the last state.
`paymentQuorumPositive_presets` and `twoSlotsPerEpoch_presets` prove the first two for the mainnet and minimal presets.
For the validators, 2^40 is `VALIDATOR_REGISTRY_LIMIT`.
The registry of the builders has no limit in the specification, so for it the bound is an assumption, which matches `BUILDER_INDEX_FLAG`.
No theorem proves either bound along a chain.
The chain must stay inside one fork, from Gloas on, so a chain across the upgrade to Heze is not covered.
A run of payment steps relates two states of one fork, and carrying open payments through that upgrade needs a run across forks.
The four facts that the runs assume do hold through that upgrade, by `PaymentFacts.upgradeToHeze`.
The "at least once" half is stated for a chain split at the epoch step, which fixes the step that pays.
The quorum is read on the state that the epoch transition reaches before its step of the payments.
A bid whose payment a slashing cancels may still be paid by the late path of the bid, and then the run releases it once.

Whatever those hypotheses leave unproved is part of what a reader trusts.

### A3. Side channels

EthLib makes no constant-time claim.
`Hash/Keccak.lean` says it "is not intended to be constant-time", and the field arithmetic uses Lean's `Nat`, which gives no timing guarantee.
This matters where secret data is handled.

XMSS and leanSPHINCS `keyGen` and `sign` handle secret data.
The Python bindings expose all four, as `key_gen` and `sign` in each module, which take the secret seed.
BLS key generation, signing and the proof of possession handle secret data, and the Python bindings expose all three.
The bindings `derive_master_sk`, `derive_child_sk` and `derive_path` handle secret seeds or keys.
HMAC-SHA-256, HKDF and the Concatenation KDF take a secret key, input keying material or shared secret.
The Python bindings expose them as `hmac_sha256`, `hkdf_extract`, `hkdf` and `concat_kdf`.
HKDF-Expand-Label and the QUIC packet keys take a secret, and the bindings expose them as `tls13_expand_label` and `packet_keys`.
PBKDF2 and scrypt take a secret password, and the bindings expose them as `pbkdf2` and `scrypt`.
The steps of scrypt take values derived from the password, and the bindings expose them as `salsa208`, `scrypt_block_mix` and `scrypt_romix`.

ROMix, the memory-hard step of scrypt, reads its table at indices that depend on the password, as AES reads its S-box below.
Its memory use depends on its parameters, and D1 says what a caller must bound.

Every AES function that takes a key handles secret data.
Its S-box is a table, and the cipher reads it at indices that depend on the key.
The Python bindings expose the block cipher, CTR and GCM, as `encrypt_block`, `decrypt_block`, `ctr`, `gcm_encrypt` and `gcm_decrypt`.

### A4. Idealisations

A security theorem rests on a model, such as a random oracle for a hash.
Each such theorem of EthLib rests on the idealisations listed below, and on any hypothesis that its statement names.
The two theorems of Casper FFG share one bullet, as do the signature theorems of the light client.
The binding of a proof of possession shares the bullet of leanXMSS, and the codeword searches of each scheme share the bullet of that scheme:

- leanXMSS: the hash `H`, Keccak-256, is a random oracle on byte strings.
  The theorem says nothing about an attack that uses the structure of Keccak.
  The binding of an EIP-8450 proof of possession rests on the same oracle.
  So do the failure bounds of the codeword searches of leanXMSS.
- leanSPHINCS: the hash `H`, Keccak-256, is a random oracle on byte strings, as for leanXMSS.
  The unforgeability theorem says nothing about an attack that uses the structure of Keccak.
  It counts classical queries only, so it says nothing about a quantum adversary.
  The failure bounds of the codeword searches of leanSPHINCS rest on the same oracle.
- Merkle search bounds: each new `(level, position, left, right)` input receives an independent uniform answer from a finite nonempty range.
  Repeated inputs receive the same answer, and the initial cache is empty.
  The fixed-target bound excludes one honest input from the oracle domain and fixes the target before the run.
  Reading it as a second-preimage bound conditions on the honest digest, a modelling step that no theorem proves.
  Only classical queries are counted.
  No SHA-256, Keccak or quantum security claim follows from this model.
- SSZ root bound: the SHA-256 node hash is a random oracle on byte strings, shared by every node of the tree.
  The roots of the all-zero subtrees, constants of the specification, are oracle answers in the model.
  The type is fixed before the run, except in the layout bound, where the adversary picks both types.
  The branch bound fixes the depth before the run, and its adversary picks the index, the leaves and the branches.
  The blob sidecar bound fixes the preset and the fork before the run, and its adversary picks both sidecars.
  Each new input receives 32 independent uniform bytes, repeated inputs receive the same answer, and the initial cache is empty.
  Only classical queries are counted, and the adversary's private sampling is not.
  The bound says nothing about an attack that uses the structure of SHA-256.
  The bound on signing roots runs the same experiment, so it rests on the same oracle.
- Trie root bound: Keccak-256 is a random oracle on byte strings, shared by the keys and the nodes of the trie.
  Each new input receives 32 independent uniform bytes, repeated inputs receive the same answer, and the initial cache is empty.
  Only classical queries are counted, and the adversary's private sampling is not.
  The bound says nothing about an attack that uses the structure of Keccak.
- VRF unpredictability: Keccak-256 is a random oracle on byte strings, as for leanXMSS.
  The bound says nothing about an attack that uses the structure of Keccak.
  It counts classical queries only, so it says nothing about a quantum adversary.
- VRF mixed selection: Keccak-256 on the 74-byte inputs that start with `PQ_VRF_MIX` is a uniformly random function of the output and the randomness, independent of the tree hash.
  That is the random-oracle assumption for the domain of the mix, and the tree hash stays Keccak-256 itself.
  The holder can still compute Keccak-256 on mix inputs, and the model ignores those values.
  No other input of the VRF has 74 bytes, so the mix shares no input with the tree; that is necessary for the assumption, not a proof of it.
  The randomness is uniform, drawn after the holder registers its tree, and independent of the holder.
  The bound counts classical mix queries only, and says nothing about an attack that uses the structure of Keccak.
- BLS: the hash to G2 under the message tag is a random oracle onto the multiples of `g2`, and the hash under the key tag of the proof-of-possession scheme is an independent random oracle onto the same group.
  The two tags differ, as §3.3.1 of the BLS draft requires.
  [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380), §3, calls its `hash_to_curve` suitable where a random oracle onto the group is needed, and §8.8.2 gives the suite that encoding.
  Nothing in EthLib proves that the hash behaves as such an oracle.
- Light client: an aggregate signature check accepts a message only if every key in its set signed it (`SignatureChecks.AggregateSound`).
  BLS signatures with proofs of possession are meant to give this, except with small probability, and EthLib proves only the bound below.
  `Pop.byteForgeAdvantage_le_coCdhAdvantage` bounds the forger of such aggregates on EthLib's bytes, with both hashes as random oracles.
  That is the draft's scheme, whose proofs of possession hash the key under the key tag.
  Ethereum registers keys with deposit signatures under the message tag instead, which that game does not model.
  `LightClientForgery.forgeAdvantage_le` bounds the probability that the light client accepts a forged signature of one designated honest member, when every signer carries a proof of possession that passes PopVerify, §3.3.3.
  The theorems on one accepted update say nothing about a forged aggregate signature; the bound gives its probability.
- ECDSA: the bijection in the middle of the conversion `x_R mod n` is a uniform permutation, which the adversary evaluates in both directions.
  In ECDSA that bijection is the identity on integers below `2^256`, so the model idealises the conversion, as §4 of [Fersch, Kiltz and Poettering](https://doi.org/10.1145/2976749.2978413) does.
  The model draws the deterministic nonces of RFC 6979 as a random function of the message, so each message has one signature.
  [RFC 6979 §3.2](https://www.rfc-editor.org/rfc/rfc6979#section-3.2) computes them with HMAC_DRBG, whose seed holds the private key; the model assumes that output is pseudorandom, and no theorem proves it.
  The hash of messages is a fixed public function, so a bound on this game must charge its collisions to a named reduction.
  `Proofs/Secp256k1/Security/Game.lean` states that game; `forgeAdvantage_le` (`Proofs/Secp256k1/Security/ChosenMessageBound.lean`) bounds its advantage by named reductions.
- Casper FFG: a vote names its signer, so no one can forge a vote.
  The theorems of accountable safety and plausible liveness say nothing about an attack on the signatures.
- KZG batch checks: the challenge hash `Fr.hashToBlsField` is a random oracle from the inputs of the batch onto `Fr`.
  That hash reduces a SHA-256 digest modulo `r`, so it is not exactly uniform even if SHA-256 is a random oracle.
  Then each value has probability at most `3 / 2^256`, which is below `1.36 / r`, and the bounds grow by that factor.
  The real hash reads an encoding of those inputs.
  The encoding is injective on the batches that the checks accept: their arrays have matching lengths, and each cell has 64 values.
  In `prEvent_batchErrorPoly_root_le`, `prEvent_cellErrorPoly_root_le`, `prEvent_cellInput_root_le` and `prEvent_blobInput_root_le`, the adversary queries that oracle at most `q` times.
  In `prEvent_blobInput_root_le`, the evaluation challenges `computeChallenge` are a fixed function of the blobs and commitments, not part of the oracle.
  Their hash input starts with a different 16-byte domain tag from that of the batch challenge, so the two hashes never read the same bytes.
  So the bound `(q + 1) (n - 1) / r` covers grinding, where the adversary hashes many batches and keeps one whose challenge is a root.
  `blobBindingAdvantage_le` instead models both individual and batch challenges with one shared cache and uniform answers in `Fr`.
  Its typed keys erase polynomial annotations and stand for the two domain-separated byte encodings; no theorem proves those encodings jointly injective.
  That theorem also assumes correct representations from the adversary, a reading of the algebraic group model.
  The theorems say nothing about an attack that uses the structure of SHA-256.

## Gap B: does the code that runs match the definitions?

s2n-bignum proves its theorems about the object code, so a compiler bug cannot invalidate them.
EthLib is the other way round.
Its theorems are about the Lean definitions, and everything between them and the running code is trusted.
The sketch shows where each gap sits.

```text
 source document --A-- Lean definition == proof == theorem
                            |
                            B
                            |
        compiled code, C boundary, wheel --D-- client

 C: is the proof itself sound?
```

### B1. The compilers and the runtime

The Lean compiler turns the definitions into C, a C compiler turns that into machine code, and the Lean runtime runs it.
No theorem covers that path.

The vectors can test it end to end, but only through a comparison.
The Python suite regenerates every vector through the bindings and writes it over the committed one.
For most operations it does not compare the result with an expected answer, so a passing run proves nothing on its own.
The check is that the regenerated files are identical to the committed ones, which match consensus-specs `v1.7.0-alpha.12`.
`uv run --no-project --python 3.12 python tests/cryptography/check_vectors.py` makes that comparison against the pinned digests.

On every change, CI regenerates the vectors through the bindings.
It fails when a file under `tests/cryptography` then differs from the committed one.
That run skips the key generation and signing cases of leanXMSS and leanSPHINCS, which take minutes each.
Every Monday, the `vectors-slow` workflow regenerates all cases, these included.
It fails when a test file then differs from the committed one, or when a pinned digest does not match.
So between two weekly runs, a change can alter the compiled key generation or signing of those two schemes unnoticed.

### B2. Lean core's own implementations

Lean core implements `Array.forIn'`, `foldlM`, `foldrM`, `mapM` and `anyM` with `@[implemented_by]`, and the `Nat`, `ByteArray` and `Array` primitives with `@[extern]`.
The compiled code runs those implementations, not the definitions the kernel checks.
Any loop or fold over an array reaches them, so Lean core is a declared trusted baseline, and `lake exe check-decls` does not report it.

### B3. Native code during elaboration

The `EthLib` and `Exports` libraries set `precompileModules := true`.
So `#eval`, or a tactic that evaluates, in any module that imports them runs natively compiled code.
A proof is unaffected unless it uses one of the tactics of C2.

### B4. The C boundary

Between the Lean exports and Python sits a layer of hand-written C.

<!-- generated: exports -->
Lean exports 521 operations and 49 size constants.
The Python extension calls 521 of the operations and 49 of the constants.
<!-- end generated -->

<!-- generated: c-lines -->
11844 lines of hand-written C sit between them and Python: `aes.c` (119), `blocks.c` (364), `bls.c` (426), `chacha20_poly1305.c` (75), `chain.c` (45), `consensus.c` (2652), `crc32.c` (34), `crc32c.c` (34), `deposit_tree.c` (84), `devp2p.c` (79), `discv4.c` (78), `discv5.c` (303), `engine.c` (207), `enr.c` (177), `era.c` (12), `era1.c` (12), `eth.c` (263), `ethash.c` (65), `evm.c` (109), `fees.c` (56), `forkid.c` (101), `gossip.c` (158), `hmac.c` (122), `keccak.c` (85), `keystore.c` (30), `kzg.c` (511), `libp2p.c` (187), `module.c` (1644), `noise.c` (111), `password_kdf.c` (105), `pow.c` (73), `precompile.c` (85), `pyvalue.c` (421), `quic.c` (221), `reqresp.c` (130), `rlp.c` (156), `rlpx.c` (184), `rpc.c` (84), `secp256k1.c` (169), `secp256r1.c` (42), `sha256.c` (38), `snap.c` (159), `snappy.c` (146), `sphincs.c` (85), `ssz.c` (86), `state.c` (108), `transactions.c` (181), `trie.c` (115), `vrf.c` (141), `wrappers.h` (817), `x25519.c` (21), `xmss.c` (134).
<!-- end generated -->

That C converts arguments, owns and frees Lean objects, and turns errors into Python exceptions.
The vectors test this layer only through the regeneration and comparison of B1.

An export that can fail returns the code and the message of its typed Lean error.
The C layer raises them as an exception of `ethlib.errors`, one class for each primitive.
C reads the code from the pair that the export returns.
A wrong field offset in C would give a wrong code, and no theorem covers that read.
Some wrong argument sizes are caught in C first, and raise `ValueError` with no code.

One generic converter in `pyvalue.c` passes typed values between Python and Lean.
It knows the constructors of one Lean type of Python values, and the type of no export.
Such an export needs only a short C wrapper that passes its Lean function and its arity to the generic caller, and no byte format of its own.
The C code repeats the order of the constructors of the Lean type, and no theorem checks it.
A change to that order needs the same change in C.

On the Lean side, every typed export requires a theorem for the type of its result.
That theorem says that reading back the value of a result gives that result, so two results never become one value of the Lean type.
The converter refuses a Lean `dict` with a repeated key, which would drop a value.
It counts the parts and the bytes of each call from Python, and refuses more than a million parts or 512 MiB.
However much a call shares between its lists, the converter then builds at most a million parts and 512 MiB.
A property test sends random nested values through Lean and back, with integers of thousands of bits.
A separate test passes a value at the deepest level allowed.
Another property test sends values that the converter must refuse, and checks that each raises `TypeError` or `ValueError`, never a crash.
The converter refuses an `int` wider than 65536 bits, so that each call holds the GIL for a short time.
Lean reads and writes the digits of a large `int` by halves, in time about `d log d` for `d` digits.
Each export that moves to typed values removes its own C, and the line count above shows it.

### B5. Compiler substitutions in this repository

`@[implemented_by]` and `@[extern]` make the compiled code run something other than the definition, with no proof that the two agree.
`@[csimp]` replaces a function with one proved equal to it, so it adds no logical trust, but the code that runs is still not the definition a reader reads.

The repository has none of the three today.
`lake exe check-decls` reports any of them, and fails on one that is not in its baseline.

### B6. The build and its publication

`setup.py` runs `lake build Exports`, and links the objects under `.lake/build/ir/EthLib/` with `libleanshared`, `libgmp` and `libuv`.
`.github/workflows/publish.yml` builds the wheels with `cibuildwheel`, cleans the build before each wheel, and publishes them to PyPI.

The workflow installs elan and the Lean toolchain that `lean-toolchain` names from pinned releases, and checks the SHA-256 digest of each archive first.
Each wheel runs the vector suites and the check of the pinned vectors before it is published.
A build provenance attestation records which workflow run, at which commit, built each wheel and the sdist.

## Gap C: is the proof itself sound?

### C1. The Lean kernel and its axioms

Every theorem trusts the Lean kernel, and whichever of the three standard axioms it uses: `propext`, `Classical.choice` and `Quot.sound`.
Those three are the allowed set; a theorem may use fewer.

`lake exe check-decls` checks dependencies: no declaration may depend on an axiom outside that set, apart from those in its baseline.
It does not check the kernel, and it does not show that the axioms are consistent.
That rests on Lean's own design and review.
The replay of C3 uses Lean's own kernel, so no independent type checker covers EthLib yet.

### C2. Tactics that trust compiled code

`native_decide`, `bv_decide` and `decide +native` each add an axiom that trusts the compiled code.
A proof that uses one is no longer checked by the kernel alone.
It also trusts every `@[implemented_by]` and `@[extern]` that the compiled code reaches (B2).

`CONTRIBUTING.md` does not allow these tactics, and a new use fails `lake exe check-decls`.

<!-- generated: native -->
No theorem uses them.
<!-- end generated -->

### C3. Declarations the kernel did not check

A metaprogram can add a declaration to the environment without the kernel checking it.
The `replay` workflow catches such a declaration with leanchecker.
leanchecker replays every declaration of EthLib into Lean's kernel, proof bodies included.
First, the workflow checks that leanchecker rejects a fixture theorem of `False` that the kernel never checked.
The replay uses Lean's own kernel, so it does not protect against a bug in that kernel (C1).

The workflow runs every Monday and on each push to `master`, but a newer push cancels a replay still in progress.
So only the weekly run is sure to finish.

## Gap D: does the use of EthLib hold together?

### D1. The client's obligations

A client chooses the right operation for its fork, passes inputs of the right form, and handles errors.

XMSS adds one more obligation: never sign two different messages at one leaf index with one secret key.
Each leaf index names a one-time signing key, and nothing in EthLib records which leaf indices were used, so the caller must prevent reuse.
The Lean and Python docstrings of `sign` both say so.

leanSPHINCS adds another.
Never sign more than `2^30` messages with one secret key.
Nothing in EthLib counts signatures, so the caller must.
The Lean and Python docstrings of `sign` both say so.

Password derivations add bounds on memory and time.
The ROMix table of scrypt has a payload of `128 * r * N` bytes, and the expanded password and the mixed blocks take at least `128 * r * p` bytes each.
The key itself, of either derivation, can be up to `(2^32 - 1) * 32` bytes, about 128 GiB.
Parameters within the bounds of RFC 7914 can ask for more memory than any machine has.
For example, `N = 2^40` and `r = 8` pass the check on the cost and ask for a table of `2^50` bytes, one pebibyte.
Likewise, `r = 1` and `p = 2^30 - 1` pass the check on `p` and ask for about 128 GiB per buffer.
No error is returned then: the Lean runtime aborts the process, or the operating system kills it.
The work of scrypt grows with `N * r * p` and with the key length.
The work of PBKDF2 grows with `c` times the number of 32-byte blocks of the key.
So a hostile parameter can also make a call run for an impractical time.
A keystore file gives `N`, `r` and `p`, or `c`, and the key length `dklen`.
So a caller that reads one must bound `r * N`, `r * p`, `c` and `dklen` before it calls the derivation.
The Lean docstrings of `pbkdf2`, `scrypt` and `romix` say so.
Keystore decryption does this itself with a model of the cost, against limits that its caller chooses.

### D2. Dependencies

`lake-manifest.json` pins every dependency.

<!-- generated: pins -->
The specification requires no package.
The package requires Mathlib, at `v4.35.0`, commit `56a0058`.
The package requires VCVio, at `bbf05ee`.
Only the proofs import them.
The Lean toolchain is `leanprover/lean4:v4.35.0`.
<!-- end generated -->

VCVio defines the oracle computations and probabilities in which the security games are stated.
The proofs below import it, directly or through another file.
A directory is listed when at least one file under it imports VCVio, or when the file of the same name beside it does, such as `Wots.lean` beside `Wots/`.
So a listed directory can hold files that do not import VCVio.
The files named `Proofs.lean` are roots that gather the proofs of a domain, so they are not listed.

<!-- generated: vcvio-users -->
- `EthLib/Consensus/Proofs/Accessors/`
- `EthLib/Consensus/Proofs/DataAvailability/`
- `EthLib/Consensus/Proofs/Gossip/`
- `EthLib/Consensus/Proofs/LightClient/`
- `EthLib/Consensus/Proofs/PqKeys/`
- `EthLib/Consensus/Proofs/SigningRandomOracle.lean`
- `EthLib/Cryptography/Proofs/Aes/`
- `EthLib/Cryptography/Proofs/BadOnBudget.lean`
- `EthLib/Cryptography/Proofs/BadOnGrowth.lean`
- `EthLib/Cryptography/Proofs/Bls/`
- `EthLib/Cryptography/Proofs/DerivationTable.lean`
- `EthLib/Cryptography/Proofs/EvalDistEq.lean`
- `EthLib/Cryptography/Proofs/ExceptTAnswers.lean`
- `EthLib/Cryptography/Proofs/HashSig/`
- `EthLib/Cryptography/Proofs/IndependentAnswers.lean`
- `EthLib/Cryptography/Proofs/IndependentOutside.lean`
- `EthLib/Cryptography/Proofs/Kzg/`
- `EthLib/Cryptography/Proofs/LazyPermutation.lean`
- `EthLib/Cryptography/Proofs/LogKeys.lean`
- `EthLib/Cryptography/Proofs/LoggedUntilBad.lean`
- `EthLib/Cryptography/Proofs/Merkle/`
- `EthLib/Cryptography/Proofs/ProgrammedPermutation.lean`
- `EthLib/Cryptography/Proofs/QueryAvoidance.lean`
- `EthLib/Cryptography/Proofs/RandomOracleTable.lean`
- `EthLib/Cryptography/Proofs/Secp256k1/`
- `EthLib/Cryptography/Proofs/Sphincs/`
- `EthLib/Cryptography/Proofs/TaggedLazyPermutation.lean`
- `EthLib/Cryptography/Proofs/UniformReads.lean`
- `EthLib/Cryptography/Proofs/Vrf/`
- `EthLib/Cryptography/Proofs/Wots/`
- `EthLib/Cryptography/Proofs/Xmss/`
- `EthLib/Execution/Proofs/Trie/`
- `EthLib/Serialization/Proofs/Ssz/`

No specification file imports it.
<!-- end generated -->

### D3. The KZG trusted setup

The setup raises three separate assumptions, and each use of KZG relies on a different subset of them.

- Provenance: the embedded bytes are the ceremony's output.
  They match consensus-specs `presets/mainnet/trusted_setups/trusted_setup_4096.json` byte for byte, and `Kzg/TrustedSetupData.lean` records that source, the commit it comes from and its sha256.
- Algebraic consistency: the bytes decode to valid points, the monomial points are powers of one secret, and the Lagrange points are the matching basis.
  For the embedded bytes, the first part is proved only in part, the third is proved if the bytes decode, and the second is not.
  `TrustedSetup.ofHex_valid` (`Proofs/Kzg/TrustedSetup.lean`) proves that, if they decode, each point is on its curve.
  No theorem says that they decode.
  If they decode, `TrustedSetup.ofHex_torsion` proves that each monomial point of `G1` has an order that divides `r`.
  No theorem says this of the Lagrange points or of the points of `G2`.
  If they decode, `TrustedSetup.ofHex_lagrangeOfMonomial` (`Proofs/Kzg/SetupLagrange/Embedded.lean`) proves that each Lagrange point of `G1` is the sum of the monomial points times the coefficients of its basis polynomial.
  So the Lagrange points are the matching basis of whatever secret the monomial points hold.
  The kernel checks this on the embedded data, in three rounds of 256 transforms of size 16.
  It also checks that each of the 8192 strings of `G1` encodes its table point, so decompression gives that point.
  The kernel computes no square root: each table point is a certificate that it checks with three products.
  Compiled code computes two tables of intermediate points when the files are built, and the repository holds no copy of them.
  A wrong table only makes a kernel check fail.
  This is a second recorded exception to the rule of a few seconds for concrete facts in [CONTRIBUTING.md](CONTRIBUTING.md#known-answers).
  It costs about 20 CPU-minutes per replay, measured one module at a time, in 56 modules, and about as much per build.
  Each module takes 14 to 29 seconds and at most 3.3 GB to replay.
  The Python suite checks for every point that it decodes and lies in the subgroup (`bindings/python/tests/kzg/test_trusted_setup.py`).
  `checksSufficient` covers the ceremony's monomial points, under its hypotheses.
  `TrustedSetup.WellFormed s τ` (`Proofs/Kzg/Commitment.lean`) states the consistency of a setup `s` with a secret `τ`.
  The theorems on commitments and on honest proofs take it as a hypothesis.
  For the embedded setup, `TrustedSetup.ofHex_wellFormed` reduces it to the monomial points.
  If the setup decodes and its monomial points of `G1` and `G2` represent the powers of `τ`, it is well formed at `τ`.
  That some `τ` makes the monomial points represent its powers is an assumption, and no theorem proves it.
- Secrecy: no one knows the secret, which holds if at least one ceremony participant was honest.
  Only binding, a security property, needs it; a theorem about parsing, or that an honest proof verifies, does not.

### D4. The vectors

A client that tests against the vectors trusts whatever produced their expected values.
The KZG vectors and the `eth_*` BLS vectors match the consensus-specs `v1.7.0-alpha.12` general vectors byte for byte.
The other BLS vectors match `ethereum/bls12-381-tests` `v0.1.2`, and the hash-to-curve vectors come from RFC 9380.
`v1.7.0-alpha.12` was the last release before consensus-specs removed its KZG specification, in ethereum/consensus-specs#5398.
