import EthCryptographySpecs.Xmss.Ots

/-!
# `Xmss.Merkle`

The Merkle tree over the one-time keys, one leaf per epoch.

Its root is half the public key, so one root stands for `2 ^ 32` one-time keys.

A signature carries the 32 siblings that lead its leaf back to that root.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Nodes -/

/-- The parent of two nodes, hashed under its own place in the tree. -/
def merkleNode (pp : PublicParam) (level index : Nat) (left right : Digest) :
    Digest :=
  -- - payload: two children of DIGEST_LEN bytes = 2 * 16 = 32
  -- - hash input: TWEAK_LEN + PUBLIC_PARAM_LEN + payload = 16 + 16 + 32 = 64
  tweakHash pp .merkle (UInt32.ofNat level) (UInt32.ofNat index)
    (packBytes left ++ packBytes right)

/-- A node the key's epochs never reach, derived from the secret seed. -/
def fillerNode (pp : PublicParam) (seed : Seed) (level index : Nat) : Digest :=
  -- Deriving it keeps the unsigned epochs hidden and costs no storage.
  tweakHash pp .filler (UInt32.ofNat level) (UInt32.ofNat index)
    (packBytes seed)

/-! ## The tree -/

/-- A key signs at the epochs `epochStart` to `epochEnd`, and nowhere else. -/
structure Tree where
  /-- The call site every node of this tree is hashed under. -/
  publicParam : PublicParam
  /-- The secret the filler nodes are derived from. -/
  seed : Seed
  /-- The first epoch the key signs at. -/
  epochStart : Epoch
  /-- The last epoch the key signs at. -/
  epochEnd : Epoch

/-- Whether the subtree at `index` on `level` holds an epoch of the key. -/
def Tree.covers (t : Tree) (level index : Nat) : Bool :=
  -- A node on `level` spans the epochs whose leading bits are `index`.
  --
  -- So shifting the two end epochs the same way brackets the nodes reached.
  t.epochStart.toNat >>> level ≤ index && index ≤ t.epochEnd.toNat >>> level

/-- The node at `index` on `level`, over the leaves `leaf`. -/
def Tree.node (t : Tree) (leaf : Nat → Digest) (level index : Nat) : Digest :=
  -- Testing the range first cuts an unused subtree off at its top.
  --
  -- A key covering `R` epochs reaches `O(R + 32)` nodes, never `2 ^ 32`.
  if t.covers level index then
    match level with
    -- One leaf per epoch, and the epoch is the leaf's index.
    | 0 => leaf index
    -- The two children of `index` on `level + 1` are `2 * index` and one more.
    | l + 1 => merkleNode t.publicParam (l + 1) index
        (t.node leaf l (2 * index)) (t.node leaf l (2 * index + 1))
  else
    fillerNode t.publicParam t.seed level index

/-- The root of the tree: half of the public key. -/
def Tree.root (t : Tree) (leaf : Nat → Digest) : Digest :=
  t.node leaf LOG_LIFETIME 0

/-! ## The authentication path -/

/-- The sibling of the path node at `level`: its parent's other child. -/
def siblingIndex (epoch level : Nat) : Nat :=
  -- Shifting names the path node, flipping its bottom bit names the sibling.
  (epoch >>> level) ^^^ 1

/-- The 32 siblings a signature at `epoch` carries, from the leaf upward. -/
def Tree.authPath (t : Tree) (leaf : Nat → Digest) (epoch : Epoch) :
    Vector Digest LOG_LIFETIME :=
  Vector.ofFn fun level => t.node leaf level (siblingIndex epoch.toNat level)

/-! ## Climbing back to the root -/

namespace Internal

/-- Fold the sibling at `level` into the node the verifier holds. -/
def climbStep (pp : PublicParam) (epoch level : Nat)
    (current sibling : Digest) : Digest :=
  -- Bit `level` of the epoch says which child of its parent the path node is.
  if (epoch >>> level) % 2 == 0 then
    merkleNode pp (level + 1) (epoch >>> (level + 1)) current sibling
  else
    merkleNode pp (level + 1) (epoch >>> (level + 1)) sibling current

/-- Climb the bottom `levels` levels of the path, starting from the leaf. -/
def climbUpto (pp : PublicParam) (epoch : Nat)
    (path : Vector Digest LOG_LIFETIME) (levels : Nat)
    (hl : levels ≤ LOG_LIFETIME) (leaf : Digest) : Digest :=
  match levels with
  | 0 => leaf
  -- The last step folds in the sibling at `l`, after climbing the `l` below it.
  | l + 1 => climbStep pp epoch l
      (climbUpto pp epoch path l (by omega) leaf) (path[l]'(by omega))

end Internal

/-- The root an authentication path reaches from a leaf. -/
def climb (pp : PublicParam) (epoch : Epoch)
    (path : Vector Digest LOG_LIFETIME) (leaf : Digest) : Digest :=
  Internal.climbUpto pp epoch.toNat path LOG_LIFETIME (Nat.le_refl _) leaf

end EthCryptographySpecs.Xmss
