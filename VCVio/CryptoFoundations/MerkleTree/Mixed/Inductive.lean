/-
Copyright (c) 2026 Gregor Mitscha-Baude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

module

public import ToMathlib.Data.IndexedBinaryTree.Perfect
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
public import VCVio.CryptoFoundations.MerkleTree.Mixed.Defs

/-!
# Trees without injections as inductive Merkle trees

Without injected payloads, a `MixedMerkleTree` of height `K` is the inductive Merkle tree
(`InductiveMerkleTree`) over the perfect skeleton of height `K` whose leaves are the hashes of the
payloads:

* `perfectLeaves g k t`: the leaves of the perfect subtree of height `k` at heap index `t`; leaf
  `j` is `g (t * 2 ^ k + j)`. `nodeValue compress g k t` is the root of its built tree.
* `node_eq_nodeValue`: a node of a tree without injections is the root of the built subtree.
* `perfectLeaves_get`: leaf `SkeletonLeafIndex.ofNat k i` is `g i`.
* `generateProof_perfectLeaves`: the inductive tree's proof for leaf `SkeletonLeafIndex.ofNat k i`
  lists the siblings `(i >>> j) ^^^ 1`, from the root down.
* `climb_eq_getPutativeRootWithHash`: a climb without injections is the putative root of the
  reversed path.
-/

@[expose] public section

namespace MixedMerkleTree

open BinaryTree InductiveMerkleTree

universe u v

section Perfect

variable {α : Type u}

/-- The leaves of the perfect subtree of height `k` at heap index `t`: leaf `j` is
`g (t * 2 ^ k + j)`. -/
def perfectLeaves (g : ℕ → α) : (k : ℕ) → ℕ → LeafData α (Skeleton.perfect k)
  | 0, t => .leaf (g t)
  | k + 1, t => .internal (perfectLeaves g k (2 * t)) (perfectLeaves g k (2 * t + 1))

/-- The digest of the node at height `j` and heap index `t` of the tree with leaves `g`. -/
def nodeValue (compress : α → α → α) (g : ℕ → α) (j t : ℕ) : α :=
  (populateUp (perfectLeaves g j t) compress).getRootValue

/-- A node at height `0` is its leaf. -/
theorem nodeValue_zero (compress : α → α → α) (g : ℕ → α) (t : ℕ) :
    nodeValue compress g 0 t = g t := rfl

/-- A node at height `j + 1` compresses its two children. -/
theorem nodeValue_succ (compress : α → α → α) (g : ℕ → α) (j t : ℕ) :
    nodeValue compress g (j + 1) t =
      compress (nodeValue compress g j (2 * t)) (nodeValue compress g j (2 * t + 1)) := rfl

/-- Without injections, a node is the root of the built subtree over the hashed payloads. -/
theorem node_eq_nodeValue {Payload : Type v} (hash : Payload → α) (compress : α → α → α)
    (K : ℕ) (leaves : ℕ → Payload) :
    ∀ l i, node hash compress K leaves (fun _ ↦ none) l i =
      nodeValue compress (fun j ↦ hash (leaves j)) l i
  | 0, _ => rfl
  | l + 1, i => by
    rw [node, nodeValue_succ, node_eq_nodeValue hash compress K leaves l,
      node_eq_nodeValue hash compress K leaves l]
    rfl

/-- The inductive tree's proof for the leaf `ofNat k i` of the perfect subtree containing it lists
the siblings `(i >>> j) ^^^ 1` from the root down. -/
theorem generateProof_perfectLeaves (compress : α → α → α) (g : ℕ → α) (k i : ℕ) :
    (generateProof (buildMerkleTreeWithHash (perfectLeaves g k (i / 2 ^ k)) compress)
        (SkeletonLeafIndex.ofNat k i)).toList =
      ((List.range k).map fun j ↦ nodeValue compress g j ((i >>> j) ^^^ 1)).reverse := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hdiv : i / 2 ^ (k + 1) = i / 2 ^ k / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have hx := xor_one_eq (i / 2 ^ k)
    have hdm := Nat.div_add_mod (i / 2 ^ k) 2
    rw [List.range_succ, List.map_append, List.reverse_append, List.map_cons, List.map_nil,
      List.reverse_singleton, List.singleton_append, Nat.shiftRight_eq_div_pow, ← ih]
    by_cases hb : i / 2 ^ k % 2 = 0
    · rw [show SkeletonLeafIndex.ofNat (k + 1) i = .ofLeft (SkeletonLeafIndex.ofNat k i) by
        simp only [SkeletonLeafIndex.ofNat, hb, ↓reduceIte]]
      have h2 : 2 * (i / 2 ^ (k + 1)) = i / 2 ^ k := by omega
      have h3 : 2 * (i / 2 ^ (k + 1)) + 1 = i / 2 ^ k ^^^ 1 := by omega
      change nodeValue compress g k (2 * (i / 2 ^ (k + 1)) + 1) ::
        (generateProof (buildMerkleTreeWithHash
          (perfectLeaves g k (2 * (i / 2 ^ (k + 1)))) compress) _).toList = _
      rw [h3, h2]
    · rw [show SkeletonLeafIndex.ofNat (k + 1) i = .ofRight (SkeletonLeafIndex.ofNat k i) by
        simp only [SkeletonLeafIndex.ofNat, hb, ↓reduceIte]]
      have h2 : 2 * (i / 2 ^ (k + 1)) + 1 = i / 2 ^ k := by omega
      have h3 : 2 * (i / 2 ^ (k + 1)) = i / 2 ^ k ^^^ 1 := by omega
      change nodeValue compress g k (2 * (i / 2 ^ (k + 1))) ::
        (generateProof (buildMerkleTreeWithHash
          (perfectLeaves g k (2 * (i / 2 ^ (k + 1)) + 1)) compress) _).toList = _
      rw [h2, h3]

/-- Leaf `ofNat k i` of the perfect subtree containing it is `g i`. -/
theorem perfectLeaves_get (g : ℕ → α) (k i : ℕ) :
    (perfectLeaves g k (i / 2 ^ k)).get (SkeletonLeafIndex.ofNat k i) = g i := by
  induction k with
  | zero => simp only [Nat.pow_zero, Nat.div_one]; rfl
  | succ k ih =>
    have hdiv : i / 2 ^ (k + 1) = i / 2 ^ k / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have hdm := Nat.div_add_mod (i / 2 ^ k) 2
    by_cases hb : i / 2 ^ k % 2 = 0
    · rw [show SkeletonLeafIndex.ofNat (k + 1) i = .ofLeft (SkeletonLeafIndex.ofNat k i) by
        simp only [SkeletonLeafIndex.ofNat, hb, ↓reduceIte]]
      change (perfectLeaves g k (2 * (i / 2 ^ (k + 1)))).get _ = _
      rw [show 2 * (i / 2 ^ (k + 1)) = i / 2 ^ k by omega, ih]
    · rw [show SkeletonLeafIndex.ofNat (k + 1) i = .ofRight (SkeletonLeafIndex.ofNat k i) by
        simp only [SkeletonLeafIndex.ofNat, hb, ↓reduceIte]]
      change (perfectLeaves g k (2 * (i / 2 ^ (k + 1)) + 1)).get _ = _
      rw [show 2 * (i / 2 ^ (k + 1)) + 1 = i / 2 ^ k by omega, ih]

/-- The last sibling of a climb without injections is compressed in last, on the side of bit
`path.length` of the index. -/
theorem climb_none_append {Payload : Type v} (hash : Payload → α) (compress : α → α → α)
    (path : List α) (sib : α) (i : ℕ) (x : α) :
    climb hash compress (fun _ ↦ none) i x (path ++ [sib]) =
      pairUp compress (i / 2 ^ path.length) (climb hash compress (fun _ ↦ none) i x path) sib := by
  rw [climb_append, climb_cons, climb_nil, Nat.shiftRight_eq_div_pow]
  rfl

end Perfect

/-- A climb without injections is the inductive tree's putative root at the leaf `ofNat k i`, for
any proof listing the path from the root down. -/
theorem climb_eq_getPutativeRootWithHash {Payload : Type u} {α : Type v} (hash : Payload → α)
    (compress : α → α → α) (i : ℕ) (leaf : α) (k : ℕ) (path : List α)
    (idx : SkeletonLeafIndex (Skeleton.perfect k)) (v : List.Vector α idx.depth)
    (hidx : idx = SkeletonLeafIndex.ofNat k i) (hv : v.toList = path.reverse) :
    climb hash compress (fun _ ↦ none) i leaf path =
      getPutativeRootWithHash idx leaf v compress := by
  induction k generalizing path with
  | zero =>
    subst hidx
    have : path = [] := by
      have := congrArg List.length hv
      simp only [List.Vector.toList_length, SkeletonLeafIndex.depth_ofNat,
        List.length_reverse] at this
      exact List.eq_nil_of_length_eq_zero this.symm
    subst this
    rfl
  | succ k ih =>
    have hlen : path.length = k + 1 := by
      have := congrArg List.length hv
      simp only [List.Vector.toList_length, hidx, SkeletonLeafIndex.depth_ofNat,
        List.length_reverse] at this
      exact this.symm
    obtain ⟨path, sib, rfl⟩ := List.eq_nil_or_concat' path |>.resolve_left
      (by rintro rfl; simp only [List.length_nil] at hlen; omega)
    replace hlen : path.length = k := by
      simp only [List.length_append, List.length_singleton] at hlen; omega
    obtain ⟨l, hl⟩ := v
    simp only [List.Vector.toList_mk, List.reverse_append, List.reverse_singleton,
      List.singleton_append] at hv
    subst hv
    rw [climb_none_append, hlen]
    by_cases hb : i / 2 ^ k % 2 = 0
    · have hidx' : idx = .ofLeft (SkeletonLeafIndex.ofNat k i) := by
        rw [hidx]; simp only [SkeletonLeafIndex.ofNat, hb, ↓reduceIte]
      subst hidx'
      simp only [pairUp, hb, ↓reduceIte, getPutativeRootWithHash]
      rw [ih path _ ⟨path.reverse, by simp only [List.length_reverse, SkeletonLeafIndex.depth_ofNat,
        hlen]⟩ rfl rfl]
      rfl
    · have hidx' : idx = .ofRight (SkeletonLeafIndex.ofNat k i) := by
        rw [hidx]; simp only [SkeletonLeafIndex.ofNat, hb, ↓reduceIte]
      subst hidx'
      simp only [pairUp, hb, ↓reduceIte, getPutativeRootWithHash]
      rw [ih path _ ⟨path.reverse, by simp only [List.length_reverse, SkeletonLeafIndex.depth_ofNat,
        hlen]⟩ rfl rfl]
      rfl

end MixedMerkleTree
