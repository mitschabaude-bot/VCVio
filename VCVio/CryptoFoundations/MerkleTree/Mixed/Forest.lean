/-
Copyright (c) 2026 Gregor Mitscha-Baude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

module

public import VCVio.CryptoFoundations.MerkleTree.HashForest.Binary
public import VCVio.CryptoFoundations.MerkleTree.Mixed.Defs

/-!
# Caps of Merkle trees with injected payloads as hash forests

The cap of height `h` of a `MixedMerkleTree` is a `MerkleHashForest.Forest` of `2 ^ h` roots
(`forest`): a leaf is a leaf operation on its payload, a node a node operation on its two
children, and an injecting node a node operation whose first child is the node operation on its
children and whose second child is the leaf operation on its payload. The operations are
unaddressed and carry no context.

`evaluateForestWithHash_forest`: under any answer function that hashes a leaf operation's payload
with `hash` and compresses a node operation's two children with `compress`, the forest evaluates to
the cap.
-/

public section

namespace MixedMerkleTree

open MerkleHashForest

universe u v

variable {Payload : Type u} {Digest : Type v}

/-- The hash-forest operations of a mixed Merkle tree: unaddressed leaf and node operations. -/
abbrev Operations (Payload : Type u) (Digest : Type v) :=
  MerkleHashForest.Tree BinaryOperationKind Unit Unit Payload Digest

/-- The leaf operation on `p`. -/
@[expose]
def leafOp (p : Payload) : Operations Payload Digest :=
  .operation .leaf () () [.payload p]

/-- The node operation on two children. -/
@[expose]
def nodeOp (left right : Operations Payload Digest) : Operations Payload Digest :=
  .operation .node () () [.child left, .child right]

/-- The operation tree of the node at height `l` and index `i`, as `node`. -/
@[expose]
def nodeTree (K : ℕ) (leaves : ℕ → Payload) (inj : ℕ → Option (ℕ → Payload)) :
    ℕ → ℕ → Operations Payload Digest
  | 0, i => leafOp (leaves i)
  | l + 1, i =>
    match inj (K - (l + 1)) with
    | some f => nodeOp (nodeOp (nodeTree K leaves inj l (2 * i))
        (nodeTree K leaves inj l (2 * i + 1))) (leafOp (f i))
    | none => nodeOp (nodeTree K leaves inj l (2 * i)) (nodeTree K leaves inj l (2 * i + 1))

/-- The cap of height `h` as a forest of `2 ^ h` roots. -/
@[expose]
def forest (K : ℕ) (leaves : ℕ → Payload) (inj : ℕ → Option (ℕ → Payload)) (h : ℕ) :
    Forest BinaryOperationKind Unit Unit Payload Digest (2 ^ h) :=
  ⟨(List.range (2 ^ h)).map (nodeTree K leaves inj (K - h)), by
    rw [List.length_map, List.length_range]⟩

variable (hash : Payload → Digest) (compress : Digest → Digest → Digest)
  (answer : Query BinaryOperationKind Unit Unit Payload Digest → Digest)

/-- `answer` hashes leaf operations with `hash` and compresses node operations with `compress`. -/
structure Answers : Prop where
  leaf : ∀ p, answer ⟨.leaf, (), (), [.payload p]⟩ = hash p
  node : ∀ a b, answer ⟨.node, (), (), [.child a, .child b]⟩ = compress a b

variable {hash compress answer}

theorem evaluateTreeWithHash_leafOp (h : Answers hash compress answer) (p : Payload) :
    evaluateTreeWithHash answer (leafOp p) = hash p := by
  simp only [evaluateTreeWithHash, leafOp, Internal.evaluateTreeWithHash,
    Internal.evaluateInputsWithHash, Internal.evaluateInputWithHash]
  exact h.leaf p

theorem evaluateTreeWithHash_nodeOp (h : Answers hash compress answer)
    (left right : Operations Payload Digest) :
    evaluateTreeWithHash answer (nodeOp left right) =
      compress (evaluateTreeWithHash answer left) (evaluateTreeWithHash answer right) := by
  simp only [evaluateTreeWithHash, nodeOp, Internal.evaluateTreeWithHash,
    Internal.evaluateInputsWithHash, Internal.evaluateInputWithHash]
  exact h.node _ _

/-- The operation tree of a node evaluates to the node. -/
theorem evaluateTreeWithHash_nodeTree (h : Answers hash compress answer) (K : ℕ)
    (leaves : ℕ → Payload) (inj : ℕ → Option (ℕ → Payload)) :
    ∀ l i, evaluateTreeWithHash answer (nodeTree K leaves inj l i) =
      node hash compress K leaves inj l i
  | 0, i => evaluateTreeWithHash_leafOp h _
  | l + 1, i => by
    have ih := evaluateTreeWithHash_nodeTree h K leaves inj l
    rw [nodeTree, node]
    cases inj (K - (l + 1)) with
    | some f =>
      simp only [Option.map_some, inject, evaluateTreeWithHash_nodeOp h, ih,
        evaluateTreeWithHash_leafOp h]
    | none => simp only [Option.map_none, inject, evaluateTreeWithHash_nodeOp h, ih]

/-- **The cap is a hash forest.** The forest of the cap of height `h` evaluates to the cap. -/
theorem evaluateForestWithHash_forest (h : Answers hash compress answer) (K : ℕ)
    (leaves : ℕ → Payload) (inj : ℕ → Option (ℕ → Payload)) (c : ℕ) :
    (evaluateForestWithHash answer (forest K leaves inj c)).toList =
      cap hash compress K leaves inj c := by
  change List.map (evaluateTreeWithHash answer)
    (List.map (nodeTree K leaves inj (K - c)) (List.range (2 ^ c))) = _
  rw [cap, List.map_map]
  exact List.map_congr_left fun i _ ↦ evaluateTreeWithHash_nodeTree h K leaves inj _ i

end MixedMerkleTree
