/-
Copyright (c) 2026 Gregor Mitscha-Baude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Mixed.Defs
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Knowledge extraction for mixed Merkle caps

Fixed leaf hashes and compressions are one primitive on `Op`. A node extractor receives the
same explicit coins as its node adversary. `knowledge_bound` reduces disagreement with the
named, top-down extraction to failures of the extractors assigned to the derived node adversaries.
The injection schedule uses global depths; an opening's payloads use depths below its cap.
-/

public section

namespace MixedMerkleTree.Knowledge

open OracleComp
open scoped ENNReal

universe u v

variable {Payload : Type u} {Digest : Type v} {Coins : Type}

/-- A leaf-hash input or an ordered pair of compression inputs. -/
abbrev Op (Payload : Type u) (Digest : Type v) := Payload ⊕ (Digest × Digest)

/-- The fixed primitive answering both kinds of node operation. -/
@[expose]
def answer (hash : Payload → Digest) (compress : Digest → Digest → Digest) :
    Op Payload Digest → Digest
  | .inl p => hash p
  | .inr (a, b) => compress a b

/-- A node adversary outputs a target digest and all preimages it reveals, on explicit coins. -/
abbrev NodeAdversary (Coins : Type) (Payload : Type u) (Digest : Type v) :=
  Coins → Digest × List (Op Payload Digest)

/-- An extractor assignment chooses a same-coins extractor for each node adversary. -/
abbrev ExtractorMap (Coins : Type) (Payload : Type u) (Digest : Type v) :=
  NodeAdversary Coins Payload Digest → Coins → Op Payload Digest

/-- A revealed preimage of the target differs from the extractor's prediction. -/
@[expose]
def NodeBad (f : Op Payload Digest → Digest) (B : NodeAdversary Coins Payload Digest)
    (E : Coins → Op Payload Digest) (c : Coins) : Prop :=
  ∃ q ∈ (B c).2, f q = (B c).1 ∧ q ≠ E c

/-- The node game tests failure with the adversary and extractor on the same uniform coins. -/
@[expose]
noncomputable def nodeGame [SampleableType Coins] (f : Op Payload Digest → Digest)
    (B : NodeAdversary Coins Payload Digest) (E : Coins → Op Payload Digest) : ProbComp Bool :=
  open Classical in do
    let c ← $ᵗ Coins
    return decide (NodeBad f B E c)

/-- Probability that some revealed preimage escapes the same-coins node extractor. -/
@[expose]
noncomputable def nodeFail [SampleableType Coins] (f : Op Payload Digest → Digest)
    (B : NodeAdversary Coins Payload Digest) (E : Coins → Op Payload Digest) : ℝ≥0∞ :=
  Pr{let c ← $ᵗ Coins}[NodeBad f B E c]

/-- A leaf opening with injected payloads by depth below the cap and bottom-up siblings. -/
structure Opening (Payload : Type u) (Digest : Type v) where
  /-- The global leaf index. -/
  index : ℕ
  /-- The leaf's payload. -/
  payload : Payload
  /-- Injected payloads by depth below the cap. -/
  pays : ℕ → Option Payload
  /-- Sibling digests, starting at the leaf. -/
  path : List Digest

/-- An opening has the public shape and climbs to its indexed cap entry. -/
@[expose]
def Opening.Verifies (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (K h : ℕ) (inj : ℕ → Bool) (cap : List Digest) (o : Opening Payload Digest) : Prop :=
  h ≤ K ∧ cap.length = 2 ^ h ∧ o.index < 2 ^ K ∧ o.path.length = K - h ∧
    (∀ d < K - h, (o.pays d).isSome = inj (h + d)) ∧
    cap[o.index >>> (K - h)]? =
      some (climb hash compress o.pays o.index (hash o.payload) o.path)

/-- A Merkle adversary outputs a cap and a list of openings on explicit coins. -/
abbrev MerkleAdversary (Coins : Type) (Payload : Type u) (Digest : Type v) :=
  Coins → List Digest × List (Opening Payload Digest)

/-- The four operation stages at a tree node. -/
inductive Stage where
  /-- Hash a leaf payload. -/
  | leaf
  /-- Compress the two tree children. -/
  | children
  /-- Hash an injected payload. -/
  | payload
  /-- Compress the child compression with the injected hash. -/
  | injection
  deriving DecidableEq

/-- An operation position uses global depth and the node index at that depth. -/
structure Position where
  /-- Depth below the whole tree's root. -/
  depth : ℕ
  /-- Node index at this depth. -/
  index : ℕ
  /-- Which operation of the node this position represents. -/
  stage : Stage
  deriving DecidableEq

/-- Positions below the cap: leaves hash, inner nodes compress, scheduled nodes also inject. -/
@[expose]
def Position.Valid (K h : ℕ) (inj : ℕ → Bool) (v : Position) : Prop :=
  h ≤ v.depth ∧ v.depth ≤ K ∧ v.index < 2 ^ v.depth ∧
    match v.stage with
    | .leaf => v.depth = K
    | .children => v.depth < K
    | .payload | .injection => v.depth < K ∧ inj v.depth = true

/-- The finite set of all operation positions determined by the tree, cap, and schedule. -/
@[expose]
noncomputable def positions (K h : ℕ) (inj : ℕ → Bool) : Finset Position :=
  open Classical in
  ((Finset.range (K + 1)).biUnion fun d ↦
    (Finset.range (2 ^ d)).biUnion fun i ↦
      ({Stage.leaf, .children, .payload, .injection} : Finset Stage).image
        fun s ↦ Position.mk d i s).filter (Position.Valid K h inj)

/-- The operation exposing a node's final digest at the given global depth and index. -/
@[expose]
def nodePosition (K : ℕ) (inj : ℕ → Bool) (d i : ℕ) : Position :=
  ⟨d, i, if d = K then .leaf else if inj d then .injection else .children⟩

/-- A top-down rank; the intermediate child compression and injected hash follow the injection. -/
@[expose]
def Position.rank (v : Position) : ℕ :=
  2 * v.depth + match v.stage with
    | .leaf | .injection => 0
    | .children | .payload => 1

/-- The parent operation and the selected child (`true` for right); `none` means a cap entry. -/
@[expose]
def Position.parent (h : ℕ) (inj : ℕ → Bool) (v : Position) : Option (Position × Bool) :=
  match v.stage with
  | .payload => some (⟨v.depth, v.index, .injection⟩, true)
  | .children =>
    if inj v.depth then some (⟨v.depth, v.index, .injection⟩, false)
    else if v.depth ≤ h then none
    else some (⟨v.depth - 1, v.index / 2, .children⟩, v.index % 2 != 0)
  | .leaf | .injection =>
    if v.depth ≤ h then none
    else some (⟨v.depth - 1, v.index / 2, .children⟩, v.index % 2 != 0)

/-- Every parent precedes its child in the top-down rank. -/
theorem Position.parent_rank_lt (h : ℕ) (inj : ℕ → Bool) (v u : Position) (right : Bool)
    (hp : v.parent h inj = some (u, right)) : u.rank < v.rank := by
  sorry

/-- Ancestors in nearest-parent-first order, recording the extractor calls needed for a target. -/
@[expose]
def Position.ancestors (h : ℕ) (inj : ℕ → Bool) (v : Position) : List Position :=
  match hp : v.parent h inj with
  | none => []
  | some (u, _) => u :: u.ancestors h inj
termination_by v.rank
decreasing_by sorry

/-- Read a compression pair, using a fixed pair of default digests for payload predictions. -/
@[expose]
def opChildren (d₀ : Digest) : Op Payload Digest → Digest × Digest
  | .inl _ => (d₀, d₀)
  | .inr ab => ab

/-- Read a payload; a compression-shaped prediction supplies the fixed default payload. -/
@[expose]
def opPayload (p₀ : Payload) : Op Payload Digest → Payload
  | .inl p => p
  | .inr _ => p₀

/-- The digest reached after the bottom `l` siblings, with injection depths shifted for `climb`. -/
@[expose]
def Opening.digest (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (K h l : ℕ) (o : Opening Payload Digest) : Digest :=
  climb hash compress (fun d ↦ o.pays (d + (K - h - l))) o.index (hash o.payload)
    (o.path.take l)

/-- The ordered pair compressed at an inner position of an opening. -/
@[expose]
def Opening.childPair (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (K h d : ℕ) (o : Opening Payload Digest) : Digest × Digest :=
  let l := K - d - 1
  let x := o.digest hash compress K h l
  let s := o.path.getD l (hash p₀)
  if (o.index >>> l) % 2 = 0 then (x, s) else (s, x)

/-- Operations an opening computes at a path position; absent injected payloads reveal none. -/
@[expose]
def Opening.ops (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (K h : ℕ) (v : Position) (o : Opening Payload Digest) :
    List (Op Payload Digest) :=
  if o.index >>> (K - v.depth) = v.index then
    match v.stage with
    | .leaf => [.inl o.payload]
    | .children => [.inr (o.childPair hash compress p₀ K h v.depth)]
    | .payload => (o.pays (v.depth - h)).toList.map Sum.inl
    | .injection => (o.pays (v.depth - h)).toList.map fun p ↦
        .inr (answer hash compress (.inr (o.childPair hash compress p₀ K h v.depth)), hash p)
  else []

/-- All operations computed at a position by the adversary's verifying openings. -/
@[expose]
noncomputable def revealedOps (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool) (A : MerkleAdversary Coins Payload Digest)
    (v : Position) (c : Coins) : List (Op Payload Digest) := by
  classical
  exact ((A c).2.filter (fun o ↦ decide (o.Verifies hash compress K h inj (A c).1))).flatMap
    (Opening.ops hash compress p₀ K h v)

/-- The node adversary targets a cap digest or a child of its parent's extracted operation and
reveals all verifying-opening operations here. It runs `A` and the extractors of this position's
ancestors, at most `2 * (K - h) + 1` extractors along a path, with the same coins throughout. -/
@[expose]
noncomputable def derivedAdversary (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (v : Position) : NodeAdversary Coins Payload Digest :=
  fun c ↦
    let target := match hp : v.parent h inj with
      | none => (A c).1.getD v.index (hash p₀)
      | some (u, right) =>
        let ab := opChildren (hash p₀) (X (derivedAdversary hash compress p₀ K h inj A X u) c)
        if right then ab.2 else ab.1
    (target, revealedOps hash compress p₀ K h inj A v c)
termination_by v.rank
decreasing_by sorry

/-- The assigned extractor's operation at a position. -/
@[expose]
noncomputable def extractedOp (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool) (A : MerkleAdversary Coins Payload Digest)
    (X : ExtractorMap Coins Payload Digest) (v : Position) (c : Coins) : Op Payload Digest :=
  X (derivedAdversary hash compress p₀ K h inj A X v) c

/-- Extracted leaf payloads, with the fixed default for predictions of the wrong shape. -/
@[expose]
noncomputable def extractedLeaves (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) (i : ℕ) : Payload :=
  opPayload p₀ (extractedOp hash compress p₀ K h inj A X ⟨K, i, .leaf⟩ c)

/-- Extracted injected payloads at the scheduled inner depths from the cap downwards. -/
@[expose]
noncomputable def extractedInjections (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) (d : ℕ) : Option (ℕ → Payload) :=
  if h ≤ d ∧ d < K ∧ inj d = true then
    some fun i ↦ opPayload p₀ (extractedOp hash compress p₀ K h inj A X ⟨d, i, .payload⟩ c)
  else none

/-- An opening disagrees with the extracted leaf or an injected payload at a depth it opens. -/
@[expose]
def Opening.Disagrees (K h : ℕ) (leaves : ℕ → Payload) (injections : ℕ → Option (ℕ → Payload))
    (o : Opening Payload Digest) : Prop :=
  o.payload ≠ leaves o.index ∨
    ∃ d < K - h, o.pays d ≠ MixedMerkleTree.pays K injections o.index (K - h) d

section Statements

variable (hash : Payload → Digest) (compress : Digest → Digest → Digest) (p₀ : Payload)
  (K h : ℕ) (inj : ℕ → Bool) (A : MerkleAdversary Coins Payload Digest)
  (X : ExtractorMap Coins Payload Digest)

/-- Finite position enumeration agrees with the structural validity predicate. -/
theorem mem_positions (v : Position) : v ∈ positions K h inj ↔ v.Valid K h inj := by
  sorry

/-- A non-cap position's parent is another enumerated position. -/
theorem parent_mem_positions (v u : Position) (right : Bool) (hv : v ∈ positions K h inj)
    (hp : v.parent h inj = some (u, right)) : u ∈ positions K h inj := by
  sorry

/-- The ancestor extractors and the position's own extractor fit the structural path budget. -/
theorem ancestors_length_le (v : Position) (hv : v ∈ positions K h inj) :
    (v.ancestors h inj).length + 1 ≤ 2 * (K - h) + 1 := by
  sorry

/-- Two distinct valid revealed preimages force failure of every same-coins extractor. -/
theorem nodeBad_of_collision (f : Op Payload Digest → Digest)
    (B : NodeAdversary Coins Payload Digest) (E : Coins → Op Payload Digest) (c : Coins)
    (q q' : Op Payload Digest) (hq : q ∈ (B c).2) (hq' : q' ∈ (B c).2)
    (hy : f q = (B c).1) (hy' : f q' = (B c).1) (hne : q ≠ q') : NodeBad f B E c := by
  sorry

/-- Honest openings satisfy the cap verifier with the honest global injection schedule. -/
theorem honest_verifies (leaves : ℕ → Payload) (injections : ℕ → Option (ℕ → Payload))
    (hh : h ≤ K) (i : ℕ) (hi : i < 2 ^ K) :
    Opening.Verifies hash compress K h (fun d ↦ (injections d).isSome)
      (cap hash compress K leaves injections h)
      ⟨i, leaves i, pays K injections i (K - h),
        siblings hash compress K leaves injections i (K - h)⟩ := by
  sorry

/-- Every operation of a verifying opening is revealed by its derived node adversary. -/
theorem opening_op_mem (c : Coins) (o : Opening Payload Digest) (ho : o ∈ (A c).2)
    (hv : o.Verifies hash compress K h inj (A c).1) (v : Position) (q : Op Payload Digest)
    (hq : q ∈ o.ops hash compress p₀ K h v) :
    q ∈ (derivedAdversary hash compress p₀ K h inj A X v c).2 := by
  sorry

/-- Absent node failures, a verifying opening's operation equals the predicted operation here,
and its output equals the derived target; this is the top-down induction invariant. -/
theorem opening_op_eq_extracted (c : Coins)
    (hgood : ∀ v ∈ positions K h inj,
      ¬ NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) c)
    (o : Opening Payload Digest) (ho : o ∈ (A c).2)
    (hver : o.Verifies hash compress K h inj (A c).1) (v : Position)
    (hv : v ∈ positions K h inj) (q : Op Payload Digest)
    (hq : q ∈ o.ops hash compress p₀ K h v) :
    q = extractedOp hash compress p₀ K h inj A X v c ∧
      answer hash compress q = (derivedAdversary hash compress p₀ K h inj A X v c).1 := by
  sorry

/-- Every verifying opening that disagrees with extraction witnesses a failure at a position. -/
theorem disagreement_implies_nodeBad (c : Coins) (o : Opening Payload Digest)
    (ho : o ∈ (A c).2) (hv : o.Verifies hash compress K h inj (A c).1)
    (hd : o.Disagrees K h (extractedLeaves hash compress p₀ K h inj A X c)
      (extractedInjections hash compress p₀ K h inj A X c)) :
    ∃ v ∈ positions K h inj,
      NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) c := by
  sorry

/-- Standard-model knowledge reduction for a mixed Merkle cap, for every extractor assignment. -/
theorem knowledge_bound [SampleableType Coins] (hh : h ≤ K) :
    Pr{let c ← $ᵗ Coins}[∃ o ∈ (A c).2, o.Verifies hash compress K h inj (A c).1 ∧
      o.Disagrees K h (extractedLeaves hash compress p₀ K h inj A X c)
        (extractedInjections hash compress p₀ K h inj A X c)] ≤
    ∑ v ∈ positions K h inj,
      nodeFail (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) := by
  sorry

end Statements

end MixedMerkleTree.Knowledge
