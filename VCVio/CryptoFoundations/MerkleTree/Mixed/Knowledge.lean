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
  rcases v with ⟨d, i, s⟩
  cases s <;> simp only [parent] at hp
  all_goals
    (try split_ifs at hp) <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
  all_goals
    obtain ⟨rfl, rfl⟩ := hp
    simp only [rank]
    omega

/-- Ancestors in nearest-parent-first order, recording the extractor calls needed for a target. -/
@[expose]
def Position.ancestors (h : ℕ) (inj : ℕ → Bool) (v : Position) : List Position :=
  match _hp : v.parent h inj with
  | none => []
  | some (u, _) => u :: u.ancestors h inj
termination_by v.rank
decreasing_by exact Position.parent_rank_lt h inj _ _ _ _hp

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
    let target := match _hp : v.parent h inj with
      | none => (A c).1.getD v.index (hash p₀)
      | some (u, right) =>
        let ab := opChildren (hash p₀) (X (derivedAdversary hash compress p₀ K h inj A X u) c)
        if right then ab.2 else ab.1
    (target, revealedOps hash compress p₀ K h inj A v c)
termination_by v.rank
decreasing_by exact Position.parent_rank_lt h inj _ _ _ _hp

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

/-- The canonical operation computed by an opening at a position on its path. -/
@[expose]
def Opening.opAt (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (K h : ℕ) (v : Position) (o : Opening Payload Digest) : Op Payload Digest :=
  match v.stage with
  | .leaf => .inl o.payload
  | .children => .inr (o.childPair hash compress p₀ K h v.depth)
  | .payload => .inl ((o.pays (v.depth - h)).getD p₀)
  | .injection => .inr
      (answer hash compress (.inr (o.childPair hash compress p₀ K h v.depth)),
        hash ((o.pays (v.depth - h)).getD p₀))

/-- A scheduled inner depth of a verifying opening supplies a payload. -/
theorem Opening.Verifies.pays_some (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (K h : ℕ) (inj : ℕ → Bool)
    (cap : List Digest) (o : Opening Payload Digest)
    (hv : o.Verifies hash compress K h inj cap) (d : ℕ)
    (hd : h ≤ d) (hdK : d < K) (hinj : inj d = true) :
    ∃ p, o.pays (d - h) = some p := by
  have hs := hv.2.2.2.2.1 (d - h) (by omega)
  rw [Nat.add_sub_of_le hd, hinj] at hs
  exact Option.isSome_iff_exists.mp hs

/-- Every node index along a verifying opening is in the range at its global depth. -/
theorem Opening.Verifies.index_lt (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (K h : ℕ) (inj : ℕ → Bool)
    (cap : List Digest) (o : Opening Payload Digest)
    (hv : o.Verifies hash compress K h inj cap) (d : ℕ) (hd : d ≤ K) :
    o.index >>> (K - d) < 2 ^ d := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),
    ← Nat.pow_add, Nat.add_sub_cancel' hd]
  exact hv.2.2.1

/-- A valid position on a verifying opening's path reveals exactly its canonical operation. -/
theorem Opening.ops_eq_singleton (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (cap : List Digest) (o : Opening Payload Digest)
    (hver : o.Verifies hash compress K h inj cap) (v : Position)
    (hv : v.Valid K h inj) (hi : o.index >>> (K - v.depth) = v.index) :
    o.ops hash compress p₀ K h v = [o.opAt hash compress p₀ K h v] := by
  rcases v with ⟨d, i, s⟩
  cases s <;> simp only [Position.Valid] at hv
  all_goals simp only [ops, opAt, hi, ↓reduceIte]
  all_goals
    obtain ⟨p, hp⟩ := hver.pays_some hash compress K h inj cap o d hv.1 hv.2.2.2.1 hv.2.2.2.2
    simp only [hp, Option.toList_some, List.map_cons, List.map_nil, Option.getD_some]

/-- A partial climb advances by one sibling and the injection at the resulting depth. -/
theorem Opening.digest_succ (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h l : ℕ)
    (o : Opening Payload Digest) (hlen : o.path.length = K - h) (hl : l < K - h) :
    o.digest hash compress K h (l + 1) =
      inject hash compress (o.pays (K - h - (l + 1)))
        (pairUp compress (o.index >>> l) (o.digest hash compress K h l)
          (o.path.getD l (hash p₀))) := by
  have hlt : l < o.path.length := by omega
  unfold digest
  rw [List.take_succ_eq_append_getElem hlt, climb_append]
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt),
    List.length_singleton, climb_cons, climb_nil, List.length_nil, Nat.zero_add]
  rw [List.getElem_eq_getD (hash p₀)]
  congr 2
  apply climb_congr
  intro d _
  congr 1
  omega

/-- A node's canonical operation answers the digest of the opening at its global depth. -/
theorem Opening.answer_nodePosition (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (cap : List Digest) (o : Opening Payload Digest)
    (hver : o.Verifies hash compress K h inj cap) (d i : ℕ)
    (hd : h ≤ d) (hdK : d ≤ K) :
    answer hash compress (o.opAt hash compress p₀ K h (nodePosition K inj d i)) =
      o.digest hash compress K h (K - d) := by
  by_cases he : d = K
  · subst d
    simp only [nodePosition, ↓reduceIte, opAt, answer, digest, Nat.sub_self,
      List.take_zero, climb_nil]
  · have hstep := o.digest_succ hash compress p₀ K h (K - d - 1) hver.2.2.2.1 (by omega)
    have heq : K - d - 1 + 1 = K - d := by omega
    rw [heq] at hstep
    rw [hstep]
    have hdepth : K - h - (K - d) = d - h := by omega
    rw [hdepth]
    have hpair : answer hash compress (.inr (o.childPair hash compress p₀ K h d)) =
        pairUp compress (o.index >>> (K - d - 1))
          (o.digest hash compress K h (K - d - 1))
          (o.path.getD (K - d - 1) (hash p₀)) := by
      simp only [childPair, pairUp, answer]
      split <;> rfl
    cases hi : inj d with
    | false =>
      have hs := hver.2.2.2.2.1 (d - h) (by omega)
      rw [Nat.add_sub_of_le hd, hi] at hs
      have hp : o.pays (d - h) = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp hs)
      simp only [nodePosition, he, ↓reduceIte, hi, Bool.false_eq_true, opAt, hp, inject]
      exact hpair
    | true =>
      obtain ⟨p, hp⟩ := hver.pays_some hash compress K h inj cap o d hd (by omega) hi
      simp only [nodePosition, he, ↓reduceIte, hi, opAt, hp, Option.getD_some, inject, answer]
      exact congrArg (fun z ↦ compress z (hash p)) hpair

/-- A parent of a path position lies on the same opening's path. -/
theorem Opening.parent_path (K h : ℕ) (inj : ℕ → Bool) (o : Opening Payload Digest)
    (v u : Position) (right : Bool) (hv : v.Valid K h inj)
    (hi : o.index >>> (K - v.depth) = v.index)
    (hp : v.parent h inj = some (u, right)) :
    o.index >>> (K - u.depth) = u.index := by
  rcases v with ⟨d, i, s⟩
  obtain ⟨_, hdK, _, _⟩ := hv
  change d ≤ K at hdK
  cases s <;> simp only [Position.parent] at hp
  all_goals
    (try split_ifs at hp) <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp
  all_goals
    obtain ⟨rfl, rfl⟩ := hp
    first
    | exact hi
    | change o.index >>> (K - (d - 1)) = i / 2
      rw [show K - (d - 1) = K - d + 1 by omega, Nat.shiftRight_succ, hi]

/-- Selecting the path side of a parent's child compression gives the partial-climb digest. -/
theorem Opening.childPair_select (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h d i : ℕ)
    (o : Opening Payload Digest) (hd : 0 < d) (hdK : d ≤ K)
    (hi : o.index >>> (K - d) = i) :
    (if i % 2 != 0 then (o.childPair hash compress p₀ K h (d - 1)).2
      else (o.childPair hash compress p₀ K h (d - 1)).1) =
      o.digest hash compress K h (K - d) := by
  unfold childPair
  rw [show K - (d - 1) - 1 = K - d by omega]
  dsimp only
  rw [hi]
  by_cases he : i % 2 = 0 <;> simp [he]

/-- The canonical operation of a path position answers the corresponding input of its parent. -/
theorem Opening.parent_edge (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (cap : List Digest) (o : Opening Payload Digest)
    (hver : o.Verifies hash compress K h inj cap) (v u : Position) (right : Bool)
    (hv : v.Valid K h inj) (hi : o.index >>> (K - v.depth) = v.index)
    (hp : v.parent h inj = some (u, right)) :
    answer hash compress (o.opAt hash compress p₀ K h v) =
      (if right then (opChildren (hash p₀) (o.opAt hash compress p₀ K h u)).2
        else (opChildren (hash p₀) (o.opAt hash compress p₀ K h u)).1) := by
  have hnode : ∀ d i, h ≤ d → d ≤ K →
      answer hash compress (o.opAt hash compress p₀ K h (nodePosition K inj d i)) =
        o.digest hash compress K h (K - d) :=
    fun d i hd hdK ↦ o.answer_nodePosition hash compress p₀ K h inj cap hver d i hd hdK
  rcases v with ⟨d, i, s⟩
  change h ≤ d ∧ d ≤ K ∧ i < 2 ^ d ∧ _ at hv
  obtain ⟨hhd, hdK, _, hs⟩ := hv
  cases s <;> simp only [Position.parent] at hp
  all_goals (try dsimp only at hs hi)
  all_goals
    (try split_ifs at hp) <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp
  all_goals
    obtain ⟨rfl, rfl⟩ := hp
    first
    | rfl
    | have hn : Position.mk d i .leaf = nodePosition K inj d i := by
        simp only [nodePosition, hs, ↓reduceIte]
      rw [hn, hnode d i hhd hdK]
      exact (o.childPair_select hash compress p₀ K h d i (by omega) hdK hi).symm
    | have hn : Position.mk d i .children = nodePosition K inj d i := by
        simp only [nodePosition, ite_eq_right (show d ≠ K by omega), ite_eq_right ‹¬inj d = true›]
      rw [hn, hnode d i hhd hdK]
      exact (o.childPair_select hash compress p₀ K h d i (by omega) hdK hi).symm
    | have hn : Position.mk d i .injection = nodePosition K inj d i := by
        simp only [nodePosition, ite_eq_right (show d ≠ K by omega), ite_eq_left hs.2]
      rw [hn, hnode d i hhd hdK]
      exact (o.childPair_select hash compress p₀ K h d i (by omega) hdK hi).symm

/-- A position without a parent is a final node operation at cap depth. -/
theorem Position.eq_nodePosition_of_parent_none (K h : ℕ) (inj : ℕ → Bool)
    (v : Position) (hv : v.Valid K h inj) (hp : v.parent h inj = none) :
    v.depth = h ∧ v = nodePosition K inj h v.index := by
  rcases v with ⟨d, i, s⟩
  change h ≤ d ∧ d ≤ K ∧ i < 2 ^ d ∧ _ at hv
  obtain ⟨hhd, hdK, _, hs⟩ := hv
  cases s <;> simp only [Position.parent] at hp
  all_goals dsimp only at hs
  all_goals (try split_ifs at hp); cases hp
  all_goals
    have he : d = h := by omega
    refine ⟨he, ?_⟩
    rw [← he]
    first
    | have hs' : d = K := hs
      simp only [nodePosition, hs', ↓reduceIte]
    | have hs' : d < K := hs
      simp only [nodePosition, ite_eq_right (Nat.ne_of_lt hs'), ite_eq_right ‹¬inj d = true›]
    | have hs' : d < K ∧ inj d = true := hs
      simp only [nodePosition, ite_eq_right (Nat.ne_of_lt hs'.1), ite_eq_left hs'.2]

/-- The operation at a cap position answers its indexed cap digest. -/
theorem Opening.cap_answer (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (cap : List Digest) (o : Opening Payload Digest)
    (hver : o.Verifies hash compress K h inj cap) (v : Position)
    (hv : v.Valid K h inj) (hi : o.index >>> (K - v.depth) = v.index)
    (hp : v.parent h inj = none) :
    answer hash compress (o.opAt hash compress p₀ K h v) = cap.getD v.index (hash p₀) := by
  obtain ⟨hd, he⟩ := v.eq_nodePosition_of_parent_none K h inj hv hp
  have hval := o.answer_nodePosition hash compress p₀ K h inj cap hver h v.index
    (Nat.le_refl _) hver.1
  rw [← he] at hval
  rw [hd] at hi
  rw [hval]
  rw [List.getD_eq_getElem?_getD, ← hi, hver.2.2.2.2.2, Option.getD_some]
  simp only [digest, Nat.sub_self, Nat.add_zero, ← hver.2.2.2.1, List.take_length]

section Statements

variable (hash : Payload → Digest) (compress : Digest → Digest → Digest) (p₀ : Payload)
  (K h : ℕ) (inj : ℕ → Bool) (A : MerkleAdversary Coins Payload Digest)
  (X : ExtractorMap Coins Payload Digest)

/-- Finite position enumeration agrees with the structural validity predicate. -/
theorem mem_positions (v : Position) : v ∈ positions K h inj ↔ v.Valid K h inj := by
  classical
  rw [positions, Finset.mem_filter]
  refine ⟨And.right, fun hv ↦ ⟨?_, hv⟩⟩
  rcases v with ⟨d, i, s⟩
  change h ≤ d ∧ d ≤ K ∧ i < 2 ^ d ∧ _ at hv
  obtain ⟨_, hd, hi, _⟩ := hv
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  refine ⟨d, by omega, i, hi, s, ?_, rfl⟩
  cases s <;> simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

/-- A non-cap position's parent is another enumerated position. -/
theorem parent_mem_positions (v u : Position) (right : Bool) (hv : v ∈ positions K h inj)
    (hp : v.parent h inj = some (u, right)) : u ∈ positions K h inj := by
  rw [mem_positions] at hv ⊢
  rcases v with ⟨d, i, s⟩
  change h ≤ d ∧ d ≤ K ∧ i < 2 ^ d ∧ _ at hv
  obtain ⟨hhd, hdK, hi, hs⟩ := hv
  cases s <;> simp only [Position.parent] at hp
  all_goals (try dsimp only at hs hi)
  all_goals
    (try split_ifs at hp) <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
  all_goals
    obtain ⟨rfl, rfl⟩ := hp
    simp only [Position.Valid]
    first
    | exact ⟨hhd, hdK, hi, hs.1, hs.2⟩
    | exact ⟨hhd, hdK, hi, hs, ‹inj d = true›⟩
    | have hd : d - 1 + 1 = d := by omega
      have hi' : i / 2 < 2 ^ (d - 1) := by
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2
        rw [← Nat.pow_succ]
        change i < 2 ^ (d - 1 + 1)
        rw [hd]
        exact hi
      exact ⟨by omega, by omega, hi', by omega⟩

/-- The ancestor extractors and the position's own extractor fit the structural path budget. -/
theorem ancestors_length_le (v : Position) (hv : v ∈ positions K h inj) :
    (v.ancestors h inj).length + 1 ≤ 2 * (K - h) + 1 := by
  have hlength : ∀ v ∈ positions K h inj,
      (v.ancestors h inj).length + 2 * h ≤ v.rank := by
    intro v
    induction v using (measure Position.rank).wf.induction with
    | h v ih =>
      intro hv
      have hdepth := ((mem_positions K h inj v).1 hv).1
      rw [Position.ancestors]
      split
      · rcases v with ⟨d, i, s⟩
        change h ≤ d at hdepth
        cases s <;> simp only [List.length_nil, Position.rank] <;> omega
      · rename_i u right hp
        have hu := parent_mem_positions K h inj v u right hv hp
        have hr := Position.parent_rank_lt h inj v u right hp
        have hi := ih u hr hu
        simp only [List.length_cons]
        omega
  have hl := hlength v hv
  have hv' := (mem_positions K h inj v).1 hv
  rcases v with ⟨d, i, s⟩
  change h ≤ d ∧ d ≤ K ∧ i < 2 ^ d ∧ _ at hv'
  cases s <;> simp only [Position.rank] at hl <;> simp only at hv' <;> omega

/-- Two distinct valid revealed preimages force failure of every same-coins extractor. -/
theorem nodeBad_of_collision (f : Op Payload Digest → Digest)
    (B : NodeAdversary Coins Payload Digest) (E : Coins → Op Payload Digest) (c : Coins)
    (q q' : Op Payload Digest) (hq : q ∈ (B c).2) (hq' : q' ∈ (B c).2)
    (hy : f q = (B c).1) (hy' : f q' = (B c).1) (hne : q ≠ q') : NodeBad f B E c := by
  classical
  by_cases he : q = E c
  · exact ⟨q', hq', hy', fun he' ↦ hne (he.trans he'.symm)⟩
  · exact ⟨q, hq, hy, he⟩

/-- Honest openings satisfy the cap verifier with the honest global injection schedule. -/
theorem honest_verifies (leaves : ℕ → Payload) (injections : ℕ → Option (ℕ → Payload))
    (hh : h ≤ K) (i : ℕ) (hi : i < 2 ^ K) :
    Opening.Verifies hash compress K h (fun d ↦ (injections d).isSome)
      (cap hash compress K leaves injections h)
      ⟨i, leaves i, pays K injections i (K - h),
        siblings hash compress K leaves injections i (K - h)⟩ := by
  refine ⟨hh, ?_, hi, ?_, ?_, ?_⟩
  · simp only [cap, List.length_map, List.length_range]
  · simp only [siblings, List.length_map, List.length_range]
  · intro d hd
    simp only [pays, Option.isSome_map]
    congr 2
    omega
  · have hidx : i >>> (K - h) < 2 ^ h := by
      rw [Nat.shiftRight_eq_div_pow,
        Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
        Nat.add_sub_cancel' hh]
      exact hi
    have hc := climb_cap hash compress K leaves injections h i hh hi
    rw [hc]
    simp only [cap, List.getElem?_map, List.getElem?_range hidx, Option.map_some,
      List.getD_eq_getElem?_getD, Option.getD_some]

/-- Every operation of a verifying opening is revealed by its derived node adversary. -/
theorem opening_op_mem (c : Coins) (o : Opening Payload Digest) (ho : o ∈ (A c).2)
    (hv : o.Verifies hash compress K h inj (A c).1) (v : Position) (q : Op Payload Digest)
    (hq : q ∈ o.ops hash compress p₀ K h v) :
    q ∈ (derivedAdversary hash compress p₀ K h inj A X v c).2 := by
  rw [derivedAdversary]
  simp only [revealedOps, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  exact ⟨o, ⟨ho, hv⟩, hq⟩

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
  classical
  induction v using (measure Position.rank).wf.induction generalizing q with
  | h v ih =>
    have hvalid := (mem_positions K h inj v).1 hv
    have hi : o.index >>> (K - v.depth) = v.index := by
      by_contra hn
      simp only [Opening.ops, hn, ↓reduceIte, List.not_mem_nil] at hq
    rw [o.ops_eq_singleton hash compress p₀ K h inj (A c).1 hver v hvalid hi,
      List.mem_singleton] at hq
    subst q
    have htarget : answer hash compress (o.opAt hash compress p₀ K h v) =
        (derivedAdversary hash compress p₀ K h inj A X v c).1 := by
      rw [derivedAdversary]
      dsimp only
      cases hp : v.parent h inj with
      | none =>
        exact o.cap_answer hash compress p₀ K h inj (A c).1 hver v hvalid hi hp
      | some ur =>
        obtain ⟨u, right⟩ := ur
        dsimp only
        have hu := parent_mem_positions K h inj v u right hv hp
        have huvalid := (mem_positions K h inj u).1 hu
        have hui := o.parent_path K h inj v u right hvalid hi hp
        have hqu : o.opAt hash compress p₀ K h u ∈ o.ops hash compress p₀ K h u := by
          rw [o.ops_eq_singleton hash compress p₀ K h inj (A c).1 hver u huvalid hui]
          exact List.mem_singleton_self _
        have hpred := (ih u (v.parent_rank_lt h inj u right hp) hu _ hqu).1
        change o.opAt hash compress p₀ K h u =
          X (derivedAdversary hash compress p₀ K h inj A X u) c at hpred
        rw [← hpred]
        exact o.parent_edge hash compress p₀ K h inj (A c).1 hver v u right hvalid hi hp
    refine ⟨?_, htarget⟩
    by_contra hne
    apply hgood v hv
    exact ⟨o.opAt hash compress p₀ K h v,
      opening_op_mem hash compress p₀ K h inj A X c o ho hver v _
        (by rw [o.ops_eq_singleton hash compress p₀ K h inj (A c).1 hver v hvalid hi]
            exact List.mem_singleton_self _), htarget, hne⟩

/-- Without node failures, a verifying opening's leaf is the extracted leaf. -/
theorem opening_leaf_eq (c : Coins)
    (hgood : ∀ v ∈ positions K h inj,
      ¬ NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) c)
    (o : Opening Payload Digest) (ho : o ∈ (A c).2)
    (hv : o.Verifies hash compress K h inj (A c).1) :
    o.payload = extractedLeaves hash compress p₀ K h inj A X c o.index := by
  have hpos : (Position.mk K o.index .leaf).Valid K h inj :=
    ⟨hv.1, Nat.le_refl _, hv.2.2.1, rfl⟩
  have he := (opening_op_eq_extracted hash compress p₀ K h inj A X c hgood o ho hv
    ⟨K, o.index, .leaf⟩ ((mem_positions K h inj _).2 hpos) (.inl o.payload)
    (by simp only [Opening.ops, Nat.sub_self, Nat.shiftRight_zero, ↓reduceIte,
          List.mem_singleton])).1
  exact congrArg (opPayload p₀) he

/-- Without node failures, a verifying opening's injections are the extracted injections. -/
theorem opening_pays_eq (c : Coins)
    (hgood : ∀ v ∈ positions K h inj,
      ¬ NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) c)
    (o : Opening Payload Digest) (ho : o ∈ (A c).2)
    (hv : o.Verifies hash compress K h inj (A c).1) (d : ℕ) (hd : d < K - h) :
    o.pays d = pays K (extractedInjections hash compress p₀ K h inj A X c)
      o.index (K - h) d := by
  have hdepth : K - (K - h - d) = h + d := by omega
  have hidx : K - h - d = K - (h + d) := by omega
  have hlt : h + d < K := by omega
  have hs := hv.2.2.2.2.1 d hd
  unfold pays
  rw [hdepth, hidx]
  cases hp : o.pays d with
  | none =>
    have hinj : inj (h + d) = false := by
      rw [hp, Option.isSome_none] at hs
      exact hs.symm
    simp only [extractedInjections, hinj, Bool.false_eq_true, and_false, ↓reduceIte,
      Option.map_none]
  | some p =>
    have hinj : inj (h + d) = true := by
      rw [hp, Option.isSome_some] at hs
      exact hs.symm
    let v : Position := ⟨h + d, o.index >>> (K - (h + d)), .payload⟩
    have hpos : v.Valid K h inj := by
      change h ≤ h + d ∧ h + d ≤ K ∧
        o.index >>> (K - (h + d)) < 2 ^ (h + d) ∧ h + d < K ∧ inj (h + d) = true
      exact ⟨Nat.le_add_right _ _, Nat.le_of_lt hlt,
        hv.index_lt hash compress K h inj (A c).1 o (h + d) (Nat.le_of_lt hlt), hlt, hinj⟩
    have hops := o.ops_eq_singleton hash compress p₀ K h inj (A c).1 hv v hpos rfl
    have hmem : .inl p ∈ o.ops hash compress p₀ K h v := by
      rw [hops]
      simp only [Opening.opAt, v, Nat.add_sub_cancel_left, hp, Option.getD_some,
        List.mem_singleton]
    have he := (opening_op_eq_extracted hash compress p₀ K h inj A X c hgood o ho hv v
      ((mem_positions K h inj v).2 hpos) (.inl p) hmem).1
    have hpay := congrArg (opPayload p₀) he
    simp only [extractedInjections, show h ≤ h + d from Nat.le_add_right _ _, hlt, hinj,
      and_self, ↓reduceIte, Option.map_some]
    exact congrArg some hpay

/-- Every verifying opening that disagrees with extraction witnesses a failure at a position. -/
theorem disagreement_implies_nodeBad (c : Coins) (o : Opening Payload Digest)
    (ho : o ∈ (A c).2) (hv : o.Verifies hash compress K h inj (A c).1)
    (hd : o.Disagrees K h (extractedLeaves hash compress p₀ K h inj A X c)
      (extractedInjections hash compress p₀ K h inj A X c)) :
    ∃ v ∈ positions K h inj,
      NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) c := by
  classical
  by_contra hn
  have hgood : ∀ v ∈ positions K h inj,
      ¬ NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) c := by
    intro v hv hbad
    exact hn ⟨v, hv, hbad⟩
  rcases hd with hleaf | ⟨d, hd, hpays⟩
  · exact hleaf (opening_leaf_eq hash compress p₀ K h inj A X c hgood o ho hv)
  · exact hpays (opening_pays_eq hash compress p₀ K h inj A X c hgood o ho hv d hd)

/-- Standard-model knowledge reduction for a mixed Merkle cap, for every extractor assignment. -/
theorem knowledge_bound [SampleableType Coins] :
    Pr{let c ← $ᵗ Coins}[∃ o ∈ (A c).2, o.Verifies hash compress K h inj (A c).1 ∧
      o.Disagrees K h (extractedLeaves hash compress p₀ K h inj A X c)
        (extractedInjections hash compress p₀ K h inj A X c)] ≤
    ∑ v ∈ positions K h inj,
      nodeFail (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) := by
  refine (prEvent_mono ($ᵗ Coins) _
    (fun c ↦ ∃ v ∈ positions K h inj,
      NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) c) ?_).trans ?_
  · intro c ⟨o, ho, hv, hd⟩
    exact disagreement_implies_nodeBad hash compress p₀ K h inj A X c o ho hv hd
  · exact prEvent_exists_finset_le (positions K h inj) ($ᵗ Coins) _

end Statements

end MixedMerkleTree.Knowledge
