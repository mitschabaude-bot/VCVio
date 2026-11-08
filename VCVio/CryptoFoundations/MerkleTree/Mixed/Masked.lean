/-
Copyright (c) 2026 Gregor Mitscha-Baude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Mixed.Knowledge

/-! # Hash-consistent partial extraction for mixed Merkle caps -/

public section

namespace MixedMerkleTree.Knowledge

open OracleComp
open scoped ENNReal

variable {Payload Digest Coins : Type} [DecidableEq Digest]

/-- A position accepts only the operation shape assigned to its stage. -/
@[expose] def Position.opShape (v : Position) (op : Op Payload Digest) : Bool :=
  match v.stage, op with
  | .leaf, .inl _ | .payload, .inl _ | .children, .inr _ | .injection, .inr _ => true
  | _, _ => false

/-- All path operations for a target, including every injected payload hash along its ancestry. -/
@[expose] def extractionPathPositions (h : ℕ) (inj : ℕ → Bool) (v : Position) : List Position :=
  let path := v :: v.ancestors h inj
  path ++ path.filterMap (fun u =>
    if u.stage = .injection then some ⟨u.depth, u.index, .payload⟩ else none)

/-- All operations needed by a leaf path, including the hashes of its injected payloads. -/
@[expose] def maskPositions (K h : ℕ) (inj : ℕ → Bool) (i : ℕ) : List Position :=
  extractionPathPositions h inj ⟨K, i, .leaf⟩

/-- A target's ancestor list is closed under taking a parent. -/
theorem Position.parent_mem_path (h : ℕ) (inj : ℕ → Bool) (v u w : Position)
    (hu : u ∈ v :: v.ancestors h inj) (right : Bool)
    (hp : u.parent h inj = some (w, right)) : w ∈ v :: v.ancestors h inj := by
  induction v using (measure Position.rank).wf.induction with
  | h v ih =>
      rcases List.mem_cons.mp hu with rfl | hu
      · rw [Position.ancestors, hp]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [Position.ancestors] at hu
        split at hu
        · cases hu
        · rename_i parent rightParent edge
          have hw := ih parent (v.parent_rank_lt h inj _ _ edge) hu
          rw [Position.ancestors, edge]
          exact List.mem_cons_of_mem _ hw

omit [DecidableEq Digest] in
/-- Every ancestor of a valid opening position remains valid and on the same opening. -/
theorem Opening.path_valid (K h : ℕ) (inj : ℕ → Bool) (o : Opening Payload Digest)
    (v : Position) (hv : v.Valid K h inj)
    (hi : o.index >>> (K - v.depth) = v.index) (u : Position)
    (hu : u ∈ v :: v.ancestors h inj) :
    u.Valid K h inj ∧ o.index >>> (K - u.depth) = u.index := by
  induction v using (measure Position.rank).wf.induction with
  | h v ih =>
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨hv, hi⟩
      · rw [Position.ancestors] at hu
        split at hu
        · cases hu
        · rename_i parent rightParent edge
          have hp := parent_mem_positions K h inj v parent rightParent
            ((mem_positions K h inj v).mpr hv) edge
          exact ih parent (v.parent_rank_lt h inj _ _ edge)
            ((mem_positions K h inj _).mp hp)
            (o.parent_path K h inj v parent rightParent hv hi edge) hu

omit [DecidableEq Digest] in
/-- Every authenticated path position is valid and lies on the target's opening. -/
theorem Opening.extractionPath_valid (K h : ℕ) (inj : ℕ → Bool)
    (o : Opening Payload Digest) (v : Position) (hv : v.Valid K h inj)
    (hi : o.index >>> (K - v.depth) = v.index) (u : Position)
    (hu : u ∈ extractionPathPositions h inj v) :
    u.Valid K h inj ∧ o.index >>> (K - u.depth) = u.index := by
  simp only [extractionPathPositions, List.mem_append, List.mem_filterMap] at hu
  rcases hu with hu | ⟨w, hw, heq⟩
  · exact o.path_valid K h inj v hv hi u hu
  · split at heq
    · rename_i hs
      cases Option.some.inj heq
      obtain ⟨hwv, hwi⟩ := o.path_valid K h inj v hv hi w hw
      exact ⟨⟨hwv.1, hwv.2.1, hwv.2.2.1,
        by simpa only [hs, Position.Valid] using hwv.2.2.2⟩, hwi⟩
    · cases heq

/-- Authentication paths are closed under taking a parent. -/
theorem extractionPath_parent_mem (h : ℕ) (inj : ℕ → Bool) (v u w : Position)
    (hu : u ∈ extractionPathPositions h inj v) (right : Bool)
    (hp : u.parent h inj = some (w, right)) : w ∈ extractionPathPositions h inj v := by
  simp only [extractionPathPositions, List.mem_append, List.mem_filterMap] at hu ⊢
  rcases hu with hu | ⟨a, ha, heq⟩
  · exact Or.inl (v.parent_mem_path h inj u w hu right hp)
  · split at heq
    · rename_i hs
      cases Option.some.inj heq
      simp only [Position.parent, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      have eq : Position.mk a.depth a.index .injection = a := by
        cases a
        cases hs
        rfl
      rw [eq]
      exact Or.inl ha
    · cases heq

/-- A path witness checks operation shapes and hash links to the indexed cap entry. -/
@[expose] def checkPositionPath (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool) (cap : List Digest)
    (ops : Position → Op Payload Digest) (v : Position) : Bool :=
  decide (h ≤ K ∧ cap.length = 2 ^ h) &&
    (extractionPathPositions h inj v).all fun u =>
      u.opShape (ops u) && decide (answer hash compress (ops u) =
        match u.parent h inj with
        | none => cap.getD u.index (hash p₀)
        | some (parent, right) =>
            let pair := opChildren (hash p₀) (ops parent)
            if right then pair.2 else pair.1)

/-- Every predicted operation on a target path has its stage's shape and assigned hash output. -/
@[expose] def positionConsistent (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool) (A : MerkleAdversary Coins Payload Digest)
    (X : ExtractorMap Coins Payload Digest) (c : Coins) (v : Position) : Bool :=
  checkPositionPath hash compress p₀ K h inj (A c).1
    (fun u => extractedOp hash compress p₀ K h inj A X u c) v

/-- Every predicted operation from a cap to a leaf, including injected payloads, is consistent. -/
@[expose] def pathConsistent (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool) (A : MerkleAdversary Coins Payload Digest)
    (X : ExtractorMap Coins Payload Digest) (c : Coins) (i : ℕ) : Bool :=
  positionConsistent hash compress p₀ K h inj A X c ⟨K, i, .leaf⟩

/-- A leaf is known exactly when all extracted path operations are hash-consistent. -/
@[expose] def extractedMask (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool) (A : MerkleAdversary Coins Payload Digest)
    (X : ExtractorMap Coins Payload Digest) (c : Coins) (i : Fin (2 ^ K)) : Option Payload :=
  if pathConsistent hash compress p₀ K h inj A X c i then
    some (extractedLeaves hash compress p₀ K h inj A X c i)
  else none

/-- An injected payload is known exactly when its own path from the cap is consistent. -/
@[expose] def extractedInjectionMask (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) (d : ℕ) (i : Fin (2 ^ d)) : Option Payload :=
  if h ≤ d ∧ d < K ∧ inj d = true then
    let v := Position.mk d i .payload
    if positionConsistent hash compress p₀ K h inj A X c v then
      some (opPayload p₀ (extractedOp hash compress p₀ K h inj A X v c))
    else none
  else none

/-- Absence of node failures on a parent-closed path determines its revealed operations. -/
theorem opening_op_eq_extracted_local (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) (S : List Position)
    (closed : ∀ v ∈ S, ∀ u right, v.parent h inj = some (u, right) → u ∈ S)
    (hgood : ∀ v ∈ S, v ∈ positions K h inj →
      ¬ NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) c)
    (o : Opening Payload Digest) (ho : o ∈ (A c).2)
    (hver : o.Verifies hash compress K h inj (A c).1) (v : Position) (member : v ∈ S)
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
        have hpred := (ih u (v.parent_rank_lt h inj u right hp)
          (closed v member u right hp) hu _ hqu).1
        change o.opAt hash compress p₀ K h u =
          X (derivedAdversary hash compress p₀ K h inj A X u) c at hpred
        rw [← hpred]
        exact o.parent_edge hash compress p₀ K h inj (A c).1 hver v u right hvalid hi hp
    refine ⟨?_, htarget⟩
    by_contra hne
    apply hgood v member hv
    exact ⟨o.opAt hash compress p₀ K h v,
      opening_op_mem hash compress p₀ K h inj A X c o ho hver v _
        (by rw [o.ops_eq_singleton hash compress p₀ K h inj (A c).1 hver v hvalid hi]
            exact List.mem_singleton_self _), htarget, hne⟩

/-- Without failures on a target's cap path, all predicted path operations are consistent. -/
theorem positionConsistent_of_no_nodeBad (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) (o : Opening Payload Digest) (ho : o ∈ (A c).2)
    (hver : o.Verifies hash compress K h inj (A c).1) (v : Position)
    (hv : v.Valid K h inj) (hi : o.index >>> (K - v.depth) = v.index)
    (good : ∀ u ∈ extractionPathPositions h inj v, u ∈ positions K h inj →
      ¬ NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X u)
        (X (derivedAdversary hash compress p₀ K h inj A X u)) c) :
    positionConsistent hash compress p₀ K h inj A X c v = true := by
  simp only [positionConsistent, checkPositionPath, Bool.and_eq_true_iff,
    decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨hver.1, hver.2.1⟩, ?_⟩
  intro u hu
  obtain ⟨huv, hui⟩ := o.extractionPath_valid K h inj v hv hi u hu
  have hq : o.opAt hash compress p₀ K h u ∈ o.ops hash compress p₀ K h u := by
    rw [o.ops_eq_singleton hash compress p₀ K h inj (A c).1 hver u huv hui]
    exact List.mem_singleton_self _
  obtain ⟨same, target⟩ := opening_op_eq_extracted_local hash compress p₀ K h inj A X c
    (extractionPathPositions h inj v)
    (fun a ha b right hp => extractionPath_parent_mem h inj v a b ha right hp) good
    o ho hver u hu ((mem_positions K h inj u).mpr huv) _ hq
  refine ⟨?_, ?_⟩
  · rw [← same]
    rcases u with ⟨depth, index, stage⟩
    cases stage <;> rfl
  · rw [← same]
    refine target.trans ?_
    rw [derivedAdversary]
    cases hp : u.parent h inj with
    | none => rfl
    | some pair =>
        rcases pair with ⟨parent, right⟩
        rfl

/-- Opening an unknown injected column forces a node failure on that payload's cap path. -/
theorem opening_injection_none_implies_nodeBad (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) (o : Opening Payload Digest) (ho : o ∈ (A c).2)
    (hv : o.Verifies hash compress K h inj (A c).1) (d : ℕ)
    (hd : h ≤ d) (hdK : d < K) (hinj : inj d = true)
    (unknown : extractedInjectionMask hash compress p₀ K h inj A X c d
      ⟨o.index >>> (K - d), hv.index_lt hash compress K h inj (A c).1 o d hdK.le⟩ = none) :
    ∃ v ∈ extractionPathPositions h inj ⟨d, o.index >>> (K - d), .payload⟩,
      v ∈ positions K h inj ∧
      NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) c := by
  classical
  by_contra absent
  have good : ∀ u ∈ extractionPathPositions h inj
      ⟨d, o.index >>> (K - d), .payload⟩, u ∈ positions K h inj →
      ¬ NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X u)
        (X (derivedAdversary hash compress p₀ K h inj A X u)) c := by
    simpa only [not_exists, not_and] using absent
  have consistent := positionConsistent_of_no_nodeBad hash compress p₀ K h inj A X c o ho hv
    ⟨d, o.index >>> (K - d), .payload⟩
    ⟨hd, hdK.le, hv.index_lt hash compress K h inj (A c).1 o d hdK.le, hdK, hinj⟩ rfl good
  simp only [extractedInjectionMask, hd, hdK, hinj, and_self, ↓reduceIte, consistent,
    reduceCtorEq] at unknown

/-- A verifying opening of an unknown column forces a node failure on that very path and coins. -/
theorem opening_none_implies_nodeBad (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) (o : Opening Payload Digest) (ho : o ∈ (A c).2)
    (hv : o.Verifies hash compress K h inj (A c).1)
    (unknown : extractedMask hash compress p₀ K h inj A X c ⟨o.index, hv.2.2.1⟩ = none) :
    ∃ v ∈ maskPositions K h inj o.index, v ∈ positions K h inj ∧
      NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) c := by
  classical
  by_contra absent
  have good : ∀ u ∈ extractionPathPositions h inj ⟨K, o.index, .leaf⟩,
      u ∈ positions K h inj →
      ¬ NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X u)
        (X (derivedAdversary hash compress p₀ K h inj A X u)) c := by
    simpa only [maskPositions, not_exists, not_and] using absent
  have consistent := positionConsistent_of_no_nodeBad hash compress p₀ K h inj A X c o ho hv
    ⟨K, o.index, .leaf⟩ ⟨hv.1, le_rfl, hv.2.2.1, rfl⟩
    (by simp only [Nat.sub_self, Nat.shiftRight_zero]) good
  simp only [extractedMask, pathConsistent, consistent, ↓reduceIte, reduceCtorEq] at unknown

/-- Every verifying opening either agrees with partial extraction or exposes a node failure. -/
theorem opening_mask_disagree_implies_nodeBad (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) (o : Opening Payload Digest) (ho : o ∈ (A c).2)
    (hv : o.Verifies hash compress K h inj (A c).1)
    (disagree : extractedMask hash compress p₀ K h inj A X c ⟨o.index, hv.2.2.1⟩ ≠
      some o.payload) :
    ∃ v ∈ positions K h inj,
      NodeBad (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) c := by
  cases hm : extractedMask hash compress p₀ K h inj A X c ⟨o.index, hv.2.2.1⟩ with
  | none =>
      obtain ⟨v, _, hv', bad⟩ := opening_none_implies_nodeBad hash compress p₀ K h inj A X
        c o ho hv hm
      exact ⟨v, hv', bad⟩
  | some p =>
      have hp : p = extractedLeaves hash compress p₀ K h inj A X c o.index := by
        unfold extractedMask at hm
        split at hm
        · exact (Option.some.inj hm).symm
        · cases hm
      apply disagreement_implies_nodeBad hash compress p₀ K h inj A X c o ho hv
      exact Or.inl (fun he => disagree (by rw [hm, hp, ← he]))

/-- The existing node-failure sum bounds openings outside the mask and wrong known payloads. -/
theorem masked_knowledge_bound [SampleableType Coins] (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest) :
    Pr{let c ← $ᵗ Coins}[∃ o ∈ (A c).2, ∃ hv : o.Verifies hash compress K h inj (A c).1,
      extractedMask hash compress p₀ K h inj A X c ⟨o.index, hv.2.2.1⟩ ≠ some o.payload] ≤
    ∑ v ∈ positions K h inj,
      nodeFail (answer hash compress) (derivedAdversary hash compress p₀ K h inj A X v)
        (X (derivedAdversary hash compress p₀ K h inj A X v)) := by
  refine (prEvent_mono ($ᵗ Coins) _ _ ?_).trans
    (prEvent_exists_finset_le (positions K h inj) ($ᵗ Coins) _)
  rintro c ⟨o, ho, hv, hd⟩
  exact opening_mask_disagree_implies_nodeBad hash compress p₀ K h inj A X c o ho hv hd

/-- A partial-word witness supplies hash and compression operations for every known cap path. -/
structure MaskAuthentication (Payload Digest : Type) (K : ℕ) where
  /-- The authenticated partial word. -/
  word : Fin (2 ^ K) → Option Payload
  /-- Operations linking revealed leaf payloads to their cap entries. -/
  operations : Position → Op Payload Digest

/-- Authentication checks every known column against its typed operation path. -/
@[expose] def MaskAuthentication.check [DecidableEq Payload]
    (hash : Payload → Digest) (compress : Digest → Digest → Digest) (p₀ : Payload)
    (K h : ℕ) (inj : ℕ → Bool) (cap : List Digest)
    (w : MaskAuthentication Payload Digest K) : Bool :=
  (List.ofFn fun i : Fin (2 ^ K) => match w.word i with
    | none => true
    | some p => checkPositionPath hash compress p₀ K h inj cap w.operations ⟨K, i, .leaf⟩ &&
        decide (opPayload p₀ (w.operations ⟨K, i, .leaf⟩) = p)).all id

/-- The same-coins extractor produces partial words and their authentication computably. -/
@[expose] def extractedAuthentication (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) : MaskAuthentication Payload Digest K where
  word := extractedMask hash compress p₀ K h inj A X c
  operations v := extractedOp hash compress p₀ K h inj A X v c

/-- The reduction's extracted partial-word witness passes authentication unconditionally. -/
theorem extractedAuthentication_check [DecidableEq Payload] (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) :
    (extractedAuthentication hash compress p₀ K h inj A X c).check hash compress p₀ K h inj
      (A c).1 = true := by
  simp only [MaskAuthentication.check, List.all_eq_true, List.forall_mem_ofFn_iff]
  intro i
  simp only [extractedAuthentication, extractedMask]
  by_cases known : pathConsistent hash compress p₀ K h inj A X c i = true
  · have known' := known
    unfold pathConsistent positionConsistent at known'
    simp [known, known', extractedLeaves]
  · simp [known]

/-- An injected-payload witness supplies predicted operations on its cap paths. -/
structure InjectionMaskAuthentication (Payload Digest : Type) (d : ℕ) where
  /-- The authenticated partial injected-payload word. -/
  word : Fin (2 ^ d) → Option Payload
  /-- Operations authenticating the payloads through the mixed tree. -/
  operations : Position → Op Payload Digest

/-- Injection authentication checks payload hashes and every ancestor operation to the cap. -/
@[expose] def InjectionMaskAuthentication.check [DecidableEq Payload]
    (hash : Payload → Digest) (compress : Digest → Digest → Digest) (p₀ : Payload)
    (K h d : ℕ) (inj : ℕ → Bool) (cap : List Digest)
    (w : InjectionMaskAuthentication Payload Digest d) : Bool :=
  (List.ofFn fun i : Fin (2 ^ d) => match w.word i with
    | none => true
    | some p => decide (h ≤ d ∧ d < K ∧ inj d = true) &&
        checkPositionPath hash compress p₀ K h inj cap w.operations ⟨d, i, .payload⟩ &&
        decide (opPayload p₀ (w.operations ⟨d, i, .payload⟩) = p)).all id

/-- The injected-payload reduction supplies the same extracted operations and mask. -/
@[expose] def extractedInjectionAuthentication (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h d : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) : InjectionMaskAuthentication Payload Digest d where
  word := extractedInjectionMask hash compress p₀ K h inj A X c d
  operations v := extractedOp hash compress p₀ K h inj A X v c

/-- The extracted injected-payload mask authenticates unconditionally on the same coins. -/
theorem extractedInjectionAuthentication_check [DecidableEq Payload]
    (hash : Payload → Digest) (compress : Digest → Digest → Digest) (p₀ : Payload)
    (K h d : ℕ) (inj : ℕ → Bool) (A : MerkleAdversary Coins Payload Digest)
    (X : ExtractorMap Coins Payload Digest) (c : Coins) :
    (extractedInjectionAuthentication hash compress p₀ K h d inj A X c).check
      hash compress p₀ K h d inj (A c).1 = true := by
  simp only [InjectionMaskAuthentication.check, List.all_eq_true,
    List.forall_mem_ofFn_iff]
  intro i
  simp only [extractedInjectionAuthentication, extractedInjectionMask]
  by_cases shape : h ≤ d ∧ d < K ∧ inj d = true
  · by_cases known : positionConsistent hash compress p₀ K h inj A X c
        ⟨d, i, .payload⟩ = true
    · have known' := known
      unfold positionConsistent at known'
      simp [shape, known, known']
    · simp [shape, known]
  · simp [shape]

/-- Checked paths bind their target unless unequal operations have the same answer. -/
theorem checkPositionPath_binding (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (cap : List Digest) (left right : Position → Op Payload Digest) (v : Position)
    (hl : checkPositionPath hash compress p₀ K h inj cap left v = true)
    (hr : checkPositionPath hash compress p₀ K h inj cap right v = true)
    (different : left v ≠ right v) :
    ∃ u ∈ extractionPathPositions h inj v,
      left u ≠ right u ∧ answer hash compress (left u) = answer hash compress (right u) := by
  classical
  have links (ops : Position → Op Payload Digest)
      (checked : checkPositionPath hash compress p₀ K h inj cap ops v = true) :
      ∀ u ∈ extractionPathPositions h inj v,
        answer hash compress (ops u) =
          match u.parent h inj with
          | none => cap.getD u.index (hash p₀)
          | some (parent, side) =>
              let pair := opChildren (hash p₀) (ops parent)
              if side then pair.2 else pair.1 := by
    simp only [checkPositionPath, Bool.and_eq_true_iff, List.all_eq_true] at checked
    intro u hu
    exact of_decide_eq_true (checked.2 u hu).2
  by_contra absent
  have equal : ∀ u ∈ extractionPathPositions h inj v, left u = right u := by
    intro u
    induction u using (measure Position.rank).wf.induction with
    | h u ih =>
      intro hu
      have answers : answer hash compress (left u) = answer hash compress (right u) := by
        rw [links left hl u hu, links right hr u hu]
        cases hp : u.parent h inj with
        | none => rfl
        | some pair =>
            obtain ⟨parent, side⟩ := pair
            dsimp only
            rw [ih parent (u.parent_rank_lt h inj parent side hp)
              (extractionPath_parent_mem h inj v u parent hu side hp)]
      by_contra unequal
      exact absent ⟨u, hu, unequal, answers⟩
  exact different (equal v (List.mem_append_left _ (List.mem_cons_self)))

/-- A revealed leaf in a checked mask has a checked cap path and the stated payload. -/
theorem MaskAuthentication.check_known [DecidableEq Payload]
    (hash : Payload → Digest) (compress : Digest → Digest → Digest) (p₀ : Payload)
    (K h : ℕ) (inj : ℕ → Bool) (cap : List Digest)
    (w : MaskAuthentication Payload Digest K)
    (checked : w.check hash compress p₀ K h inj cap = true)
    (i : Fin (2 ^ K)) (p : Payload) (known : w.word i = some p) :
    checkPositionPath hash compress p₀ K h inj cap w.operations ⟨K, i, .leaf⟩ = true ∧
      opPayload p₀ (w.operations ⟨K, i, .leaf⟩) = p := by
  simp only [MaskAuthentication.check, List.all_eq_true, List.forall_mem_ofFn_iff] at checked
  simpa only [known, id_eq, Bool.and_eq_true_iff, decide_eq_true_eq] using checked i

/-- A revealed injected payload in a checked mask has a checked cap path and its stated value. -/
theorem InjectionMaskAuthentication.check_known [DecidableEq Payload]
    (hash : Payload → Digest) (compress : Digest → Digest → Digest) (p₀ : Payload)
    (K h d : ℕ) (inj : ℕ → Bool) (cap : List Digest)
    (w : InjectionMaskAuthentication Payload Digest d)
    (checked : w.check hash compress p₀ K h d inj cap = true)
    (i : Fin (2 ^ d)) (p : Payload) (known : w.word i = some p) :
    (h ≤ d ∧ d < K ∧ inj d = true) ∧
      checkPositionPath hash compress p₀ K h inj cap w.operations ⟨d, i, .payload⟩ = true ∧
        opPayload p₀ (w.operations ⟨d, i, .payload⟩) = p := by
  simp only [InjectionMaskAuthentication.check, List.all_eq_true,
    List.forall_mem_ofFn_iff] at checked
  have result := checked i
  simp only [known, id_eq, Bool.and_eq_true_iff, decide_eq_true_eq] at result
  exact ⟨result.1.1, result.1.2, result.2⟩

/-- Different authenticated leaves under one cap exhibit a hash-operation collision. -/
theorem MaskAuthentication.binding [DecidableEq Payload]
    (hash : Payload → Digest) (compress : Digest → Digest → Digest) (p₀ : Payload)
    (K h : ℕ) (inj : ℕ → Bool) (cap : List Digest)
    (left right : MaskAuthentication Payload Digest K)
    (hl : left.check hash compress p₀ K h inj cap = true)
    (hr : right.check hash compress p₀ K h inj cap = true)
    (i : Fin (2 ^ K)) (a b : Payload) (ha : left.word i = some a)
    (hb : right.word i = some b) (different : a ≠ b) :
    ∃ u ∈ maskPositions K h inj i,
      left.operations u ≠ right.operations u ∧
        answer hash compress (left.operations u) = answer hash compress (right.operations u) := by
  simp only [MaskAuthentication.check, List.all_eq_true, List.forall_mem_ofFn_iff] at hl hr
  have la := hl i
  have rb := hr i
  simp only [ha, id_eq, Bool.and_eq_true_iff, decide_eq_true_eq] at la
  simp only [hb, id_eq, Bool.and_eq_true_iff, decide_eq_true_eq] at rb
  apply checkPositionPath_binding hash compress p₀ K h inj cap left.operations right.operations
    ⟨K, i, .leaf⟩ la.1 rb.1
  intro same
  exact different (la.2.symm.trans ((congrArg (opPayload p₀) same).trans rb.2))

/-- Different authenticated injected payloads exhibit a hash-operation collision. -/
theorem InjectionMaskAuthentication.binding [DecidableEq Payload]
    (hash : Payload → Digest) (compress : Digest → Digest → Digest) (p₀ : Payload)
    (K h d : ℕ) (inj : ℕ → Bool) (cap : List Digest)
    (left right : InjectionMaskAuthentication Payload Digest d)
    (hl : left.check hash compress p₀ K h d inj cap = true)
    (hr : right.check hash compress p₀ K h d inj cap = true)
    (i : Fin (2 ^ d)) (a b : Payload) (ha : left.word i = some a)
    (hb : right.word i = some b) (different : a ≠ b) :
    ∃ u ∈ extractionPathPositions h inj ⟨d, i, .payload⟩,
      left.operations u ≠ right.operations u ∧
        answer hash compress (left.operations u) = answer hash compress (right.operations u) := by
  simp only [InjectionMaskAuthentication.check, List.all_eq_true,
    List.forall_mem_ofFn_iff] at hl hr
  have la := hl i
  have rb := hr i
  simp only [ha, id_eq, Bool.and_eq_true_iff, decide_eq_true_eq] at la
  simp only [hb, id_eq, Bool.and_eq_true_iff, decide_eq_true_eq] at rb
  apply checkPositionPath_binding hash compress p₀ K h inj cap left.operations right.operations
    ⟨d, i, .payload⟩ la.1.2 rb.1.2
  intro same
  exact different (la.2.symm.trans ((congrArg (opPayload p₀) same).trans rb.2))

end MixedMerkleTree.Knowledge
