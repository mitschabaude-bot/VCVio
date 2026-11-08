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

/-- Every predicted operation on a target path has its stage's shape and assigned hash output. -/
@[expose] def positionConsistent (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool) (A : MerkleAdversary Coins Payload Digest)
    (X : ExtractorMap Coins Payload Digest) (c : Coins) (v : Position) : Bool :=
  (extractionPathPositions h inj v).all fun u =>
    let op := extractedOp hash compress p₀ K h inj A X u c
    u.opShape op && decide (answer hash compress op =
      (derivedAdversary hash compress p₀ K h inj A X u c).1)

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
  sorry

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
  sorry

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

/-- A partial-word witness supplies a Merkle opening for each revealed column. -/
structure MaskAuthentication (Payload Digest : Type) (K : ℕ) where
  /-- The authenticated partial word. -/
  word : Fin (2 ^ K) → Option Payload
  /-- Paths supplied for the known columns. -/
  openings : Fin (2 ^ K) → Option (Opening Payload Digest)

/-- The finite authentication checker verifies every known column and ignores hidden columns. -/
@[expose] def MaskAuthentication.check [DecidableEq Payload]
    (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (K h : ℕ) (inj : ℕ → Bool) (cap : List Digest)
    (w : MaskAuthentication Payload Digest K) : Bool :=
  decide (h ≤ K ∧ cap.length = 2 ^ h) &&
    (List.ofFn fun i : Fin (2 ^ K) => match w.word i, w.openings i with
      | none, _ => true
      | some p, some o => decide (o.index = i.val ∧ o.payload = p ∧
          o.Verifies hash compress K h inj cap)
      | some _, none => false).all id

/-- Reconstruct an opening from the predicted operations along one extracted leaf path. -/
@[expose] def extractedOpening (hash : Payload → Digest) (compress : Digest → Digest → Digest)
    (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool) (A : MerkleAdversary Coins Payload Digest)
    (X : ExtractorMap Coins Payload Digest) (c : Coins) (i : Fin (2 ^ K)) :
    Opening Payload Digest where
  index := i
  payload := extractedLeaves hash compress p₀ K h inj A X c i
  pays d := if d < K - h ∧ inj (h + d) then
    some (opPayload p₀ (extractedOp hash compress p₀ K h inj A X
      ⟨h + d, i.val >>> (K - (h + d)), .payload⟩ c)) else none
  path := List.ofFn fun l : Fin (K - h) =>
    let pair := opChildren (hash p₀) (extractedOp hash compress p₀ K h inj A X
      ⟨K - l.val - 1, i.val >>> (l.val + 1), .children⟩ c)
    if (i.val >>> l.val) % 2 = 0 then pair.2 else pair.1

/-- Hash-consistent extracted paths authenticate to the adversary's fixed cap. -/
theorem extractedOpening_verifies (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) (shape : h ≤ K ∧ (A c).1.length = 2 ^ h) (i : Fin (2 ^ K))
    (known : pathConsistent hash compress p₀ K h inj A X c i = true) :
    (extractedOpening hash compress p₀ K h inj A X c i).Verifies hash compress K h inj
      (A c).1 := by
  sorry

/-- The same-coins extractor produces partial words and their authentication computably. -/
@[expose] def extractedAuthentication (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) : MaskAuthentication Payload Digest K where
  word := extractedMask hash compress p₀ K h inj A X c
  openings i := if pathConsistent hash compress p₀ K h inj A X c i then
    some (extractedOpening hash compress p₀ K h inj A X c i) else none

/-- The reduction's extracted partial-word witness passes authentication for a well-shaped cap. -/
theorem extractedAuthentication_check [DecidableEq Payload] (hash : Payload → Digest)
    (compress : Digest → Digest → Digest) (p₀ : Payload) (K h : ℕ) (inj : ℕ → Bool)
    (A : MerkleAdversary Coins Payload Digest) (X : ExtractorMap Coins Payload Digest)
    (c : Coins) (shape : h ≤ K ∧ (A c).1.length = 2 ^ h) :
    (extractedAuthentication hash compress p₀ K h inj A X c).check hash compress K h inj
      (A c).1 = true := by
  sorry

end MixedMerkleTree.Knowledge
