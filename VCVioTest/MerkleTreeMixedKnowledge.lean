/-
Copyright (c) 2026 Gregor Mitscha-Baude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Mixed.Masked
public meta import VCVio.CryptoFoundations.MerkleTree.Mixed.Masked

/-!
# Executable mixed Merkle knowledge extraction

A height-three tree injects payloads at depths zero and one. A finite dictionary contains the
actual leaf hashes and compression preimages of the entire tree. The assigned node extractor
looks up only its target digest on the adversary's original coins. A single honest opening and
several malformed openings exercise the named leaf and injection extractors, including recovery
of leaves outside the revealed path, root and non-root caps, and explicit defaults.
-/

public section

namespace VCVioTest.MerkleTreeMixedKnowledge

open MixedMerkleTree MixedMerkleTree.Knowledge

/-- Tagged leaf encoding, distinct from compression encodings. -/
def hash (p : ℕ) : List ℕ := [0, p]

/-- Ordered compression encoding with a delimiter for the left digest. -/
def compress (a b : List ℕ) : List ℕ := 1 :: a.length :: a ++ b

/-- Two coin values select different private trees. -/
def leaves (c : Bool) (i : ℕ) : ℕ := (if c then 100 else 10) + i

/-- Payloads at both the root and the next depth exercise consecutive injections. -/
def injections (c : Bool) (d : ℕ) : Option (ℕ → ℕ) :=
  if d < 2 then some (fun i ↦ (if c then 200 else 20) + 10 * d + i) else none

/-- The public global injection schedule. -/
def schedule (d : ℕ) : Bool := d < 2

/-- A complete dictionary of actual hash and ordered compression preimages. -/
def dictionary (c : Bool) : List (List ℕ × Op ℕ (List ℕ)) :=
  let leafOps := (List.range 8).map fun i ↦ Sum.inl (leaves c i)
  let innerOps := (List.range 3).flatMap fun d ↦
    (List.range (2 ^ d)).flatMap fun i ↦
      let a := node hash compress 3 (leaves c) (injections c) (3 - d - 1) (2 * i)
      let b := node hash compress 3 (leaves c) (injections c) (3 - d - 1) (2 * i + 1)
      let children := Sum.inr (a, b)
      match injections c d with
      | none => [children]
      | some f => [children, .inl (f i), .inr (compress a b, hash (f i))]
  (leafOps ++ innerOps).map fun q ↦ (answer hash compress q, q)

/-- Lookup shares the two private dictionaries and uses the original coins and target digest. -/
def extractor : ExtractorMap Bool ℕ (List ℕ) :=
  let falseTree := dictionary false
  let trueTree := dictionary true
  fun B c ↦
    let entries := if c then trueTree else falseTree
    let target := (B c).1
    ((entries.find? fun entry ↦ entry.1 == target).map (·.2)).getD (.inl 0)

/-- An honest opening of leaf five below the chosen cap. -/
def opening (h : ℕ) (c : Bool) : Opening ℕ (List ℕ) :=
  ⟨5, leaves c 5, pays 3 (injections c) 5 (3 - h),
    siblings hash compress 3 (leaves c) (injections c) 5 (3 - h)⟩

/-- Malformed shapes, leaf indices, digests and injection payload schedules. -/
def malformed (h : ℕ) (c : Bool) : List (Opening ℕ (List ℕ)) :=
  let o := opening h c
  [{ o with index := 8 },
   { o with payload := 999 },
   { o with path := o.path.drop 1 },
   { o with path := o.path ++ [[]] },
   { o with path := o.path.map (fun _ ↦ []) },
   { o with pays := fun _ ↦ none },
   { o with pays := fun _ ↦ some 999 },
   { o with pays := fun d ↦ if d = 0 then some 999 else o.pays d },
   { o with pays := fun d ↦ if h + d = 2 then some 999 else o.pays d }]

/-- The transcript reveals one honest path, preceded by invalid openings. -/
def adversary (h : ℕ) : MerkleAdversary Bool ℕ (List ℕ) := fun c ↦
  (cap hash compress 3 (leaves c) (injections c) h, malformed h c ++ [opening h c])

/-- Materialize the complete leaf vector through the library extractor. -/
def recoveredLeaves (h : ℕ) (c : Bool) : List ℕ :=
  (List.range 8).map (extractedLeaves hash compress 0 3 h schedule (adversary h) extractor c)

/-- Materialize the extracted payloads at every depth through the library extractor. -/
def recoveredInjections (h : ℕ) (c : Bool) : List (Option (List ℕ)) :=
  (List.range 4).map fun d ↦
    (extractedInjections hash compress 0 3 h schedule (adversary h) extractor c d).map
      fun f ↦ (List.range (2 ^ d)).map f

/-- All payloads below the cap and every leaf agree with the private tree. -/
def recoversTree (h : ℕ) (c : Bool) : Bool :=
  recoveredLeaves h c == (List.range 8).map (leaves c) &&
  recoveredInjections h c == (List.range 4).map (fun d ↦
    if h ≤ d then (injections c d).map (fun f ↦ (List.range (2 ^ d)).map f) else none) &&
  cap hash compress 3
      (extractedLeaves hash compress 0 3 h schedule (adversary h) extractor c)
      (extractedInjections hash compress 0 3 h schedule (adversary h) extractor c) h ==
    (adversary h c).1

/-- Verifier decisions reject every malformed opening while accepting the honest path. -/
def checksOpenings (h : ℕ) (c : Bool) : Bool :=
  let cap := (adversary h c).1
  decide ((opening h c).Verifies hash compress 3 h schedule cap) &&
  (malformed h c).all (fun o ↦ !decide (o.Verifies hash compress 3 h schedule cap)) &&
  !decide ((opening h c).Verifies hash compress 3 h schedule []) &&
  !decide ((opening h c).Verifies hash compress 3 h schedule (cap ++ [[]])) &&
  !decide ((opening h c).Verifies hash compress 3 4 schedule cap)

/-- Invalid openings contribute no operations, including injected-payload operations. -/
def checksRevealed (h : ℕ) (c : Bool) : Bool :=
  [Position.mk 3 5 .leaf, ⟨1, 1, .payload⟩, ⟨1, 1, .children⟩,
      ⟨1, 1, .injection⟩, ⟨3, 0, .leaf⟩].all fun v ↦
    revealedOps hash compress 0 3 h schedule (adversary h) v c ==
      (opening h c).ops hash compress 0 3 h v

/-- Missing dictionary entries and wrong operation shapes use the fixed defaults. -/
def checksDefaults : Bool :=
  let absent : NodeAdversary Bool ℕ (List ℕ) := fun _ ↦ ([], [])
  let wrongShape : ExtractorMap Bool ℕ (List ℕ) := fun _ _ ↦ .inr ([], [])
  extractor absent false == .inl 0 &&
  extractedLeaves hash compress 7 3 0 schedule (adversary 0) wrongShape false 5 == 7 &&
  ((extractedInjections hash compress 7 3 0 schedule (adversary 0) wrongShape false 1).map
    (fun f ↦ f 1)) == some 7 &&
  ((extractedInjections hash compress 0 3 1 schedule (adversary 1) extractor false 0).isNone) &&
  ((extractedInjections hash compress 0 3 0 schedule (adversary 0) extractor false 3).isNone)

/-- The finite verification decision requires no equality on function-valued payloads. -/
def verifiesFunctionPayload (o : Opening (ℕ → ℕ) ℕ) : Bool :=
  decide (o.Verifies (fun p ↦ p 0) (· + ·) 0 0 (fun _ ↦ false) [o.payload 0])

/-- The empty-height tree is a single leaf with no injection depths. -/
def checksLeafCap : Bool :=
  let o : Opening ℕ (List ℕ) := ⟨0, 42, fun _ ↦ none, []⟩
  let A : MerkleAdversary Bool ℕ (List ℕ) := fun _ ↦ ([hash 42], [o])
  let X : ExtractorMap Bool ℕ (List ℕ) := fun _ _ ↦ .inl 42
  decide (o.Verifies hash compress 0 0 (fun _ ↦ false) [hash 42]) &&
    extractedLeaves hash compress 0 0 0 (fun _ ↦ false) A X false 0 == 42 &&
    verifiesFunctionPayload ⟨0, (fun n ↦ n + 1), fun _ ↦ none, []⟩

/-- Honest path extraction is full and its generated authentication verifies at every cap. -/
def checksMasks (h : ℕ) (c : Bool) : Bool :=
  let w := extractedAuthentication hash compress 0 3 h schedule (adversary h) extractor c
  (List.ofFn w.word).all Option.isSome &&
    w.check hash compress 3 h schedule (adversary h c).1 &&
    decide (w.word ⟨5, by decide⟩ = some (leaves c 5))

/-- A wrong injected payload prediction hides the entire path even with correct tree children. -/
def checksInjectedMask (c : Bool) : Bool :=
  let broken : ExtractorMap Bool ℕ (List ℕ) := fun B coins =>
    if (B coins).1 = hash ((injections coins 0).getD (fun _ => 0) 0) then .inl 999
    else extractor B coins
  let w := extractedAuthentication hash compress 0 3 0 schedule (adversary 0) broken c
  (List.ofFn w.word).all Option.isNone &&
    w.check hash compress 3 0 schedule (adversary 0 c).1

/-- Deterministic executable regression for full mixed-tree extraction. -/
def checks : Bool :=
  [false, true].all (fun c ↦ [0, 1].all fun h ↦
    recoversTree h c && checksOpenings h c && checksRevealed h c && checksMasks h c) &&
    checksDefaults && checksLeafCap && [false, true].all checksInjectedMask

#eval do
  unless checks do throw (IO.userError "mixed Merkle knowledge extraction failed")
  IO.println "mixed Merkle knowledge extraction: full trees, injections and malformed openings OK"

end VCVioTest.MerkleTreeMixedKnowledge
