/-
Copyright (c) 2026 Gregor Mitscha-Baude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Mixed.Forest
public import VCVio.CryptoFoundations.MerkleTree.Mixed.Multi

/-!
# Canary tests for Merkle trees with injected payloads

A height-3 tree whose depth-1 nodes inject payloads, with a role- and order-sensitive hash and
compression. The examples pin the cap of height 1, an honest single opening climbing to its cap
entry, an honest pruned multi-opening walking to the cap entries and taking every sibling, and the
cap's hash-forest evaluation.
-/

public section

namespace VCVioTest.MerkleTreeMixedCanary

open MixedMerkleTree

def hash (p : ℕ) : List ℕ := [0, p]

def compress (a b : List ℕ) : List ℕ := 1 :: a.length :: a ++ b

def leaves (i : ℕ) : ℕ := 10 + i

/-- Depth `1` injects the payload `20 + i` into node `i`. -/
def inj (t : ℕ) : Option (ℕ → ℕ) := if t = 1 then some (20 + ·) else none

def capOf : List (List ℕ) := cap hash compress 3 leaves inj 1

/-- The cap entries are the injected depth-1 nodes. -/
example : capOf = [compress (compress (compress (hash 10) (hash 11)) (compress (hash 12) (hash 13)))
    (hash 20), compress (compress (compress (hash 14) (hash 15)) (compress (hash 16) (hash 17)))
    (hash 21)] := by
  decide

/-- The honest opening of leaf `5` climbs to its cap entry. -/
example : climb hash compress (pays 3 inj 5 2) 5 (hash (leaves 5))
    (siblings hash compress 3 leaves inj 5 2) = capOf.getD 1 [] := by
  decide

/-- The honest multi-opening of leaves `6`, `1`, `6`, `0`, from their frontier (leaf `6` led by
its first query), walks to their cap entries and takes every pruned sibling. -/
example :
    let indices := [6, 1, 6, 0]
    let fr := [(0, 3), (1, 1), (6, 0)]
    let paths := indices.map fun i ↦ siblings hash compress 3 leaves inj i 2
    walk hash compress [] (fun d ↦ (inj (1 + d)).map fun f q ↦ f (indices.getD q 0 >>> (2 - d))) 2
        (fr.map fun e ↦ (e.1, e.2, node hash compress 3 leaves inj 0 e.1))
        (pruneWalk [] paths 2 0 fr) =
      ([(0, 3, capOf.getD 0 []), (1, 0, capOf.getD 1 [])], []) ∧
    (pruneWalk [] paths 2 0 fr).length = siblingCount 2 (fr.map (·.1)) := by
  decide

/-- The cap as a hash forest evaluates to the cap. -/
example (answer : MerkleHashForest.Query MerkleHashForest.BinaryOperationKind Unit Unit ℕ (List ℕ) →
    List ℕ) (h : Answers hash compress answer) :
    (MerkleHashForest.evaluateForestWithHash answer (forest 3 leaves inj 1)).toList = capOf :=
  evaluateForestWithHash_forest h 3 leaves inj 1

end VCVioTest.MerkleTreeMixedCanary
