/-
Copyright (c) 2026 Gregor Mitscha-Baude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Mixed.Defs

/-!
# Extracting payloads from answered hash queries

A Merkle commitment binds its payloads only through the hash queries answered so far. This module
reads a tree with injected payloads (`MixedMerkleTree.node`) back from those answers:

* A `Cache` records the answered queries as relations: which payloads the leaf hash sent to which
  digest, and which pairs `compress` sent to which digest. A random oracle's query cache and a query
  log are both caches.
* `nodeAt cache inj t i root`: the node `i` at depth `t` below `root`, walking down cached
  compressions; at an injecting depth (`inj t`) a node's first child is the pair of its children.
* `extract cache inj K t i root`: the payload of node `i` at depth `t` of the tree of height `K`: a
  cached preimage of the leaf at depth `K`, or of the hash an injecting node is compressed with.
* `extract_eq_of_noPrediction`: extraction does not change when the cache grows by entries whose
  answers are not digests extraction could reach: the root and the children of cached compressions.
  So extraction at the time a root is bound equals extraction at any later time.
* `extract_of_climb`: in a cache without two queries of one answer, a climb (`climb`) whose queries
  are all cached (`ClimbCached`) and that ends at the root opens the extracted payloads.
* `climbCached_of_fresh`: answering every query outside the cache by a digest `dstar` that
  absorbs compressions, a climb that does not end at `dstar` made only cached queries.

Extraction picks preimages by choice, so it depends on the cache's relations only, not on the order
of a log. It is the relational counterpart of `MerkleTreeExtractor.treeAt`, which takes the first
match in a log of node queries over raw leaves; this one also inverts the leaf hash and walks
through injected levels.
-/

public section

namespace MixedMerkleTree

universe u v

/-- Answered hash queries: `leaf p y` if the leaf hash of `p` was answered `y`, and
`node left right y` if the compression of `left, right` was answered `y`. -/
structure Cache (Payload : Type u) (Digest : Type v) where
  /-- The answered leaf-hash queries. -/
  leaf : Payload → Digest → Prop
  /-- The answered compression queries. -/
  node : Digest → Digest → Digest → Prop

namespace Cache

variable {Payload : Type u} {Digest : Type v}

/-- No two cached payloads hash to one digest, and no two cached pairs compress to one digest. -/
structure Injective (cache : Cache Payload Digest) : Prop where
  leaf : ∀ p p' y, cache.leaf p y → cache.leaf p' y → p = p'
  node : ∀ left right left' right' y, cache.node left right y → cache.node left' right' y →
    left = left' ∧ right = right'

/-- The digests extraction under `root` can reach: `root` and the children of cached
compressions. -/
@[expose]
def Known (cache : Cache Payload Digest) (root y : Digest) : Prop :=
  y = root ∨ ∃ left right parent, cache.node left right parent ∧ (y = left ∨ y = right)

/-- `later` extends `now` and every entry it adds answers a digest not `Known` to `now`: no added
query predicts a digest that extraction from `now` under `root` can reach. -/
structure NoPrediction (now later : Cache Payload Digest) (root : Digest) : Prop where
  leaf_le : ∀ p y, now.leaf p y → later.leaf p y
  node_le : ∀ left right y, now.node left right y → later.node left right y
  leaf_new : ∀ p y, later.leaf p y → now.Known root y → now.leaf p y
  node_new : ∀ left right y, later.node left right y → now.Known root y → now.node left right y

end Cache

section Extract

variable {Payload : Type u} {Digest : Type v}

/-- Some `a` with `P a`, if there is one. -/
@[expose]
noncomputable def pick {α : Type*} (P : α → Prop) : Option α :=
  open Classical in if h : ∃ a, P a then some (Classical.choose h) else none

/-- The children of `parent`: a cached pair compressing to it. -/
@[expose]
noncomputable def children (cache : Cache Payload Digest) (parent : Digest) :
    Option (Digest × Digest) :=
  pick fun pair ↦ cache.node pair.1 pair.2 parent

/-- The node `i` at depth `t` below `root` (`2 ^ t` nodes), walking down cached compressions. The
parent of node `i` is node `i / 2`, and node `i` is its left child for even `i`; a node at an
injecting depth is the compression of the pair of its children with an injected hash. -/
@[expose]
noncomputable def nodeAt (cache : Cache Payload Digest) (inj : ℕ → Bool) :
    (t i : ℕ) → (root : Digest) → Option Digest
  | 0, _, root => some root
  | t + 1, i, root => (nodeAt cache inj t (i / 2) root).bind fun y ↦
      ((if inj t then (children cache y).map Prod.fst else some y).bind fun p ↦
        (children cache p).map fun lr ↦ if i % 2 = 0 then lr.1 else lr.2)

/-- The payload of node `i` at depth `t` of the tree of height `K` under `root`: a cached preimage
of the leaf if `t = K`, or of the hash the node is compressed with otherwise. -/
@[expose]
noncomputable def extract (cache : Cache Payload Digest) (inj : ℕ → Bool) (K t i : ℕ)
    (root : Digest) : Option Payload :=
  (nodeAt cache inj t i root).bind fun y ↦
    ((if t = K then some y else (children cache y).map Prod.snd).bind fun h ↦
      pick fun p ↦ cache.leaf p h)

/-- `pick` of a unique witness. -/
theorem pick_eq {α : Type*} (P : α → Prop) (a : α) (ha : P a) (huniq : ∀ b, P b → b = a) :
    pick P = some a := by
  have h : ∃ a, P a := ⟨a, ha⟩
  simp only [pick, h, ↓reduceDIte, huniq _ (Classical.choose_spec h)]

/-- `pick` returns a witness. -/
theorem pick_spec {α : Type*} (P : α → Prop) (a : α) (h : pick P = some a) : P a := by
  unfold pick at h
  split at h
  · rename_i hex
    rw [← Option.some.inj h]
    exact Classical.choose_spec hex
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

variable (cache : Cache Payload Digest)

/-- The children of a cached compression in an injective cache. -/
theorem children_eq (hinj : cache.Injective) (left right parent : Digest)
    (h : cache.node left right parent) : children cache parent = some (left, right) :=
  pick_eq _ (left, right) h fun pair hpair ↦ by
    obtain ⟨h1, h2⟩ := hinj.node _ _ _ _ _ hpair h
    rw [← h1, ← h2]

/-- The payload of a cached leaf hash in an injective cache. -/
theorem pick_leaf_eq (hinj : cache.Injective) (p : Payload) (y : Digest) (h : cache.leaf p y) :
    pick (fun p' ↦ cache.leaf p' y) = some p :=
  pick_eq _ p h fun _ h' ↦ hinj.leaf _ _ _ h' h

/-- Without injections, a node is its parent's child on the side of its index. -/
theorem nodeAt_succ_of_not_inj (inj : ℕ → Bool) (t i : ℕ) (root : Digest) (ht : inj t = false) :
    nodeAt cache inj (t + 1) i root = (nodeAt cache inj t (i / 2) root).bind fun y ↦
      (children cache y).map fun lr ↦ if i % 2 = 0 then lr.1 else lr.2 := by
  simp only [nodeAt, ht, Bool.false_eq_true, ↓reduceIte, Option.bind_some]

/-- In an injective cache, a payload whose cached leaf hash is the extracted leaf is extracted. -/
theorem extract_leaf (hinj : cache.Injective) (inj : ℕ → Bool) (K i : ℕ) (root : Digest)
    (p : Payload) (y : Digest) (hn : nodeAt cache inj K i root = some y)
    (hp : cache.leaf p y) :
    extract cache inj K K i root = some p := by
  simp only [extract, hn, Option.bind_some, ↓reduceIte]
  exact pick_leaf_eq cache hinj p _ hp

/-- Every node extraction reaches is `Known`. -/
theorem known_of_nodeAt (inj : ℕ → Bool) (root : Digest) :
    (t i : ℕ) → (y : Digest) → nodeAt cache inj t i root = some y → cache.Known root y
  | 0, _, y, h => by
    simp only [nodeAt, Option.some.injEq] at h
    exact Or.inl h.symm
  | t + 1, i, y, h => by
    simp only [nodeAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨parent, -, p, -, ⟨left, right⟩, hc, hy⟩ := h
    have hnode : cache.node left right p :=
      pick_spec (fun pair : Digest × Digest ↦ cache.node pair.1 pair.2 p) _ hc
    refine Or.inr ⟨left, right, p, hnode, ?_⟩
    by_cases hi : i % 2 = 0
    · simp only [hi, ↓reduceIte] at hy; exact Or.inl hy.symm
    · simp only [hi, ↓reduceIte] at hy; exact Or.inr hy.symm

/-- Without prediction, a `Known` digest has the same children later. -/
theorem children_eq_of_noPrediction (now later : Cache Payload Digest) (root y : Digest)
    (h : now.NoPrediction later root) (hy : now.Known root y) :
    children later y = children now y := by
  have hP : (fun pair : Digest × Digest ↦ later.node pair.1 pair.2 y) =
      fun pair ↦ now.node pair.1 pair.2 y :=
    funext fun pair ↦ propext ⟨fun hl ↦ h.node_new _ _ _ hl hy, h.node_le _ _ _⟩
  simp only [children, hP]

/-- Without prediction, extracted nodes stay the same. -/
theorem nodeAt_eq_of_noPrediction (now later : Cache Payload Digest) (inj : ℕ → Bool)
    (root : Digest) (h : now.NoPrediction later root) :
    (t i : ℕ) → nodeAt later inj t i root = nodeAt now inj t i root
  | 0, _ => rfl
  | t + 1, i => by
    simp only [nodeAt, nodeAt_eq_of_noPrediction now later inj root h t (i / 2)]
    cases hp : nodeAt now inj t (i / 2) root with
    | none => rfl
    | some y =>
      have hy := known_of_nodeAt now inj root _ _ _ hp
      simp only [Option.bind_some, children_eq_of_noPrediction now later root y h hy]
      split
      · cases hc : children now y with
        | none => rfl
        | some pq =>
          have hpq : now.node pq.1 pq.2 y :=
            pick_spec (fun pair : Digest × Digest ↦ now.node pair.1 pair.2 y) _ hc
          simp only [Option.map_some, Option.bind_some,
            children_eq_of_noPrediction now later root pq.1 h
              (Or.inr ⟨pq.1, pq.2, y, hpq, Or.inl rfl⟩)]
      · simp only [Option.bind_some, children_eq_of_noPrediction now later root y h hy]

/-- **Stability of extraction.** Extraction under `root` does not change when the cache grows by
entries that predict no digest it can reach. -/
theorem extract_eq_of_noPrediction (now later : Cache Payload Digest) (inj : ℕ → Bool)
    (root : Digest) (h : now.NoPrediction later root) (K t i : ℕ) :
    extract later inj K t i root = extract now inj K t i root := by
  simp only [extract, nodeAt_eq_of_noPrediction now later inj root h]
  cases hp : nodeAt now inj t i root with
  | none => rfl
  | some y =>
    have hy := known_of_nodeAt now inj root _ _ _ hp
    have hleaf : ∀ x, now.Known root x →
        (fun p ↦ later.leaf p x) = fun p ↦ now.leaf p x := fun x hx ↦
      funext fun p ↦ propext ⟨fun hl ↦ h.leaf_new _ _ hl hx, h.leaf_le _ _⟩
    simp only [Option.bind_some]
    split
    · simp only [Option.bind_some, hleaf y hy]
    · rw [children_eq_of_noPrediction now later root y h hy]
      cases hc : children now y with
      | none => rfl
      | some pq =>
        have hpq : now.node pq.1 pq.2 y :=
          pick_spec (fun pair : Digest × Digest ↦ now.node pair.1 pair.2 y) _ hc
        simp only [Option.map_some, Option.bind_some,
          hleaf pq.2 (Or.inr ⟨pq.1, pq.2, y, hpq, Or.inr rfl⟩)]

end Extract

/-! ### Extraction from accepted climbs -/

section Climb

variable {Payload : Type u} {Digest : Type v} (cache : Cache Payload Digest)
  (hash : Payload → Digest) (compress : Digest → Digest → Digest)

/-- Every query of a climb is cached: each compression with a sibling, and each injected payload's
leaf hash and its compression. -/
@[expose]
def ClimbCached (pays : ℕ → Option Payload) : ℕ → Digest → List Digest → Prop
  | _, _, [] => True
  | i, x, s :: path =>
    (if i % 2 = 0 then cache.node x s (pairUp compress i x s)
      else cache.node s x (pairUp compress i x s)) ∧
      match pays path.length with
      | some p => cache.leaf p (hash p) ∧
          cache.node (pairUp compress i x s) (hash p)
            (compress (pairUp compress i x s) (hash p)) ∧
          ClimbCached pays (i / 2) (compress (pairUp compress i x s) (hash p)) path
      | none => ClimbCached pays (i / 2) (pairUp compress i x s) path

/-- **Opened climbs are extracted.** In an injective cache, a cached climb through `t ≤ K` levels
from `x` at index `i` that ends at `root`, injecting exactly at the injecting depths below its top,
makes `x` the extracted node `i` at depth `t` and every injected payload the extracted payload at
its depth. -/
theorem extract_of_climb (hinj : cache.Injective) (inj : ℕ → Bool) (K : ℕ) (root : Digest)
    (pays : ℕ → Option Payload) :
    ∀ (path : List Digest) (i : ℕ) (x : Digest), path.length ≤ K →
      (∀ d < path.length, inj d = (pays d).isSome) →
      ClimbCached cache hash compress pays i x path →
      climb hash compress pays i x path = root →
      nodeAt cache inj path.length i root = some x ∧
        ∀ d < path.length, ∀ p, pays d = some p →
          extract cache inj K d (i >>> (path.length - d)) root = some p
  | [], i, x, _, _, _, hc => ⟨by rw [← hc]; rfl, fun d hd ↦ absurd hd (Nat.not_lt_zero _)⟩
  | s :: path, i, x, hK, hinjd, hcached, hc => by
    simp only [List.length_cons] at hK hinjd ⊢
    set z := pairUp compress i x s with hz
    obtain ⟨hzc, hrest⟩ := hcached
    have hchild : (children cache z).map (fun lr ↦ if i % 2 = 0 then lr.1 else lr.2) =
        some x := by
      by_cases hi : i % 2 = 0
      · simp only [hi, ↓reduceIte] at hzc
        rw [children_eq cache hinj _ _ _ hzc]
        simp only [hi, ↓reduceIte, Option.map_some]
      · simp only [hi, ↓reduceIte] at hzc
        rw [children_eq cache hinj _ _ _ hzc]
        simp only [hi, ↓reduceIte, Option.map_some]
    have hidx : ∀ d < path.length, i >>> (path.length + 1 - d) = (i / 2) >>> (path.length - d) :=
      fun d hd ↦ by
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
          ← Nat.pow_succ']
        congr 2
        omega
    rw [climb_cons] at hc
    have hinjr : ∀ d < path.length, inj d = (pays d).isSome := fun d hd ↦ hinjd d (by omega)
    cases hp : pays path.length with
    | none =>
      simp only [hp] at hrest
      simp only [hp, inject] at hc
      obtain ⟨hn, hext⟩ := extract_of_climb hinj inj K root pays path (i / 2) z (by omega)
        hinjr hrest hc
      have hnot : inj path.length = false := by rw [hinjd _ (by omega), hp, Option.isSome_none]
      refine ⟨by simp only [nodeAt, hn, Option.bind_some, hnot, Bool.false_eq_true, ↓reduceIte,
        hchild], fun d hd q hq ↦ ?_⟩
      rcases Nat.lt_or_ge d path.length with hd' | hd'
      · rw [hidx d hd']; exact hext d hd' q hq
      · rw [show d = path.length by omega, hp] at hq; exact absurd hq (by simp)
    | some p =>
      simp only [hp] at hrest
      simp only [hp, inject] at hc
      obtain ⟨hleafc, hzv, hrest'⟩ := hrest
      obtain ⟨hn, hext⟩ := extract_of_climb hinj inj K root pays path (i / 2)
        (compress z (hash p)) (by omega) hinjr hrest' hc
      have hyes : inj path.length = true := by rw [hinjd _ (by omega), hp, Option.isSome_some]
      have hch : children cache (compress z (hash p)) = some (z, hash p) :=
        children_eq cache hinj _ _ _ hzv
      refine ⟨by simp only [nodeAt, hn, Option.bind_some, hyes, ↓reduceIte, hch, Option.map_some,
        hchild], fun d hd q hq ↦ ?_⟩
      rcases Nat.lt_or_ge d path.length with hd' | hd'
      · rw [hidx d hd']; exact hext d hd' q hq
      · obtain rfl : d = path.length := by omega
        rw [hp, Option.some.injEq] at hq
        subst hq
        rw [show path.length + 1 - path.length = 1 by omega, Nat.shiftRight_one]
        simp only [extract, hn, Option.bind_some, show path.length ≠ K by omega, ↓reduceIte, hch,
          Option.map_some]
        exact pick_leaf_eq cache hinj _ _ hleafc

/-- **Climbing out of the cache.** If every uncached query is answered `dstar`, and a compression
involving `dstar` gives `dstar`, a climb that does not end at `dstar` starts off `dstar` and makes
only cached queries. -/
theorem climbCached_of_fresh (dstar : Digest)
    (hnode : ∀ a b, compress a b ≠ dstar → cache.node a b (compress a b))
    (hleaf : ∀ p, hash p ≠ dstar → cache.leaf p (hash p))
    (hstuck : ∀ a b, (a = dstar ∨ b = dstar) → compress a b = dstar)
    (pays : ℕ → Option Payload) :
    ∀ (i : ℕ) (x : Digest) (path : List Digest), climb hash compress pays i x path ≠ dstar →
      x ≠ dstar ∧ ClimbCached cache hash compress pays i x path
  | _, x, [], h => ⟨h, trivial⟩
  | i, x, s :: path, h => by
    rw [climb_cons] at h
    set z := pairUp compress i x s with hz
    have hx : z ≠ dstar → x ≠ dstar := fun hzd hxd ↦ hzd (by
      rw [hz, pairUp]
      split
      · exact hstuck _ _ (Or.inl hxd)
      · exact hstuck _ _ (Or.inr hxd))
    have hzc : z ≠ dstar → (if i % 2 = 0 then cache.node x s z else cache.node s x z) :=
      fun hzd ↦ by
      by_cases hi : i % 2 = 0
      · simp only [hi, ↓reduceIte]
        have : z = compress x s := by simp only [hz, pairUp, hi, ↓reduceIte]
        rw [this] at hzd ⊢; exact hnode _ _ hzd
      · simp only [hi, ↓reduceIte]
        have : z = compress s x := by simp only [hz, pairUp, hi, ↓reduceIte]
        rw [this] at hzd ⊢; exact hnode _ _ hzd
    cases hp : pays path.length with
    | none =>
      simp only [hp, inject] at h
      obtain ⟨hzd, hrest⟩ := climbCached_of_fresh dstar hnode hleaf hstuck pays _ _ path h
      refine ⟨hx hzd, hzc hzd, ?_⟩
      simp only [hp]
      exact hrest
    | some p =>
      simp only [hp, inject] at h
      obtain ⟨hzv, hrest⟩ := climbCached_of_fresh dstar hnode hleaf hstuck pays _ _ path h
      have hzd : z ≠ dstar := fun e ↦ hzv (hstuck _ _ (Or.inl e))
      have hvd : hash p ≠ dstar := fun e ↦ hzv (hstuck _ _ (Or.inr e))
      refine ⟨hx hzd, hzc hzd, ?_⟩
      simp only [hp]
      exact ⟨hleaf _ hvd, hnode _ _ hzv, hrest⟩

end Climb

end MixedMerkleTree
