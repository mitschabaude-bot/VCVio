/-
Copyright (c) 2026 Gregor Mitscha-Baude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

module

public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Sort
public import VCVio.CryptoFoundations.MerkleTree.Mixed.Defs

/-!
# Pruned multi-openings of Merkle trees with injected payloads

Several leaves of one tree (`MixedMerkleTree.node`) opened at once, with one list of siblings that
holds every sibling no opened leaf's path recomputes (Plonky3's `verify_batch_pruned`):

* The frontier starts at the distinct indices, sorted, each led by the first query opening it
  (`frontier`). One `level` groups the frontier's nodes `(index, lead, digest)` by parent: a parent
  of two nodes compresses them, a parent of one compresses it with the next sibling of the list on
  the other side. A `walk` repeats this level by level, injecting into each parent the hash of its
  lead's payload at injecting depths. A sibling read past the end of the list is `fill`.
* `prune`: the siblings a walk takes, read off the opened leaves' full paths. `siblingCount`
  counts them; `length_prune` shows `prune` provides exactly that many.
* `exists_climb_of_walk`: every query below a node the walk ends at climbs (`climb`) from its leaf
  to that node's digest, when queries at one index share their leaf and queries below one node of
  an injecting depth share its payload. So an accepted multi-opening gives every query an accepted
  single opening.
* `walk_prune`: from the honest leaves, with the pruned honest siblings, the walk ends at the
  tree's nodes and takes every sibling.
-/

public section

namespace MixedMerkleTree

universe u v

variable {Payload : Type u} {Digest : Type v}

section Defs

variable (hash : Payload → Digest) (compress : Digest → Digest → Digest) (fill : Digest)

/-- The distinct indices, sorted, each with its lead: the first query opening it. -/
@[expose]
def frontier (indices : List ℕ) : List (ℕ × ℕ) :=
  (indices.dedup.mergeSort (· ≤ ·)).map fun i ↦ (i, indices.idxOf i)

/-- One level of a walk, with the compression in a monad: the frontier's nodes
`(index, lead, digest)`, sorted by index, grouped by parent; the parent of two nodes compresses
them, the parent of one compresses it with the next sibling of `sibs` on the other side. The
parents, each led by its first child's lead, and the siblings left. -/
@[expose]
def levelM {m : Type v → Type*} [Monad m] (compress : Digest → Digest → m Digest) :
    List (ℕ × ℕ × Digest) → List Digest → m (List (ℕ × ℕ × Digest) × List Digest)
  | [], sibs => pure ([], sibs)
  | [(i, q, x)], sibs => do
    let z ← if i % 2 = 0 then compress x (sibs.headD fill) else compress (sibs.headD fill) x
    return ([(i / 2, q, z)], sibs.tail)
  | (i, q, x) :: (j, q', y) :: rest, sibs => do
    if i % 2 = 0 ∧ j = i + 1 then
      let z ← compress x y
      let (ps, sibs) ← levelM compress rest sibs
      return ((i / 2, q, z) :: ps, sibs)
    else
      let z ← if i % 2 = 0 then compress x (sibs.headD fill) else compress (sibs.headD fill) x
      let (ps, sibs) ← levelM compress ((j, q', y) :: rest) sibs.tail
      return ((i / 2, q, z) :: ps, sibs)

/-- One level of a walk, with a pure compression. -/
abbrev level (nodes : List (ℕ × ℕ × Digest)) (sibs : List Digest) :
    List (ℕ × ℕ × Digest) × List Digest :=
  levelM fill (m := Id) compress nodes sibs

/-- The walk over `levels` levels from the frontier `nodes`, injecting into the parents at depth
`d` below the walk's top the hash of their lead `q`'s payload `f q` wherever `pays d = some f`. -/
@[expose]
def walk (pays : ℕ → Option (ℕ → Payload)) :
    ℕ → List (ℕ × ℕ × Digest) → List Digest → List (ℕ × ℕ × Digest) × List Digest
  | 0, nodes, sibs => (nodes, sibs)
  | levels + 1, nodes, sibs =>
    walk pays levels ((level compress fill nodes sibs).1.map fun e ↦
        (e.1, e.2.1, inject hash compress ((pays levels).map (· e.2.1)) e.2.2))
      (level compress fill nodes sibs).2

/-- One level of the frontier's indices, sorted: the parents, and the number of siblings taken. -/
@[expose]
def countLevel : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | [i] => ([i / 2], 1)
  | i :: j :: rest =>
    if i % 2 = 0 ∧ j = i + 1 then
      ((i / 2) :: (countLevel rest).1, (countLevel rest).2)
    else
      ((i / 2) :: (countLevel (j :: rest)).1, (countLevel (j :: rest)).2 + 1)

/-- The number of siblings a walk over `levels` levels from the frontier indices `nodes` takes. -/
@[expose]
def siblingCount : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | levels + 1, nodes => (countLevel nodes).2 + siblingCount levels (countLevel nodes).1

/-- One level of `prune` at height `l`: the parents of the frontier `nodes`, each led by its first
child's lead, and the siblings taken, from the leads' full paths `paths`. -/
@[expose]
def pruneLevel (paths : List (List Digest)) (l : ℕ) :
    List (ℕ × ℕ) → List (ℕ × ℕ) × List Digest
  | [] => ([], [])
  | [(i, q)] => ([(i / 2, q)], [(paths.getD q []).getD l fill])
  | (i, q) :: (j, q') :: rest =>
    if i % 2 = 0 ∧ j = i + 1 then
      ((i / 2, q) :: (pruneLevel paths l rest).1, (pruneLevel paths l rest).2)
    else
      ((i / 2, q) :: (pruneLevel paths l ((j, q') :: rest)).1,
        (paths.getD q []).getD l fill :: (pruneLevel paths l ((j, q') :: rest)).2)

/-- The siblings a walk over `levels` levels from the frontier `nodes` at height `l` takes, read
off the queries' full paths `paths`. -/
@[expose]
def pruneWalk (paths : List (List Digest)) : ℕ → ℕ → List (ℕ × ℕ) → List Digest
  | 0, _, _ => []
  | levels + 1, l, nodes =>
    (pruneLevel fill paths l nodes).2 ++
      pruneWalk paths levels (l + 1) (pruneLevel fill paths l nodes).1

/-- The pruned siblings of the openings at `indices` with full paths `paths`, from the bottom up,
over `levels` levels. -/
@[expose]
def prune (levels : ℕ) (indices : List ℕ) (paths : List (List Digest)) : List Digest :=
  pruneWalk fill paths levels 0 (frontier indices)

end Defs

section LevelEqns

variable (compress : Digest → Digest → Digest) (fill : Digest)

theorem level_nil (sibs : List Digest) : level compress fill [] sibs = ([], sibs) := rfl

theorem level_single (i q : ℕ) (x : Digest) (sibs : List Digest) :
    level compress fill [(i, q, x)] sibs =
      ([(i / 2, q, pairUp compress i x (sibs.headD fill))], sibs.tail) := by
  simp only [level, levelM, pairUp]
  split <;> rfl

theorem level_cons_cons (i q j q' : ℕ) (x y : Digest) (rest : List (ℕ × ℕ × Digest))
    (sibs : List Digest) :
    level compress fill ((i, q, x) :: (j, q', y) :: rest) sibs =
      if i % 2 = 0 ∧ j = i + 1 then
        ((i / 2, q, compress x y) :: (level compress fill rest sibs).1,
          (level compress fill rest sibs).2)
      else
        ((i / 2, q, pairUp compress i x (sibs.headD fill)) ::
          (level compress fill ((j, q', y) :: rest) sibs.tail).1,
          (level compress fill ((j, q', y) :: rest) sibs.tail).2) := by
  simp only [level, levelM, pairUp]
  split
  · rfl
  · split <;> rfl

end LevelEqns

/-- A walk reads the injected payloads only at the depths below its top. -/
theorem walk_congr (hash : Payload → Digest) (compress : Digest → Digest → Digest) (fill : Digest)
    {pays pays' : ℕ → Option (ℕ → Payload)} :
    ∀ (levels : ℕ) (nodes : List (ℕ × ℕ × Digest)) (sibs : List Digest),
      (∀ d < levels, pays d = pays' d) →
      walk hash compress fill pays levels nodes sibs =
        walk hash compress fill pays' levels nodes sibs
  | 0, _, _, _ => rfl
  | levels + 1, nodes, sibs, h => by
    rw [walk, walk, h levels (Nat.lt_succ_self _)]
    exact walk_congr hash compress fill levels _ _ fun d hd ↦ h d (by omega)

/-! ### The frontier -/

/-- The frontier's indices are the distinct indices, sorted. -/
theorem pairwise_frontier (indices : List ℕ) :
    (frontier indices).Pairwise fun a b ↦ a.1 < b.1 := by
  unfold frontier
  rw [List.pairwise_map]
  have hle := List.pairwise_mergeSort (le := fun a b : ℕ ↦ decide (a ≤ b))
    (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) indices.dedup
  have hnd : (indices.dedup.mergeSort fun a b ↦ decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_dedup indices)
  refine (hle.and hnd).imp fun {a b} ⟨h1, h2⟩ ↦ ?_
  simp only [decide_eq_true_eq] at h1
  omega

theorem mem_frontier {indices : List ℕ} {e : ℕ × ℕ} :
    e ∈ frontier indices ↔ e.1 ∈ indices ∧ e.2 = indices.idxOf e.1 := by
  unfold frontier
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    rw [List.mem_mergeSort, List.mem_dedup] at hi
    exact ⟨hi, rfl⟩
  · rintro ⟨h1, h2⟩
    refine List.mem_map.mpr ⟨e.1, by rw [List.mem_mergeSort, List.mem_dedup]; exact h1, ?_⟩
    rw [← h2]

/-- A frontier entry's lead opens its index. -/
theorem lead_of_mem_frontier {indices : List ℕ} {e : ℕ × ℕ} (he : e ∈ frontier indices) :
    ∃ h : e.2 < indices.length, indices[e.2] = e.1 := by
  obtain ⟨hi, hq⟩ := mem_frontier.mp he
  have hql : indices.idxOf e.1 < indices.length := List.idxOf_lt_length_of_mem hi
  exact ⟨hq ▸ hql, by simp only [hq]; exact List.getElem_idxOf hql⟩

/-- In a list sorted strictly by index, two entries of one index are equal. -/
theorem eq_of_pairwise_lt {α : Type*} {nodes : List (ℕ × α)}
    (hs : nodes.Pairwise fun a b ↦ a.1 < b.1) {a b : ℕ × α} (ha : a ∈ nodes)
    (hb : b ∈ nodes) (h : a.1 = b.1) : a = b := by
  induction nodes with
  | nil => exact absurd ha List.not_mem_nil
  | cons c rest ih =>
    rw [List.pairwise_cons] at hs
    rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
    · rw [ha, hb]
    · rw [ha] at h; have := hs.1 b hb; omega
    · rw [hb] at h; have := hs.1 a ha; omega
    · exact ih hs.2 ha hb

/-! ### One level -/

section Level

variable (hash : Payload → Digest) (compress : Digest → Digest → Digest) (fill : Digest)

/-- One level of a walk on a sorted frontier: the parents are sorted, each the parent of a node and
led by its lead, and every node has its parent among them, whose digest compresses the node's with
a sibling on the node's side. -/
theorem level_struct : ∀ (nodes : List (ℕ × ℕ × Digest)) (sibs : List Digest),
    (nodes.Pairwise fun a b ↦ a.1 < b.1) →
    ((level compress fill nodes sibs).1.Pairwise fun a b ↦ a.1 < b.1) ∧
      (∀ e' ∈ (level compress fill nodes sibs).1, ∃ e ∈ nodes, e'.1 = e.1 / 2 ∧
        e'.2.1 = e.2.1) ∧
      ∀ e ∈ nodes, ∃ e' ∈ (level compress fill nodes sibs).1, e'.1 = e.1 / 2 ∧
        ∃ s, e'.2.2 = pairUp compress e.1 e.2.2 s
  | [], sibs, _ => by
    simp only [level_nil, List.Pairwise.nil, List.not_mem_nil, false_and, exists_false,
      imp_self, implies_true, and_self]
  | [(i, q, x)], sibs, _ => by
    rw [level_single]
    refine ⟨List.pairwise_singleton _ _, fun e' he' ↦ ?_, fun e he ↦ ?_⟩
    · rw [List.mem_singleton] at he'
      exact ⟨(i, q, x), List.mem_singleton_self _, by rw [he'], by rw [he']⟩
    · rw [List.mem_singleton] at he
      subst he
      exact ⟨_, List.mem_singleton_self _, rfl, sibs.headD fill, rfl⟩
  | (i, q, x) :: (j, q', y) :: rest, sibs, hs => by
    have hij : i < j := List.rel_of_pairwise_cons hs List.mem_cons_self
    have hrest : ∀ e ∈ rest, j < e.1 :=
      fun e he ↦ List.rel_of_pairwise_cons (List.Pairwise.of_cons hs) he
    have hsrest : rest.Pairwise fun a b ↦ a.1 < b.1 := (hs.of_cons).of_cons
    have hsj : ((j, q', y) :: rest).Pairwise fun a b ↦ a.1 < b.1 := hs.of_cons
    rw [level_cons_cons]
    split
    · rename_i hpair
      obtain ⟨hi2, rfl⟩ := hpair
      obtain ⟨ihs, ihp, ihc⟩ := level_struct rest sibs hsrest
      have habove : ∀ e' ∈ (level compress fill rest sibs).1, i / 2 < e'.1 := by
        intro e' he'
        obtain ⟨e, he, h, -⟩ := ihp e' he'
        have := hrest e he
        rw [h]
        omega
      refine ⟨List.Pairwise.cons (fun e' he' ↦ habove e' he') ihs, fun e' he' ↦ ?_, fun e he ↦ ?_⟩
      · rcases List.mem_cons.mp he' with rfl | he'
        · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
        · obtain ⟨e, he, h⟩ := ihp e' he'
          exact ⟨e, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he), h⟩
      · rcases List.mem_cons.mp he with rfl | he
        · exact ⟨_, List.mem_cons_self, rfl, y, by simp only [pairUp, hi2, ↓reduceIte]⟩
        rcases List.mem_cons.mp he with rfl | he
        · refine ⟨_, List.mem_cons_self, by dsimp only; omega, x, ?_⟩
          have hodd : (i + 1) % 2 ≠ 0 := by omega
          simp only [pairUp, hodd, ↓reduceIte]
        · obtain ⟨e', he', h⟩ := ihc e he
          exact ⟨e', List.mem_cons_of_mem _ he', h⟩
    · rename_i hpair
      obtain ⟨ihs, ihp, ihc⟩ := level_struct ((j, q', y) :: rest) sibs.tail hsj
      have hjp : i / 2 < j / 2 := by omega
      have habove : ∀ e' ∈ (level compress fill ((j, q', y) :: rest) sibs.tail).1,
          i / 2 < e'.1 := by
        intro e' he'
        obtain ⟨e, he, h, -⟩ := ihp e' he'
        rw [h]
        rcases List.mem_cons.mp he with rfl | he
        · exact hjp
        · have := hrest e he
          omega
      refine ⟨List.Pairwise.cons (fun e' he' ↦ habove e' he') ihs, fun e' he' ↦ ?_, fun e he ↦ ?_⟩
      · rcases List.mem_cons.mp he' with rfl | he'
        · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
        · obtain ⟨e, he, h⟩ := ihp e' he'
          exact ⟨e, List.mem_cons_of_mem _ he, h⟩
      · rcases List.mem_cons.mp he with rfl | he
        · exact ⟨_, List.mem_cons_self, rfl, sibs.headD fill, rfl⟩
        · obtain ⟨e', he', h⟩ := ihc e he
          exact ⟨e', List.mem_cons_of_mem _ he', h⟩

end Level

/-! ### Restoring the paths -/

section Restore

variable (hash : Payload → Digest) (compress : Digest → Digest → Digest) (fill : Digest)
  (indices : List ℕ) (leaf : ℕ → Digest) (pays : ℕ → Option (ℕ → Payload)) (L : ℕ)

/-- The payloads query `r` injects, by depth below the walk's top. -/
@[expose]
def paysOf (r : ℕ) (d : ℕ) : Option Payload := (pays d).map (· r)

/-- A frontier at height `l` of a walk over `L` levels: sorted by index, every query below one of
its nodes, every node led by a query below it, and every query below a node climbing from its leaf
to the node's digest. -/
structure Frontier (l : ℕ) (nodes : List (ℕ × ℕ × Digest)) : Prop where
  sorted : nodes.Pairwise fun a b ↦ a.1 < b.1
  covers : ∀ r (hr : r < indices.length), ∃ e ∈ nodes, e.1 = indices[r] >>> l
  leads : ∀ e ∈ nodes, ∃ h : e.2.1 < indices.length, indices[e.2.1] >>> l = e.1
  climbs : ∀ e ∈ nodes, ∀ r (hr : r < indices.length), indices[r] >>> l = e.1 →
    ∃ p : List Digest, p.length = l ∧
      climb hash compress (fun d ↦ paysOf pays r (d + (L - l))) indices[r] (leaf r) p = e.2.2

variable {hash compress fill indices leaf pays L}

/-- One level of a walk from a frontier at height `l < L`: a frontier one level up, when queries
below one parent inject the same payload. -/
theorem frontier_level (l : ℕ) (hl : l < L) (nodes : List (ℕ × ℕ × Digest)) (sibs : List Digest)
    (h : Frontier hash compress indices leaf pays L l nodes)
    (hpays : ∀ r q (hr : r < indices.length) (hq : q < indices.length),
      indices[r] >>> (l + 1) = indices[q] >>> (l + 1) →
      paysOf pays r (L - (l + 1)) = paysOf pays q (L - (l + 1))) :
    Frontier hash compress indices leaf pays L (l + 1)
      ((level compress fill nodes sibs).1.map fun e ↦
        (e.1, e.2.1, inject hash compress ((pays (L - (l + 1))).map (· e.2.1)) e.2.2)) := by
  obtain ⟨hs, hpar, hc⟩ := level_struct compress fill nodes sibs h.sorted
  set ps := (level compress fill nodes sibs).1
  have hparent : ∀ r (hr : r < indices.length), ∃ e ∈ nodes, e.1 = indices[r] >>> l ∧
      ∃ e' ∈ ps, e'.1 = indices[r] >>> (l + 1) ∧ ∃ s, e'.2.2 = pairUp compress e.1 e.2.2 s := by
    intro r hr
    obtain ⟨e, he, hei⟩ := h.covers r hr
    obtain ⟨e', he', h1, h2⟩ := hc e he
    exact ⟨e, he, hei, e', he', by rw [h1, hei, Nat.shiftRight_succ], h2⟩
  have hlead : ∀ e' ∈ ps, ∃ h : e'.2.1 < indices.length,
      indices[e'.2.1] >>> (l + 1) = e'.1 := by
    intro e' he'
    obtain ⟨e, he, h1, h2⟩ := hpar e' he'
    obtain ⟨hl, hle⟩ := h.leads e he
    rw [h2]
    exact ⟨hl, by rw [Nat.shiftRight_succ, hle, h1]⟩
  refine ⟨List.pairwise_map.mpr hs, fun r hr ↦ ?_, fun e' he' ↦ ?_, fun e' he' r hr hre ↦ ?_⟩
  · obtain ⟨-, -, -, e', he', h1, -⟩ := hparent r hr
    exact ⟨_, List.mem_map_of_mem he', h1⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    exact hlead x hx
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    dsimp only at hre ⊢
    obtain ⟨e, he, hei, e'', he'', hi'', s, hs''⟩ := hparent r hr
    have hee : e'' = x := eq_of_pairwise_lt hs he'' hx (by rw [hi'', hre])
    subst hee
    obtain ⟨p, hp, hpc⟩ := h.climbs e he r hr hei.symm
    obtain ⟨hql, hle⟩ := hlead e'' hx
    refine ⟨p ++ [s], by rw [List.length_append, hp, List.length_singleton], ?_⟩
    rw [climb_append, List.length_singleton, hp]
    have hpc' : climb hash compress (fun d ↦ paysOf pays r (d + 1 + (L - (l + 1)))) indices[r]
        (leaf r) p = e.2.2 := by
      rw [← hpc]
      refine climb_congr hash compress _ _ _ fun d _ ↦ ?_
      rw [show d + 1 + (L - (l + 1)) = d + (L - l) by omega]
    rw [hpc', climb_cons, climb_nil, List.length_nil, Nat.zero_add, hs'', ← hei,
      hpays r e''.2.1 hr hql (by rw [hle, hi''])]
    rfl

/-- **Restoring the paths.** The walk over `L` levels from the queries' leaves ends at nodes that
every query below climbs to from its leaf, when queries at one index share their leaf and queries
below one node of an injecting depth share its payload. -/
theorem exists_climb_of_walk (sibs : List Digest)
    (hleaf : ∀ r q (hr : r < indices.length) (hq : q < indices.length),
      indices[r] = indices[q] → leaf r = leaf q)
    (hpays : ∀ d < L, ∀ r q (hr : r < indices.length) (hq : q < indices.length),
      indices[r] >>> (L - d) = indices[q] >>> (L - d) → paysOf pays r d = paysOf pays q d)
    (r : ℕ) (hr : r < indices.length) :
    ∃ e ∈ (walk hash compress fill pays L
        ((frontier indices).map fun e ↦ (e.1, e.2, leaf e.2)) sibs).1,
      e.1 = indices[r] >>> L ∧ ∃ path : List Digest, path.length = L ∧
        climb hash compress (paysOf pays r) indices[r] (leaf r) path = e.2.2 := by
  -- The walk from a frontier at height `l` over the remaining `L - l` levels.
  have hwalk : ∀ n l (nodes : List (ℕ × ℕ × Digest)) (sibs : List Digest), l + n = L →
      Frontier hash compress indices leaf pays L l nodes →
      Frontier hash compress indices leaf pays L L
        (walk hash compress fill pays n nodes sibs).1 := by
    intro n
    induction n with
    | zero => intro l nodes sibs hn h; rw [Nat.add_zero] at hn; subst hn; exact h
    | succ n ih =>
      intro l nodes sibs hn h
      have hstep := frontier_level (fill := fill) (sibs := sibs) l (by omega) nodes h
        (fun r q hr hq he ↦ hpays (L - (l + 1)) (by omega) r q hr hq
          (by rw [show L - (L - (l + 1)) = l + 1 by omega]; exact he))
      rw [show L - (l + 1) = n by omega] at hstep
      exact ih (l + 1) _ _ (by omega) hstep
  have h0 : Frontier hash compress indices leaf pays L 0
      ((frontier indices).map fun e ↦ (e.1, e.2, leaf e.2)) := by
    refine ⟨?_, fun r' hr' ↦ ?_, fun e he ↦ ?_, fun e he r' hr' hre ↦ ?_⟩
    · rw [List.pairwise_map]
      exact pairwise_frontier indices
    · refine ⟨(indices[r'], indices.idxOf indices[r'], leaf (indices.idxOf indices[r'])), ?_,
        by rw [Nat.shiftRight_zero]⟩
      exact List.mem_map.mpr ⟨(indices[r'], indices.idxOf indices[r']),
        mem_frontier.mpr ⟨List.getElem_mem hr', rfl⟩, rfl⟩
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      obtain ⟨hq, hqi⟩ := lead_of_mem_frontier he'
      exact ⟨hq, by rw [Nat.shiftRight_zero]; exact hqi⟩
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      obtain ⟨hq, hqi⟩ := lead_of_mem_frontier he'
      rw [Nat.shiftRight_zero] at hre
      refine ⟨[], rfl, ?_⟩
      exact hleaf r' e'.2 hr' hq (by rw [hre, hqi])
  have hk := hwalk L 0 _ sibs (Nat.zero_add L) h0
  obtain ⟨e, he, hei⟩ := hk.covers r hr
  obtain ⟨p, hp, hc⟩ := hk.climbs e he r hr hei.symm
  refine ⟨e, he, hei, p, hp, ?_⟩
  rw [← hc]
  refine climb_congr hash compress _ _ _ fun d _ ↦ ?_
  rw [Nat.sub_self, Nat.add_zero]

end Restore

/-! ### Pruning -/

section Prune

variable (fill : Digest)

/-- The parents of `pruneLevel`, each the parent of a node led by the node's lead. -/
theorem pruneLevel_parents (paths : List (List Digest)) (l : ℕ) :
    ∀ ns : List (ℕ × ℕ), ∀ e' ∈ (pruneLevel fill paths l ns).1, ∃ e ∈ ns, e' = (e.1 / 2, e.2)
  | [], e', he' => absurd he' List.not_mem_nil
  | [(i, q)], e', he' => by
    simp only [pruneLevel, List.mem_singleton] at he'
    exact ⟨(i, q), List.mem_singleton_self _, he'⟩
  | (i, q) :: (j, q') :: ns, e', he' => by
    simp only [pruneLevel] at he'
    split at he'
    · rcases List.mem_cons.mp he' with rfl | he'
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨e, he, rfl⟩ := pruneLevel_parents paths l ns e' he'
        exact ⟨e, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he), rfl⟩
    · rcases List.mem_cons.mp he' with rfl | he'
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨e, he, rfl⟩ := pruneLevel_parents paths l ((j, q') :: ns) e' he'
        exact ⟨e, List.mem_cons_of_mem _ he, rfl⟩

/-- `pruneLevel` takes as many siblings, and keeps the same parents, as `countLevel`. -/
theorem pruneLevel_count (paths : List (List Digest)) (l : ℕ) :
    ∀ ns : List (ℕ × ℕ), (pruneLevel fill paths l ns).2.length = (countLevel (ns.map (·.1))).2 ∧
      (pruneLevel fill paths l ns).1.map (·.1) = (countLevel (ns.map (·.1))).1
  | [] => ⟨rfl, rfl⟩
  | [(i, q)] => ⟨rfl, rfl⟩
  | (i, q) :: (j, q') :: ns => by
    simp only [pruneLevel, List.map_cons, countLevel]
    split
    · obtain ⟨h1, h2⟩ := pruneLevel_count paths l ns
      exact ⟨h1, by rw [List.map_cons, h2]⟩
    · obtain ⟨h1, h2⟩ := pruneLevel_count paths l ((j, q') :: ns)
      simp only [List.map_cons] at h1 h2
      exact ⟨by rw [List.length_cons, h1], by rw [List.map_cons, h2]⟩

/-- `pruneWalk` takes the siblings `siblingCount` counts. -/
theorem length_pruneWalk (paths : List (List Digest)) :
    ∀ (levels l : ℕ) (ns : List (ℕ × ℕ)),
      (pruneWalk fill paths levels l ns).length = siblingCount levels (ns.map (·.1))
  | 0, _, _ => rfl
  | levels + 1, l, ns => by
    obtain ⟨h1, h2⟩ := pruneLevel_count fill paths l ns
    simp only [pruneWalk, siblingCount, List.length_append, h1, length_pruneWalk paths levels,
      h2]

/-- `prune` takes the siblings `siblingCount` counts. -/
theorem length_prune (levels : ℕ) (indices : List ℕ) (paths : List (List Digest)) :
    (prune fill levels indices paths).length =
      siblingCount levels ((frontier indices).map (·.1)) :=
  length_pruneWalk fill paths levels 0 _

end Prune

/-! ### Honest multi-openings -/

section Honest

variable (hash : Payload → Digest) (compress : Digest → Digest → Digest) (fill : Digest)
  (N : ℕ → ℕ → Digest)

/-- The nodes `ns` of height `l`, each with its digest `N l i`. -/
@[expose]
def nodesOf (l : ℕ) (ns : List (ℕ × ℕ)) : List (ℕ × ℕ × Digest) :=
  ns.map fun e ↦ (e.1, e.2, N l e.1)

/-- One level of the honest walk: the pruned siblings of the leads' paths take the frontier's
nodes to the pairs of their parents. -/
theorem level_pruneLevel (paths : List (List Digest)) (l : ℕ) :
    ∀ (ns : List (ℕ × ℕ)) (rest : List Digest),
      (∀ e ∈ ns, (paths.getD e.2 []).getD l fill = N l (e.1 ^^^ 1)) →
      level compress fill (nodesOf N l ns) ((pruneLevel fill paths l ns).2 ++ rest) =
        ((pruneLevel fill paths l ns).1.map fun e ↦
          (e.1, e.2, compress (N l (2 * e.1)) (N l (2 * e.1 + 1))), rest)
  | [], rest, _ => rfl
  | [(i, q)], rest, h => by
    simp only [nodesOf, List.map_cons, List.map_nil, pruneLevel, List.singleton_append,
      level_single, List.headD_cons, List.tail_cons]
    rw [h (i, q) (List.mem_singleton_self _), pairUp_xor_one compress (N l)]
  | (i, q) :: (j, q') :: ns, rest, h => by
    have h1 := h (i, q) List.mem_cons_self
    have hj : ∀ e ∈ (j, q') :: ns, (paths.getD e.2 []).getD l fill = N l (e.1 ^^^ 1) :=
      fun e he ↦ h e (List.mem_cons_of_mem _ he)
    have hns : ∀ e ∈ ns, (paths.getD e.2 []).getD l fill = N l (e.1 ^^^ 1) :=
      fun e he ↦ hj e (List.mem_cons_of_mem _ he)
    simp only [nodesOf, List.map_cons]
    rw [level_cons_cons]
    simp only [pruneLevel]
    split
    · rename_i hp
      obtain ⟨he, rfl⟩ := hp
      have := level_pruneLevel paths l ns rest hns
      simp only [nodesOf] at this
      rw [this]
      simp only [List.map_cons]
      rw [show 2 * (i / 2) = i by omega]
    · have := level_pruneLevel paths l ((j, q') :: ns) rest hj
      simp only [nodesOf, List.map_cons] at this
      simp only [List.cons_append, List.headD_cons, List.tail_cons, this, h1,
        pairUp_xor_one compress (N l), List.map_cons]

/-- **The honest walk.** From the frontier `ns` at height `l`, whose leads open the paths of the
tree of nodes `N`, the walk over `levels` levels ends at the nodes `N` of its parents and takes
exactly the pruned siblings, when every node `N` above a query is the pair of its children,
injected with the hash of the query's payload at injecting depths. -/
theorem walk_pruneWalk (indices : List ℕ) (L : ℕ) (pays : ℕ → Option (ℕ → Payload))
    (paths : List (List Digest))
    (hpaths : ∀ q (hq : q < indices.length), ∀ j < L,
      (paths.getD q []).getD j fill = N j ((indices[q] >>> j) ^^^ 1))
    (hN : ∀ l < L, ∀ q (hq : q < indices.length),
      N (l + 1) (indices[q] >>> (l + 1)) =
        inject hash compress ((pays (L - (l + 1))).map (· q))
          (compress (N l (2 * (indices[q] >>> (l + 1))))
            (N l (2 * (indices[q] >>> (l + 1)) + 1)))) :
    ∀ (levels l : ℕ) (ns : List (ℕ × ℕ)) (rest : List Digest),
      l + levels = L → (∀ e ∈ ns, ∃ h : e.2 < indices.length, indices[e.2] >>> l = e.1) →
      ∃ ns' : List (ℕ × ℕ), (∀ e ∈ ns', ∃ h : e.2 < indices.length,
          indices[e.2] >>> L = e.1) ∧
        walk hash compress fill pays levels (nodesOf N l ns)
          (pruneWalk fill paths levels l ns ++ rest) = (nodesOf N L ns', rest)
  | 0, l, ns, rest, hl, hns => ⟨ns, by rw [← hl, Nat.add_zero]; exact hns, by
      rw [← hl, Nat.add_zero]; rfl⟩
  | levels + 1, l, ns, rest, hl, hns => by
    have hlev : ∀ e ∈ ns, (paths.getD e.2 []).getD l fill = N l (e.1 ^^^ 1) := fun e he ↦ by
      obtain ⟨hq, hi⟩ := hns e he
      rw [hpaths e.2 hq l (by omega), hi]
    have hpar : ∀ e ∈ (pruneLevel fill paths l ns).1, ∃ h : e.2 < indices.length,
        indices[e.2] >>> (l + 1) = e.1 := fun e' he' ↦ by
      obtain ⟨e, he, rfl⟩ := pruneLevel_parents fill paths l ns e' he'
      obtain ⟨hq, hi⟩ := hns e he
      exact ⟨hq, by rw [Nat.shiftRight_succ, hi]⟩
    obtain ⟨ns', h1, h2⟩ := walk_pruneWalk indices L pays paths hpaths hN levels (l + 1)
      (pruneLevel fill paths l ns).1 rest (by omega) hpar
    refine ⟨ns', h1, ?_⟩
    rw [← h2, pruneWalk, List.append_assoc, walk,
      level_pruneLevel compress fill N paths l ns _ hlev, List.map_map]
    congr 1
    simp only [nodesOf]
    refine List.map_congr_left fun x hx ↦ ?_
    obtain ⟨hq, hi⟩ := hpar x hx
    simp only [Function.comp_apply]
    rw [← hi, hN l (by omega) x.2 hq, show L - (l + 1) = levels by omega]

/-- **Honest multi-openings verify.** The walk over `L` levels from the leaves `N 0` at the opened
indices, with the pruned siblings of their honest paths, ends at the nodes `N L` above them and
takes every sibling. -/
theorem walk_prune (indices : List ℕ) (L : ℕ) (pays : ℕ → Option (ℕ → Payload))
    (paths : List (List Digest))
    (hpaths : ∀ q (hq : q < indices.length), ∀ j < L,
      (paths.getD q []).getD j fill = N j ((indices[q] >>> j) ^^^ 1))
    (hN : ∀ l < L, ∀ q (hq : q < indices.length),
      N (l + 1) (indices[q] >>> (l + 1)) =
        inject hash compress ((pays (L - (l + 1))).map (· q))
          (compress (N l (2 * (indices[q] >>> (l + 1))))
            (N l (2 * (indices[q] >>> (l + 1)) + 1)))) :
    ∃ ns' : List (ℕ × ℕ), (∀ e ∈ ns', ∃ h : e.2 < indices.length, indices[e.2] >>> L = e.1) ∧
      walk hash compress fill pays L ((frontier indices).map fun e ↦ (e.1, e.2, N 0 e.1))
        (prune fill L indices paths) = (nodesOf N L ns', []) := by
  have := walk_pruneWalk hash compress fill N indices L pays paths hpaths hN L 0 (frontier indices)
    [] (Nat.zero_add L) fun e he ↦ by
      obtain ⟨hq, hqi⟩ := lead_of_mem_frontier he
      exact ⟨hq, by rw [Nat.shiftRight_zero]; exact hqi⟩
  rwa [List.append_nil] at this

end Honest

end MixedMerkleTree
