/-
Copyright (c) 2026 Gregor Mitscha-Baude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

module

public import Mathlib.Data.Nat.Bitwise

/-!
# Merkle trees with injected payloads

A perfect binary Merkle tree of height `K` whose leaves hash payloads, and whose inner levels may
inject further payloads: a node at an injecting depth compresses the compression of its children
with the hash of its own payload. This is the shape of a commitment to several matrices of
different heights under one root (Plonky3's `MerkleTreeMmcs`): the rows of the tallest matrices are
the leaves' payloads, and the rows of a shorter matrix are injected at the depth of its height. A
commitment is a cap: the `2 ^ h` nodes at depth `h`; the root is the cap of height `0`.

The leaf hash `hash : Payload → Digest` and the compression `compress : Digest → Digest → Digest`
are pure functions, as in the `…WithHash` layer of `InductiveMerkleTree`.

* `node K leaves inj l i`: the node at height `l` and index `i` of the tree of height `K` with the
  leaf payloads `leaves` and the injections `inj` (`inj t = some rows` if depth `t` injects, the
  payload of node `i` being `rows i`).
* `cap K leaves inj h`: the `2 ^ h` nodes at depth `h`.
* `climb pays i x path`: a single opening's walk up from `x` at index `i` through the siblings
  `path`, listed from the bottom up, compressing on the side of the index's bits and injecting the
  hash of `p` into the node at depth `d` below the walk's top wherever `pays d = some p`.
* `climb_node`: an honest opening climbs from a leaf to the node above it.
* `climb_binding`: two openings at one index that climb to one digest under one injection
  schedule open the same payloads, or exhibit a collision of `hash` or of `compress`.
-/

public section

namespace MixedMerkleTree

universe u v

variable {Payload : Type u} {Digest : Type v}

section Defs

variable (hash : Payload → Digest) (compress : Digest → Digest → Digest)

/-- Compress `x` at index `i` with its sibling `s`: `x` on the left at an even index. -/
@[expose]
def pairUp (i : ℕ) (x s : Digest) : Digest :=
  if i % 2 = 0 then compress x s else compress s x

/-- A node after its level's injection: compressed with the hash of the payload, if any. -/
@[expose]
def inject : Option Payload → Digest → Digest
  | some p, z => compress z (hash p)
  | none, z => z

/-- The node at height `l` and index `i` of the tree of height `K`: a leaf hashes its payload
`leaves i`, an inner node compresses its children and, if its depth `K - l` injects, compresses the
result with the hash of its payload. -/
@[expose]
def node (K : ℕ) (leaves : ℕ → Payload) (inj : ℕ → Option (ℕ → Payload)) : ℕ → ℕ → Digest
  | 0, i => hash (leaves i)
  | l + 1, i => inject hash compress ((inj (K - (l + 1))).map (· i))
      (compress (node K leaves inj l (2 * i)) (node K leaves inj l (2 * i + 1)))

/-- The cap of height `h`: the `2 ^ h` nodes at depth `h`. -/
@[expose]
def cap (K : ℕ) (leaves : ℕ → Payload) (inj : ℕ → Option (ℕ → Payload)) (h : ℕ) : List Digest :=
  (List.range (2 ^ h)).map (node hash compress K leaves inj (K - h))

/-- Climb from `x` at index `i` through the siblings `path`, from the bottom up, injecting the hash
of `p` into the node at depth `d` below the top wherever `pays d = some p`. -/
@[expose]
def climb (pays : ℕ → Option Payload) : ℕ → Digest → List Digest → Digest
  | _, x, [] => x
  | i, x, s :: path =>
    climb pays (i / 2) (inject hash compress (pays path.length) (pairUp compress i x s)) path

/-- The siblings of the honest opening of leaf `i`, `n` of them from the bottom up. -/
@[expose]
def siblings (K : ℕ) (leaves : ℕ → Payload) (inj : ℕ → Option (ℕ → Payload)) (i n : ℕ) :
    List Digest :=
  (List.range n).map fun l ↦ node hash compress K leaves inj l ((i >>> l) ^^^ 1)

/-- The injected payloads of the honest opening of leaf `i` through `n` levels, by depth below its
top. -/
@[expose]
def pays (K : ℕ) (inj : ℕ → Option (ℕ → Payload)) (i n : ℕ) (d : ℕ) : Option Payload :=
  (inj (K - (n - d))).map (· (i >>> (n - d)))

end Defs

section Lemmas

variable (hash : Payload → Digest) (compress : Digest → Digest → Digest)

@[simp]
theorem climb_nil (pays : ℕ → Option Payload) (i : ℕ) (x : Digest) :
    climb hash compress pays i x [] = x := rfl

theorem climb_cons (pays : ℕ → Option Payload) (i : ℕ) (x s : Digest) (path : List Digest) :
    climb hash compress pays i x (s :: path) =
      climb hash compress pays (i / 2)
        (inject hash compress (pays path.length) (pairUp compress i x s)) path := rfl

/-- A climb through `p ++ q` climbs through `p` to the node it reaches, then through `q`. -/
theorem climb_append (pays : ℕ → Option Payload) :
    ∀ (i : ℕ) (x : Digest) (p q : List Digest),
      climb hash compress pays i x (p ++ q) =
        climb hash compress pays (i >>> p.length)
          (climb hash compress (fun d ↦ pays (d + q.length)) i x p) q
  | i, x, [], q => by simp only [List.nil_append, List.length_nil, Nat.shiftRight_zero, climb_nil]
  | i, x, s :: p, q => by
    rw [List.cons_append, climb_cons, climb_append pays (i / 2), climb_cons, List.length_cons]
    rw [List.length_append]
    congr 1
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      Nat.pow_succ']

/-- A climb reads the payloads only at the depths below its top. -/
theorem climb_congr {pays pays' : ℕ → Option Payload} :
    ∀ (i : ℕ) (x : Digest) (path : List Digest), (∀ d < path.length, pays d = pays' d) →
      climb hash compress pays i x path = climb hash compress pays' i x path
  | _, _, [], _ => rfl
  | i, x, s :: path, h => by
    rw [climb_cons, climb_cons, h path.length (by simp only [List.length_cons]; omega)]
    exact climb_congr _ _ path fun d hd ↦ h d (by simp only [List.length_cons]; omega)

/-- A climb reads only the bits of the index below its length. -/
theorem climb_mod (pays : ℕ → Option Payload) :
    ∀ (i : ℕ) (x : Digest) (path : List Digest),
      climb hash compress pays i x path = climb hash compress pays (i % 2 ^ path.length) x path
  | _, _, [] => rfl
  | i, x, s :: path => by
    have h2 : i % 2 ^ (path.length + 1) % 2 = i % 2 :=
      Nat.mod_mod_of_dvd i (Nat.dvd_of_mod_eq_zero (by rw [Nat.pow_succ, Nat.mul_mod_left]))
    have hd : i % 2 ^ (path.length + 1) / 2 = i / 2 % 2 ^ path.length := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    simp only [climb_cons, List.length_cons, pairUp, h2, hd]
    rw [climb_mod pays (i / 2), climb_mod pays (i / 2 % 2 ^ path.length), Nat.mod_mod]

/-- `x ^^^ 1` flips the lowest bit. -/
theorem xor_one_eq (x : ℕ) : x ^^^ 1 = 2 * (x / 2) + (x + 1) % 2 := by
  have h1 : (x ^^^ 1) / 2 = x / 2 := by
    rw [Nat.xor_div_two]; simp only [Nat.reduceDiv, Nat.xor_zero]
  have h2 : (x ^^^ 1) % 2 = (x + 1) % 2 := by
    have := Nat.xor_mod_two_pow (a := x) (b := 1) (n := 1)
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;>
      simp only [Nat.pow_one, h, Nat.one_mod, Nat.reduceXor] at this <;> omega
  have := Nat.div_add_mod (x ^^^ 1) 2
  omega

/-- A value paired up with the value at its sibling index is the compression of the pair of
values under their parent. -/
theorem pairUp_xor_one (g : ℕ → Digest) (i : ℕ) :
    pairUp compress i (g i) (g (i ^^^ 1)) = compress (g (2 * (i / 2))) (g (2 * (i / 2) + 1)) := by
  have hx := xor_one_eq i
  have hdm := Nat.div_add_mod i 2
  unfold pairUp
  by_cases h : i % 2 = 0
  · simp only [h, ↓reduceIte]
    rw [show i ^^^ 1 = 2 * (i / 2) + 1 by omega, show 2 * (i / 2) = i by omega]
  · simp only [h, ↓reduceIte]
    rw [show i ^^^ 1 = 2 * (i / 2) by omega, show 2 * (i / 2) + 1 = i by omega]

/-- **Honest openings climb to their node.** From the node at height `l` above leaf `i`, the honest
siblings of the next `n` levels and their injected payloads climb to the node at height `l + n`. -/
theorem climb_node (K : ℕ) (leaves : ℕ → Payload) (inj : ℕ → Option (ℕ → Payload)) (i : ℕ) :
    ∀ n l : ℕ,
      climb hash compress (pays K inj i (l + n)) (i >>> l)
          (node hash compress K leaves inj l (i >>> l))
          ((List.range n).map fun j ↦
            node hash compress K leaves inj (l + j) ((i >>> (l + j)) ^^^ 1)) =
        node hash compress K leaves inj (l + n) (i >>> (l + n))
  | 0, l => by simp only [List.range_zero, List.map_nil, climb_nil, Nat.add_zero]
  | n + 1, l => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, climb_cons, List.length_map,
      List.length_range]
    have hstep : inject hash compress (pays K inj i (l + (n + 1)) n)
        (pairUp compress (i >>> l) (node hash compress K leaves inj l (i >>> l))
          (node hash compress K leaves inj (l + 0) ((i >>> (l + 0)) ^^^ 1))) =
        node hash compress K leaves inj (l + 1) (i >>> (l + 1)) := by
      simp only [Nat.add_zero]
      rw [pairUp_xor_one compress (node hash compress K leaves inj l), node, pays,
        show l + (n + 1) - n = l + 1 by omega, Nat.shiftRight_succ, Nat.shiftRight_eq_div_pow]
    rw [hstep, Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_succ]
    have := climb_node K leaves inj i n (l + 1)
    rw [show l + 1 + n = l + (n + 1) by omega] at this
    rw [← this]
    congr 1
    refine List.map_congr_left fun j _ ↦ ?_
    simp only [Function.comp_apply, show l + (j + 1) = l + 1 + j by omega]

/-- **Honest openings verify.** The honest opening of leaf `i < 2 ^ K` climbs to its entry of the
cap of height `h ≤ K`. -/
theorem climb_cap (K : ℕ) (leaves : ℕ → Payload) (inj : ℕ → Option (ℕ → Payload)) (h i : ℕ)
    (hh : h ≤ K) (hi : i < 2 ^ K) :
    climb hash compress (pays K inj i (K - h)) i (hash (leaves i))
        (siblings hash compress K leaves inj i (K - h)) =
      (cap hash compress K leaves inj h).getD (i >>> (K - h)) (hash (leaves i)) := by
  have := climb_node hash compress K leaves inj i (K - h) 0
  simp only [Nat.zero_add, Nat.shiftRight_zero, node] at this
  have hlt : i >>> (K - h) < 2 ^ h := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      Nat.add_sub_cancel' hh]
    exact hi
  rw [siblings, this, cap, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hlt, Option.map_some, Option.getD_some]

/-- Two distinct payloads with one hash. -/
@[expose]
def HashCollision : Prop :=
  ∃ p p' : Payload, p ≠ p' ∧ hash p = hash p'

/-- Two distinct pairs with one compression. -/
@[expose]
def CompressCollision : Prop :=
  ∃ a b a' b' : Digest, (a, b) ≠ (a', b') ∧ compress a b = compress a' b'

/-- **Binding.** Two climbs at one index through as many siblings, injecting at the same depths,
that end at one digest start at one digest and inject the same payloads, or give a collision of
`hash` or of `compress`. -/
theorem climb_binding {pays₁ pays₂ : ℕ → Option Payload} :
    ∀ (i : ℕ) (x₁ x₂ : Digest) (path₁ path₂ : List Digest), path₁.length = path₂.length →
      (∀ d < path₁.length, (pays₁ d).isSome = (pays₂ d).isSome) →
      climb hash compress pays₁ i x₁ path₁ = climb hash compress pays₂ i x₂ path₂ →
      (x₁ = x₂ ∧ ∀ d < path₁.length, pays₁ d = pays₂ d) ∨ HashCollision hash ∨
        CompressCollision compress
  | _, x₁, x₂, [], [], _, _, h => Or.inl ⟨h, fun d hd ↦ absurd hd (Nat.not_lt_zero _)⟩
  | _, _, _, [], _ :: _, hl, _, _ => absurd hl (by simp only [List.length_nil, List.length_cons,
      Nat.zero_ne_add_one, not_false_eq_true])
  | _, _, _, _ :: _, [], hl, _, _ => absurd hl (by simp only [List.length_nil, List.length_cons,
      Nat.add_one_ne_zero, not_false_eq_true])
  | i, x₁, x₂, s₁ :: path₁, s₂ :: path₂, hl, hs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [climb_cons, climb_cons] at h
    rcases climb_binding (i / 2) _ _ path₁ path₂ hl
        (fun d hd ↦ hs d (by simp only [List.length_cons]; omega)) h with
      ⟨hz, hp⟩ | hc | hc
    · have hsome := hs path₁.length (by simp only [List.length_cons]; omega)
      -- The nodes below the injection agree, or a collision.
      have hpair : (pairUp compress i x₁ s₁ = pairUp compress i x₂ s₂ ∧
          pays₁ path₁.length = pays₂ path₁.length) ∨ HashCollision hash ∨
            CompressCollision compress := by
        rw [hl] at hz ⊢
        rw [hl] at hsome
        cases h₁ : pays₁ path₂.length <;> cases h₂ : pays₂ path₂.length <;>
          simp only [h₁, h₂, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
            reduceCtorEq] at hsome
        · simp only [h₁, h₂, inject] at hz
          exact Or.inl ⟨hz, rfl⟩
        · rename_i p₁ p₂
          simp only [h₁, h₂, inject] at hz
          by_cases hc : (pairUp compress i x₁ s₁, hash p₁) = (pairUp compress i x₂ s₂, hash p₂)
          · rw [Prod.mk.injEq] at hc
            by_cases hp : p₁ = p₂
            · exact Or.inl ⟨hc.1, by rw [hp]⟩
            · exact Or.inr (Or.inl ⟨p₁, p₂, hp, hc.2⟩)
          · exact Or.inr (Or.inr ⟨_, _, _, _, hc, hz⟩)
      rcases hpair with ⟨hpu, hpe⟩ | hc | hc
      · have hpays : ∀ d < (s₁ :: path₁).length, pays₁ d = pays₂ d := fun d hd ↦ by
          simp only [List.length_cons] at hd
          rcases Nat.lt_or_ge d path₁.length with hd' | hd'
          · exact hp d hd'
          · rw [show d = path₁.length by omega]; exact hpe
        unfold pairUp at hpu
        by_cases hi : i % 2 = 0
        · simp only [hi, ↓reduceIte] at hpu
          by_cases hc : (x₁, s₁) = (x₂, s₂)
          · exact Or.inl ⟨(Prod.mk.inj hc).1, hpays⟩
          · exact Or.inr (Or.inr ⟨_, _, _, _, hc, hpu⟩)
        · simp only [hi, ↓reduceIte] at hpu
          by_cases hc : (s₁, x₁) = (s₂, x₂)
          · exact Or.inl ⟨(Prod.mk.inj hc).2, hpays⟩
          · exact Or.inr (Or.inr ⟨_, _, _, _, hc, hpu⟩)
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

end Lemmas

end MixedMerkleTree
