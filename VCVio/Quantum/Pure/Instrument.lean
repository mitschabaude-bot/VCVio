/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Pure.Norm
public import VCVio.Quantum.Pure.State

/-!
# Kraus branches on pure states

A branch with a single Kraus operator, `ρ ↦ K ρ K†`, sends the pure substate `|ψ⟩⟨ψ|` to the pure
substate `|Kψ⟩⟨Kψ|`. So the probability of the branch is `‖K •ᵥ ψ‖²` (the Born rule), and the state
it leaves is described by the vector `K •ᵥ ψ`. As in the core, this state is unnormalized: when
`‖K •ᵥ ψ‖ > 0` the conditional state is `K •ᵥ ψ / ‖K •ᵥ ψ‖`, and no normalization is performed
here.

These statements are about one Kraus operator per outcome. A branch that sums several Kraus maps,
or a computation that forgets an outcome, can produce a mixed state, and a pure-state argument
about it must track the individual Kraus contributions (`Quantum.MatrixMap.conj`).

## Constructors

* `Quantum.SubInstrument.ofContraction K hK`: the one-outcome subinstrument `ρ ↦ K ρ K†` of an
  operator with `‖K‖ ≤ 1`. It loses probability `‖ψ‖² - ‖K •ᵥ ψ‖²` on `ψ`, and is lossless when
  `K` is an isometry.
* `Quantum.SubInstrument.ofUnitary U`: a unitary gate, the lossless case on one register. Running
  `U` and then `V` is running `V * U`.
* `Quantum.SubInstrument.ofProjective P hP hsum`: the measurement with orthogonal projections
  `P a` summing to the identity, which leaves `P a •ᵥ ψ` on outcome `a`.

## Observation lemmas

For a measurement with finitely many Kraus operators, `∑ a, (K a)† * K a = 1`, the distribution of
the outcome on `|ψ⟩⟨ψ|` gives the event `E` the weight `∑ a ∈ E, ‖K a •ᵥ ψ‖²`
(`Quantum.SubInstrument.outcomeMeasure_ofKraus_ofVector`). The `outcomeMeasure_*_bind_ofVector`
lemmas run a continuation on the unnormalized vector `K a •ᵥ ψ`, whose squared norm already is the
probability of `a`, so a `do` block reduces to vectors one step at a time. Changing the input
vector moves the weight of every event by at most `(‖ψ‖ + ‖φ‖) * ‖ψ - φ‖`
(`Quantum.SubInstrument.abs_outcomeMeasure_real_ofKraus_ofVector_sub_le`).

## Any outcome type, and dependent output systems

The same lemmas hold branch by branch for any subinstrument: if `p.branch a = MatrixMap.conj K`,
then outcome `a` has weight `‖K •ᵥ ψ‖²` and leaves `K •ᵥ ψ`
(`Quantum.SubInstrument.post_ofVector_of_branch_eq_conj`,
`Quantum.SubInstrument.outcomeMeasure_ofVector_singleton_of_branch_eq_conj`). If every branch has
this form, the distribution is the sum of the weighted point masses over all outcomes, with no
finiteness assumption (`*_of_forall_branch_eq_conj`). `Quantum.DSubInstrument` has the same lemmas
when the output system depends on the outcome (`Quantum.DSubInstrument.post_ofKraus_ofVector`).
Lemmas about a single outcome need measurable singletons.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018. Instruments
  and post-measurement states: equations (2.258)–(2.261), p. 112. A complete family of projections
  is pairwise orthogonal: Proposition 2.40, p. 107.
-/

public section

open MeasureTheory
open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator
open Matrix

universe u v w

namespace Quantum

namespace SubInstrument

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {α β : Type*}

/-! ## A single map followed by a continuation -/

/-- On the zero substate every outcome has weight zero. -/
theorem outcomeMeasure_eq_zero_of_matrix_eq_zero [MeasurableSpace α] (p : SubInstrument A B α)
    {ρ : SubState A} (hρ : ρ.matrix = 0) : p.outcomeMeasure ρ = 0 := by
  ext s hs
  simp [outcomeMeasure_apply _ _ hs, hρ]

/-- Each branch of a composite that starts with a single map is the branch of the continuation
after that map. -/
theorem branch_ofMap_bind_apply (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI)
    (k : PUnit → SubInstrument B C β) (b : β) :
    ((ofMap Φ hcp htni).bind k).branch b = (k PUnit.unit).branch b ∘ₗ Φ := by
  rw [branch_bind_apply_univ, Fintype.sum_unique]
  rfl

/-- After the unique outcome of a single map, the substate is the image under the map. -/
theorem matrix_post_ofMap (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI) (ρ : SubState A)
    (u : PUnit) : ((ofMap Φ hcp htni).post ρ u).matrix = Φ ρ.matrix := by
  rw [matrix_post, branch_ofMap]

/-- The post-branch substates of a composite that starts with a single map are those of the
continuation on the image of the substate. -/
theorem post_ofMap_bind (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI)
    (k : PUnit.{v + 1} → SubInstrument B C β) (ρ : SubState A) (b : β) :
    ((ofMap Φ hcp htni).bind k).post ρ b =
      (k PUnit.unit).post ((ofMap Φ hcp htni).post ρ PUnit.unit.{v + 1}) b :=
  SubState.ext <| by
    rw [matrix_post, branch_ofMap_bind_apply, matrix_post, matrix_post_ofMap,
      LinearMap.comp_apply]

/-- The outcome measure of a composite that starts with a single map is the outcome measure of
the continuation on the image of the substate. -/
theorem outcomeMeasure_ofMap_bind [MeasurableSpace β] (Φ : MatrixMap A B) (hcp : Φ.IsCP)
    (htni : Φ.IsTNI) (k : PUnit.{v + 1} → SubInstrument B C β) (ρ : SubState A) :
    ((ofMap Φ hcp htni).bind k).outcomeMeasure ρ =
      (k PUnit.unit).outcomeMeasure ((ofMap Φ hcp htni).post ρ PUnit.unit.{v + 1}) := by
  ext s hs
  rw [outcomeMeasure_apply _ _ hs, outcomeMeasure_apply _ _ hs]
  simp only [branch_ofMap_bind_apply, matrix_post_ofMap, LinearMap.comp_apply]

/-! ## Contractions -/

section ofContraction

variable [DecidableEq A]

/-- The subinstrument with one outcome that applies the Kraus map `ρ ↦ K * ρ * Kᴴ` of a
contraction `K`. On vectors it is the map `ψ ↦ K •ᵥ ψ`; the decrease in squared norm is the
failure weight this step adds. -/
@[expose]
noncomputable def ofContraction (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1) : SubInstrument A B PUnit :=
  ofMap (MatrixMap.conj K) (MatrixMap.isCP_conj K)
    (MatrixMap.isTNI_conj ((posSemidef_one_sub_conjTranspose_mul_self_iff K).mpr hK))

/-- The branch family of the subinstrument of a contraction is its Kraus map at the unique
outcome. -/
@[simp]
theorem branch_ofContraction (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1) :
    (ofContraction K hK).branch = fun _ ↦ MatrixMap.conj K :=
  rfl

/-- The total map of the subinstrument of a contraction is its Kraus map. -/
@[simp]
theorem total_ofContraction (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1) :
    (ofContraction K hK).total = MatrixMap.conj K :=
  total_ofMap ..

/-- The subinstrument of an isometry is lossless. -/
theorem lossless_ofContraction {K : Matrix B A ℂ} (hK : ‖K‖ ≤ 1) (h : Kᴴ * K = 1) :
    (ofContraction K hK).Lossless :=
  lossless_ofMap _ (MatrixMap.isTP_conj h)

/-- The subinstrument of the identity operator returns the unique outcome and leaves the state
unchanged. -/
theorem ofContraction_one (h : ‖(1 : Matrix A A ℂ)‖ ≤ 1) :
    ofContraction (1 : Matrix A A ℂ) h = SubInstrument.pure PUnit.unit :=
  SubInstrument.ext <| funext fun u ↦ by
    cases u
    rw [branch_ofContraction, MatrixMap.conj_one, branch_pure_self]

/-- Each branch of a composite that starts with a contraction is the branch of the continuation
after the Kraus map of the contraction. -/
theorem branch_ofContraction_bind_apply (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1)
    (k : PUnit → SubInstrument B C β) (b : β) :
    ((ofContraction K hK).bind k).branch b = (k PUnit.unit).branch b ∘ₗ MatrixMap.conj K :=
  branch_ofMap_bind_apply ..

/-- Sequencing the subinstruments of two contractions gives the subinstrument of their
product. -/
theorem ofContraction_bind_ofContraction [DecidableEq B] (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1)
    (L : Matrix C B ℂ) (hL : ‖L‖ ≤ 1) :
    ((ofContraction K hK).bind fun _ ↦ ofContraction L hL) =
      ofContraction (L * K) (l2_opNorm_mul_le_one hL hK) :=
  SubInstrument.ext <| funext fun u ↦ by
    rw [branch_ofContraction_bind_apply, branch_ofContraction, branch_ofContraction,
      MatrixMap.conj_mul]

/-- The subinstrument of a contraction `K` sends the pure substate of `ψ` to the pure substate
of `K •ᵥ ψ`. -/
theorem post_ofContraction_ofVector (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1) (ψ : EuclideanSpace ℂ A)
    (hψ : ‖ψ‖ ≤ 1) (u : PUnit) :
    (ofContraction K hK).post (.ofVector ψ hψ) u =
      .ofVector (K •ᵥ ψ) (norm_applyVec_le_one hK hψ) :=
  SubState.ext <| by
    rw [ofContraction, matrix_post_ofMap]
    exact conj_ketBra_self K ψ

/-- On the pure substate of `ψ`, the subinstrument of a contraction `K` reports its unique
outcome with weight `‖K •ᵥ ψ‖ ^ 2`. -/
theorem outcomeMeasure_ofContraction_ofVector (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1)
    (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    (ofContraction K hK).outcomeMeasure (.ofVector ψ hψ) =
      ENNReal.ofReal (‖K •ᵥ ψ‖ ^ 2) • Measure.dirac PUnit.unit := by
  rw [outcomeMeasure_eq_sum_univ, Fintype.sum_unique, PUnit.default_eq_unit, branch_ofContraction,
    SubState.matrix_ofVector, conj_ketBra_self, trace_re_ketBra_self]

/-- Vector form of the chain rule for a contraction: the outcome measure of a composite that
starts with the contraction `K`, on the pure substate of `ψ`, is the outcome measure of the
continuation on the pure substate of `K •ᵥ ψ`. -/
theorem outcomeMeasure_ofContraction_bind_ofVector [MeasurableSpace β] (K : Matrix B A ℂ)
    (hK : ‖K‖ ≤ 1) (k : PUnit → SubInstrument B C β) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    ((ofContraction K hK).bind k).outcomeMeasure (.ofVector ψ hψ) =
      (k PUnit.unit).outcomeMeasure (.ofVector (K •ᵥ ψ) (norm_applyVec_le_one hK hψ)) :=
  (outcomeMeasure_ofMap_bind ..).trans <|
    congrArg _ (post_ofContraction_ofVector K hK ψ hψ PUnit.unit)

/-- Vector form of the post-branch substates of a composite that starts with a contraction. -/
theorem post_ofContraction_bind_ofVector (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1)
    (k : PUnit → SubInstrument B C β) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (b : β) :
    ((ofContraction K hK).bind k).post (.ofVector ψ hψ) b =
      (k PUnit.unit).post (.ofVector (K •ᵥ ψ) (norm_applyVec_le_one hK hψ)) b :=
  (post_ofMap_bind ..).trans <|
    congrArg (fun ρ ↦ (k PUnit.unit).post ρ b)
      (post_ofContraction_ofVector K hK ψ hψ PUnit.unit)

end ofContraction

/-! ## The Born rule for Kraus measurements -/

section ofKraus

variable [Fintype α] [DecidableEq A]

/-- After a Kraus measurement reports `a` on `|ψ⟩⟨ψ|`, the state is `|K a ψ⟩⟨K a ψ|`, unnormalized:
its trace `‖K a •ᵥ ψ‖²` is the probability of `a`. When that probability is positive, the
conditional state is described by the unit vector `K a •ᵥ ψ / ‖K a •ᵥ ψ‖`. -/
theorem post_ofKraus_ofVector (K : α → Matrix B A ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1)
    (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofKraus K hK).post (.ofVector ψ hψ) a =
      .ofVector (K a •ᵥ ψ) ((norm_applyVec_le_of_sum_conjTranspose_mul_self hK a ψ).trans hψ) :=
  SubState.ext <| conj_ketBra_self (K a) ψ

/-- Vector form of the chain rule for a Kraus measurement: the outcome measure of a composite
that starts with the measurement, on the pure substate of `ψ`, sums the outcome measures of the
continuations on the pure substates of the branches `K a •ᵥ ψ`. -/
theorem outcomeMeasure_ofKraus_bind_ofVector {β : Type*} [MeasurableSpace β]
    (K : α → Matrix B A ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1) (k : α → SubInstrument B C β)
    (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    ((ofKraus K hK).bind k).outcomeMeasure (.ofVector ψ hψ) =
      ∑ a, (k a).outcomeMeasure (.ofVector (K a •ᵥ ψ)
        ((norm_applyVec_le_of_sum_conjTranspose_mul_self hK a ψ).trans hψ)) := by
  rw [outcomeMeasure_bind, Measure.sum_fintype]
  simp_rw [post_ofKraus_ofVector K hK ψ hψ]

variable [MeasurableSpace α]

/-- The Born rule: for Kraus operators with `∑ a, (K a)† * K a = 1`, the distribution of the outcome
on `|ψ⟩⟨ψ|` is `∑ a, ‖K a •ᵥ ψ‖² • δ_a`, of total mass `‖ψ‖²`. For a unit vector the weights are
probabilities. -/
theorem outcomeMeasure_ofKraus_ofVector (K : α → Matrix B A ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1)
    (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    (ofKraus K hK).outcomeMeasure (.ofVector ψ hψ) =
      ∑ a, ENNReal.ofReal (‖K a •ᵥ ψ‖ ^ 2) • Measure.dirac a := by
  rw [outcomeMeasure_eq_sum_univ]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [branch_ofKraus_apply, SubState.matrix_ofVector, conj_ketBra_self, trace_re_ketBra_self]

variable [MeasurableSingletonClass α]

/-- Born rule for a single outcome. -/
theorem outcomeMeasure_ofKraus_ofVector_singleton (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofKraus K hK).outcomeMeasure (.ofVector ψ hψ) {a} = ENNReal.ofReal (‖K a •ᵥ ψ‖ ^ 2) := by
  rw [outcomeMeasure_apply_singleton, branch_ofKraus_apply, SubState.matrix_ofVector,
    conj_ketBra_self, trace_re_ketBra_self]

/-- Born rule for an event: its weight is the total squared norm of the branches of its
outcomes. -/
theorem outcomeMeasure_ofKraus_ofVector_apply (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (s : Set α)
    [DecidablePred (· ∈ s)] :
    (ofKraus K hK).outcomeMeasure (.ofVector ψ hψ) s =
      ENNReal.ofReal (∑ a with a ∈ s, ‖K a •ᵥ ψ‖ ^ 2) := by
  have hs : MeasurableSet s := s.toFinite.measurableSet
  rw [outcomeMeasure_ofKraus_ofVector, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ sq_nonneg _, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul, Set.indicator_apply]
  split_ifs <;> simp

/-- Born rule for an event, as a real number. -/
theorem outcomeMeasure_real_ofKraus_ofVector_apply (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (s : Set α)
    [DecidablePred (· ∈ s)] :
    ((ofKraus K hK).outcomeMeasure (.ofVector ψ hψ)).real s = ∑ a with a ∈ s, ‖K a •ᵥ ψ‖ ^ 2 := by
  rw [Measure.real, outcomeMeasure_ofKraus_ofVector_apply,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]

/-- The weights that a Kraus measurement gives an event on the pure substates of two vectors
differ by at most `(‖ψ‖ + ‖φ‖) * ‖ψ - φ‖`. -/
theorem abs_outcomeMeasure_real_ofKraus_ofVector_sub_le (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (ψ φ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (hφ : ‖φ‖ ≤ 1)
    (s : Set α) :
    |((ofKraus K hK).outcomeMeasure (.ofVector ψ hψ)).real s -
      ((ofKraus K hK).outcomeMeasure (.ofVector φ hφ)).real s| ≤ (‖ψ‖ + ‖φ‖) * ‖ψ - φ‖ := by
  classical
  rw [outcomeMeasure_real_ofKraus_ofVector_apply, outcomeMeasure_real_ofKraus_ofVector_apply]
  exact abs_sum_norm_sq_applyVec_sub_sum_norm_sq_applyVec_le _ K
    (fun χ ↦ sum_norm_sq_applyVec_le hK _ χ) ψ φ

/-- The weights that a Kraus measurement gives an event on the pure substates of two vectors
differ by at most twice the distance between the vectors. -/
theorem abs_outcomeMeasure_real_ofKraus_ofVector_sub_le_two_mul (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (ψ φ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (hφ : ‖φ‖ ≤ 1)
    (s : Set α) :
    |((ofKraus K hK).outcomeMeasure (.ofVector ψ hψ)).real s -
      ((ofKraus K hK).outcomeMeasure (.ofVector φ hφ)).real s| ≤ 2 * ‖ψ - φ‖ :=
  (abs_outcomeMeasure_real_ofKraus_ofVector_sub_le K hK ψ φ hψ hφ s).trans <|
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

end ofKraus

/-! ## Projective measurements -/

section ofProjectiveFinset

variable [DecidableEq A]

/-- A finite complete family of star projections satisfies the Kraus completeness relation. -/
theorem sum_conjTranspose_mul_self_of_isStarProjection_finset {P : α → Matrix A A ℂ}
    (hP : ∀ a, IsStarProjection (P a)) (s : Finset α) (hsum : ∑ a ∈ s, P a = 1) :
    ∑ a ∈ s, (P a)ᴴ * P a = 1 := by
  convert hsum using 1
  exact Finset.sum_congr rfl fun a _ ↦ by
    rw [← Matrix.star_eq_conjTranspose, (hP a).isSelfAdjoint.star_eq,
      (hP a).isIdempotentElem.eq]

/-- The Lüders instrument of projections with arbitrary labels and finite support `s`.
Completeness is the sum over `s`; all projections outside `s` must vanish. -/
@[expose]
noncomputable def ofProjectiveFinset (P : α → Matrix A A ℂ)
    (hP : ∀ a, IsStarProjection (P a)) (s : Finset α) (hs : ∀ a ∉ s, P a = 0)
    (hsum : ∑ a ∈ s, P a = 1) : SubInstrument A A α :=
  have h : MatrixMap.IsCPTNIFamily fun a ↦ MatrixMap.conj (P a) :=
    .of_forall_notMem s (fun a ha ↦ by rw [hs a ha, MatrixMap.conj_zero])
      (fun a ↦ MatrixMap.isCP_conj (P a)) fun ρ _ ↦ by
        simp_rw [MatrixMap.trace_conj_apply]
        rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul,
          sum_conjTranspose_mul_self_of_isStarProjection_finset hP s hsum, Matrix.one_mul]
  { branch := fun a ↦ MatrixMap.conj (P a)
    isCP_branch := h.isCP
    isTNI_sum := h.isTNI_sum }

variable (P : α → Matrix A A ℂ) (hP : ∀ a, IsStarProjection (P a))
    (s : Finset α) (hs : ∀ a ∉ s, P a = 0) (hsum : ∑ a ∈ s, P a = 1)

/-- The branch at any label is conjugation by that label's projection. -/
@[simp]
theorem branch_ofProjectiveFinset_apply (a : α) :
    (ofProjectiveFinset P hP s hs hsum).branch a = MatrixMap.conj (P a) :=
  rfl

/-- A complete finitely supported projective measurement preserves trace. -/
theorem lossless_ofProjectiveFinset : (ofProjectiveFinset P hP s hs hsum).Lossless := by
  rw [Lossless, total_eq_sum _ (s := s) (fun a ha ↦ by simp [hs a ha])]
  intro ρ
  simp_rw [LinearMap.sum_apply, Matrix.trace_sum, branch_ofProjectiveFinset_apply,
    MatrixMap.trace_conj_apply]
  rw [← Matrix.trace_sum, ← Finset.sum_mul,
    sum_conjTranspose_mul_self_of_isStarProjection_finset hP s hsum, Matrix.one_mul]

/-- After a projective measurement reports `a` on `|ψ⟩⟨ψ|`, the state is `|P a ψ⟩⟨P a ψ|`,
unnormalized: its trace `‖P a •ᵥ ψ‖²` is the probability of `a`. When that probability is positive,
the conditional state is described by the unit vector `P a •ᵥ ψ / ‖P a •ᵥ ψ‖`. -/
theorem post_ofProjectiveFinset_ofVector (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofProjectiveFinset P hP s hs hsum).post (.ofVector ψ hψ) a =
      .ofVector (P a •ᵥ ψ) ((norm_applyVec_le_of_isStarProjection (hP a) ψ).trans hψ) :=
  SubState.ext <| conj_ketBra_self (P a) ψ

/-- The outcome measure is the sum of Dirac measures weighted by squared projected norms. -/
theorem outcomeMeasure_ofProjectiveFinset_ofVector [MeasurableSpace α]
    (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    (ofProjectiveFinset P hP s hs hsum).outcomeMeasure (.ofVector ψ hψ) =
      Measure.sum (fun a ↦ ENNReal.ofReal (‖P a •ᵥ ψ‖ ^ 2) • Measure.dirac a) := by
  rw [outcomeMeasure_eq_sum]
  simp_rw [branch_ofProjectiveFinset_apply, SubState.matrix_ofVector,
    conj_ketBra_self, trace_re_ketBra_self]

/-- Each measurable singleton has weight equal to its squared projected norm. -/
theorem outcomeMeasure_ofProjectiveFinset_ofVector_singleton [MeasurableSpace α]
    [MeasurableSingletonClass α] (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofProjectiveFinset P hP s hs hsum).outcomeMeasure (.ofVector ψ hψ) {a} =
      ENNReal.ofReal (‖P a •ᵥ ψ‖ ^ 2) := by
  rw [outcomeMeasure_apply_singleton, branch_ofProjectiveFinset_apply,
    SubState.matrix_ofVector, conj_ketBra_self, trace_re_ketBra_self]

/-- Distinct projections in a complete finitely supported family multiply to zero. -/
theorem mul_eq_zero_of_isStarProjection_finset {P : α → Matrix A A ℂ}
    (hP : ∀ a, IsStarProjection (P a)) (s : Finset α) (hs : ∀ a ∉ s, P a = 0)
    (hsum : ∑ a ∈ s, P a = 1) {a b : α} (hab : a ≠ b) : P a * P b = 0 := by
  classical
  by_cases ha : a ∈ s
  · by_cases hb : b ∈ s
    · apply Matrix.toEuclideanLin.injective
      apply LinearMap.ext
      intro ψ
      have hnorm : ∑ i ∈ s, ‖P i •ᵥ (P b •ᵥ ψ)‖ ^ 2 = ‖P b •ᵥ ψ‖ ^ 2 := by
        calc
          _ = ∑ i ∈ s, (⟪P b •ᵥ ψ, P i •ᵥ P b •ᵥ ψ⟫_ℂ).re :=
            Finset.sum_congr rfl fun i _ ↦ norm_sq_applyVec_of_isStarProjection (hP i) _
          _ = _ := by
            rw [← Complex.re_sum, ← inner_sum, ← sum_applyVec, hsum, one_applyVec,
              re_inner_self]
      have hle : ‖P a •ᵥ P b •ᵥ ψ‖ ^ 2 + ‖P b •ᵥ ψ‖ ^ 2 ≤ ‖P b •ᵥ ψ‖ ^ 2 := by
        calc
          _ = ∑ i ∈ ({a, b} : Finset α), ‖P i •ᵥ P b •ᵥ ψ‖ ^ 2 := by
            rw [Finset.sum_pair hab, ← mul_applyVec (P b) (P b), (hP b).isIdempotentElem.eq]
          _ ≤ ∑ i ∈ s, ‖P i •ᵥ P b •ᵥ ψ‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (by simp [Finset.insert_subset_iff, ha, hb])
              (fun _ _ _ ↦ sq_nonneg _)
          _ = _ := hnorm
      have hz : P a •ᵥ P b •ᵥ ψ = 0 := by
        apply norm_eq_zero.mp
        nlinarith [norm_nonneg (P a •ᵥ P b •ᵥ ψ)]
      simpa only [mul_applyVec, map_zero, LinearMap.zero_apply] using hz
    · rw [hs b hb, mul_zero]
  · rw [hs a ha, zero_mul]

/-- Repeating a projective outcome leaves its unnormalized post-state unchanged. -/
theorem post_ofProjectiveFinset_post_self (ρ : SubState A) (a : α) :
    (ofProjectiveFinset P hP s hs hsum).post
      ((ofProjectiveFinset P hP s hs hsum).post ρ a) a =
        (ofProjectiveFinset P hP s hs hsum).post ρ a := by
  apply SubState.ext
  simp only [matrix_post, branch_ofProjectiveFinset_apply]
  rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul, (hP a).isIdempotentElem.eq]

/-- A different label has zero weight after a retained projective outcome. -/
theorem outcomeMeasure_ofProjectiveFinset_post_of_ne [MeasurableSpace α]
    [MeasurableSingletonClass α] (ρ : SubState A) {a b : α} (hab : b ≠ a) :
    (ofProjectiveFinset P hP s hs hsum).outcomeMeasure
      ((ofProjectiveFinset P hP s hs hsum).post ρ a) {b} = 0 := by
  rw [outcomeMeasure_apply_singleton, matrix_post]
  simp only [branch_ofProjectiveFinset_apply]
  rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul,
    mul_eq_zero_of_isStarProjection_finset hP s hs hsum hab, MatrixMap.conj_zero]
  simp

end ofProjectiveFinset

section ofProjective

variable [Fintype α] [DecidableEq A]

/-- A family of star projections that sums to one satisfies the completeness relation of Kraus
operators. -/
theorem sum_conjTranspose_mul_self_of_isStarProjection {P : α → Matrix A A ℂ}
    (hP : ∀ a, IsStarProjection (P a)) (hsum : ∑ a, P a = 1) : ∑ a, (P a)ᴴ * P a = 1 := by
  rw [← hsum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Matrix.star_eq_conjTranspose, (hP a).isSelfAdjoint.star_eq, (hP a).isIdempotentElem.eq]

/-- The projective measurement with projections `P a` summing to the identity: on outcome `a` it
applies `ρ ↦ P a ρ P a`. Each `P a` is an orthogonal projection (`IsStarProjection`: `P a† = P a`
and `P a * P a = P a`), and a complete family of them is pairwise orthogonal. On `ψ`, outcome `a`
has probability `‖P a •ᵥ ψ‖²` and leaves `P a •ᵥ ψ` (the Lüders rule). `ofProjectiveFinset` is the
same measurement for an arbitrary label type with finitely many nonzero projections. -/
@[expose]
noncomputable def ofProjective (P : α → Matrix A A ℂ) (hP : ∀ a, IsStarProjection (P a))
    (hsum : ∑ a, P a = 1) : SubInstrument A A α :=
  ofProjectiveFinset P hP Finset.univ (fun a ha ↦ (ha (Finset.mem_univ a)).elim) hsum

variable (P : α → Matrix A A ℂ) (hP : ∀ a, IsStarProjection (P a)) (hsum : ∑ a, P a = 1)

/-- A projective measurement is the Kraus measurement with its projections. -/
theorem ofProjective_eq_ofKraus :
    ofProjective P hP hsum = ofKraus P (sum_conjTranspose_mul_self_of_isStarProjection hP hsum) :=
  SubInstrument.ext rfl

/-- The finite-label constructor is the arbitrary-label constructor supported on all labels. -/
theorem ofProjective_eq_ofProjectiveFinset :
    ofProjective P hP hsum =
      ofProjectiveFinset P hP Finset.univ (fun a ha ↦ (ha (Finset.mem_univ a)).elim) hsum :=
  rfl

include hP hsum in
/-- Distinct projections in a finite complete family multiply to zero. -/
theorem mul_eq_zero_of_isStarProjection {a b : α} (hab : a ≠ b) : P a * P b = 0 :=
  mul_eq_zero_of_isStarProjection_finset hP Finset.univ
    (fun a ha ↦ (ha (Finset.mem_univ a)).elim) hsum hab

/-- Repeating the same outcome of a finite projective measurement preserves the post-state. -/
theorem post_ofProjective_post_self (ρ : SubState A) (a : α) :
    (ofProjective P hP hsum).post ((ofProjective P hP hsum).post ρ a) a =
      (ofProjective P hP hsum).post ρ a :=
  post_ofProjectiveFinset_post_self P hP Finset.univ _ hsum ρ a

/-- The branch of a projective measurement at `a` is the Kraus map of `P a`. -/
@[simp]
theorem branch_ofProjective_apply (a : α) :
    (ofProjective P hP hsum).branch a = MatrixMap.conj (P a) :=
  rfl

/-- A projective measurement is lossless. -/
theorem lossless_ofProjective : (ofProjective P hP hsum).Lossless :=
  lossless_ofProjectiveFinset P hP Finset.univ _ hsum

/-- After a projective measurement reports `a` on `|ψ⟩⟨ψ|`, the state is `|P a ψ⟩⟨P a ψ|`,
unnormalized: its trace `‖P a •ᵥ ψ‖²` is the probability of `a`. When that probability is positive,
the conditional state is described by the unit vector `P a •ᵥ ψ / ‖P a •ᵥ ψ‖`. -/
theorem post_ofProjective_ofVector (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofProjective P hP hsum).post (.ofVector ψ hψ) a =
      .ofVector (P a •ᵥ ψ) ((norm_applyVec_le_of_isStarProjection (hP a) ψ).trans hψ) :=
  SubState.ext <| conj_ketBra_self (P a) ψ

/-- Born rule for a projective measurement: on the pure substate of `ψ`, outcome `a` has weight
`‖P a •ᵥ ψ‖ ^ 2`. -/
theorem outcomeMeasure_ofProjective_ofVector_singleton [MeasurableSpace α]
    [MeasurableSingletonClass α] (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofProjective P hP hsum).outcomeMeasure (.ofVector ψ hψ) {a} =
      ENNReal.ofReal (‖P a •ᵥ ψ‖ ^ 2) :=
  outcomeMeasure_ofProjectiveFinset_ofVector_singleton ..

/-- Born rule for a projective measurement, in expectation form: on the pure substate of `ψ`,
outcome `a` has weight `⟪ψ, P a •ᵥ ψ⟫`. -/
theorem outcomeMeasure_ofProjective_ofVector_singleton_eq_inner [MeasurableSpace α]
    [MeasurableSingletonClass α] (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofProjective P hP hsum).outcomeMeasure (.ofVector ψ hψ) {a} =
      ENNReal.ofReal (⟪ψ, P a •ᵥ ψ⟫_ℂ).re := by
  rw [outcomeMeasure_ofProjective_ofVector_singleton, norm_sq_applyVec_of_isStarProjection (hP a)]

end ofProjective

/-! ## Kraus-form branches over any outcome type

A branch of the form `MatrixMap.conj K` sends the pure substate of `ψ` to that of `K •ᵥ ψ`, with
weight `‖K •ᵥ ψ‖ ^ 2`. This holds for subinstruments with any outcome type, also when infinitely
many branches are nonzero; the Kraus measurements above are the case of finitely many outcomes.
-/

section branchConj

variable [DecidableEq A]

/-- If the branch of a subinstrument at `a` is the Kraus map of `K`, then `K` does not increase
the norm of vectors: `‖K •ᵥ ψ‖ ^ 2` is the trace of the branch on `|ψ⟩⟨ψ|`. -/
theorem norm_applyVec_le_of_branch_eq_conj (p : SubInstrument A B α) {a : α} {K : Matrix B A ℂ}
    (hK : p.branch a = MatrixMap.conj K) (ψ : EuclideanSpace ℂ A) : ‖K •ᵥ ψ‖ ≤ ‖ψ‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have h := p.isCPTNIFamily.isTNI a (ketBra ψ ψ) (posSemidef_ketBra_self ψ)
  rwa [hK, conj_ketBra_self, trace_re_ketBra_self, trace_re_ketBra_self] at h

/-- If the branch of a subinstrument at `a` is the Kraus map of `K`, then after outcome `a` the
pure substate of `ψ` becomes the pure substate of `K •ᵥ ψ`. -/
theorem post_ofVector_of_branch_eq_conj (p : SubInstrument A B α) {a : α} {K : Matrix B A ℂ}
    (hK : p.branch a = MatrixMap.conj K) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    p.post (.ofVector ψ hψ) a =
      .ofVector (K •ᵥ ψ) ((p.norm_applyVec_le_of_branch_eq_conj hK ψ).trans hψ) :=
  SubState.ext <| by
    rw [matrix_post, hK, SubState.matrix_ofVector, SubState.matrix_ofVector, conj_ketBra_self]

/-- Born rule for a Kraus-form branch: if the branch at `a` is the Kraus map of `K`, then on the
pure substate of `ψ` the outcome `a` has weight `‖K •ᵥ ψ‖ ^ 2`. -/
theorem outcomeMeasure_ofVector_singleton_of_branch_eq_conj [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : SubInstrument A B α) {a : α} {K : Matrix B A ℂ}
    (hK : p.branch a = MatrixMap.conj K) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    p.outcomeMeasure (.ofVector ψ hψ) {a} = ENNReal.ofReal (‖K •ᵥ ψ‖ ^ 2) := by
  rw [outcomeMeasure_apply_singleton, hK, SubState.matrix_ofVector, conj_ketBra_self,
    trace_re_ketBra_self]

/-- Born rule for a subinstrument whose branches are all Kraus maps, over any outcome type: on the
pure substate of `ψ`, the outcome measure is the sum of the point masses at the outcomes `a` with
weights `‖K a •ᵥ ψ‖ ^ 2`. -/
theorem outcomeMeasure_ofVector_of_forall_branch_eq_conj [MeasurableSpace α]
    (p : SubInstrument A B α) {K : α → Matrix B A ℂ}
    (hK : ∀ a, p.branch a = MatrixMap.conj (K a)) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    p.outcomeMeasure (.ofVector ψ hψ) =
      Measure.sum fun a ↦ ENNReal.ofReal (‖K a •ᵥ ψ‖ ^ 2) • Measure.dirac a := by
  rw [outcomeMeasure_eq_sum]
  simp only [hK, SubState.matrix_ofVector, conj_ketBra_self, trace_re_ketBra_self]

end branchConj

end SubInstrument

/-! ## Dependent subinstruments on pure substates -/

namespace DSubInstrument

variable {A : Type*} [Fintype A] [DecidableEq A] {ι : Type*} {B : ι → Type*}
  [∀ i, Fintype (B i)]

/-- If the branch of a dependent subinstrument at `i` is the Kraus map of `K`, then `K` does not
increase the norm of vectors. -/
theorem norm_applyVec_le_of_branch_eq_conj (p : DSubInstrument A ι B) {i : ι}
    {K : Matrix (B i) A ℂ} (hK : p.branch i = MatrixMap.conj K) (ψ : EuclideanSpace ℂ A) :
    ‖K •ᵥ ψ‖ ≤ ‖ψ‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have h := p.isCPTNIFamily.isTNI i (ketBra ψ ψ) (posSemidef_ketBra_self ψ)
  rwa [hK, conj_ketBra_self, trace_re_ketBra_self, trace_re_ketBra_self] at h

/-- If the branch of a dependent subinstrument at `i` is the Kraus map of `K`, then after outcome
`i` the pure substate of `ψ` becomes the pure substate of `K •ᵥ ψ` on the system `B i`. -/
theorem post_ofVector_of_branch_eq_conj (p : DSubInstrument A ι B) {i : ι}
    {K : Matrix (B i) A ℂ} (hK : p.branch i = MatrixMap.conj K) (ψ : EuclideanSpace ℂ A)
    (hψ : ‖ψ‖ ≤ 1) :
    p.post (.ofVector ψ hψ) i =
      .ofVector (K •ᵥ ψ) ((p.norm_applyVec_le_of_branch_eq_conj hK ψ).trans hψ) :=
  SubState.ext <| by
    rw [matrix_post, hK, SubState.matrix_ofVector, SubState.matrix_ofVector, conj_ketBra_self]

/-- Born rule for a Kraus-form branch of a dependent subinstrument. -/
theorem outcomeMeasure_ofVector_singleton_of_branch_eq_conj [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (p : DSubInstrument A ι B) {i : ι} {K : Matrix (B i) A ℂ}
    (hK : p.branch i = MatrixMap.conj K) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    p.outcomeMeasure (.ofVector ψ hψ) {i} = ENNReal.ofReal (‖K •ᵥ ψ‖ ^ 2) := by
  rw [outcomeMeasure_apply_singleton, hK, SubState.matrix_ofVector, conj_ketBra_self,
    trace_re_ketBra_self]

/-- Born rule for a dependent subinstrument whose branches are all Kraus maps, over any outcome
type. -/
theorem outcomeMeasure_ofVector_of_forall_branch_eq_conj [MeasurableSpace ι]
    (p : DSubInstrument A ι B) {K : (i : ι) → Matrix (B i) A ℂ}
    (hK : ∀ i, p.branch i = MatrixMap.conj (K i)) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    p.outcomeMeasure (.ofVector ψ hψ) =
      Measure.sum fun i ↦ ENNReal.ofReal (‖K i •ᵥ ψ‖ ^ 2) • Measure.dirac i := by
  rw [outcomeMeasure_eq_sum]
  simp only [hK, SubState.matrix_ofVector, conj_ketBra_self, trace_re_ketBra_self]

section ofKraus

variable [Fintype ι] (K : (i : ι) → Matrix (B i) A ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)

/-- After a dependent Kraus measurement reports `i` on `|ψ⟩⟨ψ|`, the state is `|K i ψ⟩⟨K i ψ|`,
unnormalized on the output system `B i`: its trace `‖K i •ᵥ ψ‖²` is the probability of `i`. When
that probability is positive, the conditional state is described by the unit vector
`K i •ᵥ ψ / ‖K i •ᵥ ψ‖`. -/
theorem post_ofKraus_ofVector (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (i : ι) :
    (ofKraus K hK).post (.ofVector ψ hψ) i =
      .ofVector (K i •ᵥ ψ)
        (((ofKraus K hK).norm_applyVec_le_of_branch_eq_conj (branch_ofKraus_apply K hK i) ψ).trans
          hψ) :=
  post_ofVector_of_branch_eq_conj _ (branch_ofKraus_apply K hK i) ψ hψ

/-- Born rule for a dependent Kraus measurement: on the pure substate of `ψ`, outcome `i` has
weight `‖K i •ᵥ ψ‖ ^ 2`. -/
theorem outcomeMeasure_ofKraus_ofVector_singleton [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (i : ι) :
    (ofKraus K hK).outcomeMeasure (.ofVector ψ hψ) {i} = ENNReal.ofReal (‖K i •ᵥ ψ‖ ^ 2) :=
  outcomeMeasure_ofVector_singleton_of_branch_eq_conj _ (branch_ofKraus_apply K hK i) ψ hψ

end ofKraus

end DSubInstrument

/-! ## Unitaries on a fixed register -/

namespace SubInstrument

variable {M : Type u} [Fintype M] [DecidableEq M]

/-- The subinstrument that applies the unitary `U` to the register and returns the unique
value. -/
@[expose]
noncomputable def ofUnitary (U : Matrix.unitaryGroup M ℂ) : SubInstrument M M PUnit.{w + 1} :=
  SubInstrument.ofContraction (U : Matrix M M ℂ) (l2_opNorm_le_one_of_mem_unitaryGroup U.2)

/-- Applying a unitary is lossless. -/
theorem lossless_ofUnitary (U : Matrix.unitaryGroup M ℂ) :
    (ofUnitary.{u, w} U).Lossless :=
  SubInstrument.lossless_ofContraction _ (Matrix.mem_unitaryGroup_iff'.mp U.2)

/-- Applying the identity unitary is `pure`. -/
@[simp]
theorem ofUnitary_one : ofUnitary.{u, w} (1 : Matrix.unitaryGroup M ℂ) = pure PUnit.unit :=
  SubInstrument.ofContraction_one _

/-- Applying `U` and then `V` is applying the product `V * U`. -/
theorem ofUnitary_bind_ofUnitary (U V : Matrix.unitaryGroup M ℂ) :
    (ofUnitary.{u, w} U >>= fun _ ↦ ofUnitary.{u, w} V) = ofUnitary (V * U) :=
  SubInstrument.ofContraction_bind_ofContraction ..

/-- Applying a unitary `U` sends the pure substate of `ψ` to the pure substate of `U •ᵥ ψ`. -/
theorem post_ofUnitary_ofVector (U : Matrix.unitaryGroup M ℂ) (ψ : EuclideanSpace ℂ M)
    (hψ : ‖ψ‖ ≤ 1) (u : PUnit) :
    (ofUnitary.{u, w} U).post (.ofVector ψ hψ) u =
      .ofVector ((U : Matrix M M ℂ) •ᵥ ψ)
        ((norm_applyVec_of_mem_unitaryGroup U.2 ψ).le.trans hψ) :=
  SubInstrument.post_ofContraction_ofVector ..

/-- On the pure substate of `ψ`, applying a unitary returns its value with weight `‖ψ‖ ^ 2`. -/
theorem outcomeMeasure_ofUnitary_ofVector (U : Matrix.unitaryGroup M ℂ)
    (ψ : EuclideanSpace ℂ M) (hψ : ‖ψ‖ ≤ 1) :
    (ofUnitary.{u, w} U).outcomeMeasure (.ofVector ψ hψ) =
      ENNReal.ofReal (‖ψ‖ ^ 2) • Measure.dirac PUnit.unit := by
  rw [ofUnitary, SubInstrument.outcomeMeasure_ofContraction_ofVector,
    norm_applyVec_of_mem_unitaryGroup U.2]

/-- Vector form of the chain rule for a unitary step: the outcome measure of a computation that
starts by applying `U`, on the pure substate of `ψ`, is the outcome measure of the rest on the
pure substate of `U •ᵥ ψ`. -/
theorem outcomeMeasure_ofUnitary_bind_ofVector {β : Type w} [MeasurableSpace β]
    (U : Matrix.unitaryGroup M ℂ) (k : PUnit → SubInstrument M M β) (ψ : EuclideanSpace ℂ M)
    (hψ : ‖ψ‖ ≤ 1) :
    (ofUnitary.{u, w} U >>= k).outcomeMeasure (.ofVector ψ hψ) =
      (k PUnit.unit).outcomeMeasure (.ofVector ((U : Matrix M M ℂ) •ᵥ ψ)
        ((norm_applyVec_of_mem_unitaryGroup U.2 ψ).le.trans hψ)) :=
  SubInstrument.outcomeMeasure_ofContraction_bind_ofVector ..

end SubInstrument

end Quantum
