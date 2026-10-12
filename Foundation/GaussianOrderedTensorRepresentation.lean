import Foundation.GaussianTimeSpaceTensor
import Foundation.GaussianWeightedIntegrand

/-! Predictable representation of ordered increment tensors, with zero durations allowed.
The last positive Hermite degree is represented using its genuinely L² raw-past coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set MvPolynomial
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianOrderedTensorRepresentation
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeSpaceTensor GaussianTimeProcess
open GaussianTimeDivergence GaussianPredictableFull GaussianTerminalRepresentation
open GaussianTimeHilbert SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

variable {m : ℕ}

def incrementPolynomial (s t : Fin m → ℝ≥0) : MvPolynomial (Fin m) ℝ →ₗ[ℝ] GaussianL2 :=
  familyPolynomialEmbedding (fun i => incrementDirection (s i) (t i))

def tensorValue (s t : Fin m → ℝ≥0) (α : Fin m → ℕ) (ω : SampleSpace) : ℝ :=
  ∏ i, value (α i) (process (t i) ω - process (s i) ω) (t i - s i : ℝ≥0)

theorem incrementPolynomial_coeFn (s t : Fin m → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (p : MvPolynomial (Fin m) ℝ) : incrementPolynomial s t p =ᵐ[gaussianProduct]
      fun ω => eval (fun i => process (t i) ω - process (s i) ω) p := by
  filter_upwards [isonormalCylinderL2_coeFn (fun i => incrementDirection (s i) (t i)) p,
    ae_all_iff.mpr (fun i => process_increment_ae (s i) (t i) (hst i))] with ω hp hi
  exact hp.trans (congrArg (fun x => eval x p) (funext hi))

theorem tensor_coeFn (s t : Fin m → ℝ≥0) (hst : ∀ i, s i ≤ t i) (α : Fin m → ℕ) :
    incrementPolynomial s t (tensorPolynomial (fun i => (t i - s i : ℝ≥0)) α)
      =ᵐ[gaussianProduct] tensorValue s t α := by
  filter_upwards [incrementPolynomial_coeFn s t hst
    (tensorPolynomial (fun i => (t i - s i : ℝ≥0)) α)] with ω hω
  exact hω.trans (eval_tensorPolynomial _ _ _)

theorem tensorValue_memLp (s t : Fin m → ℝ≥0) (hst : ∀ i, s i ≤ t i) (α : Fin m → ℕ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp (tensorValue s t α) p gaussianProduct :=
  (polynomialDomain_memLp ⟨isonormalCylinderL2 (fun i => incrementDirection (s i) (t i))
    (tensorPolynomial (fun i => (t i - s i : ℝ≥0)) α), isonormalCylinderL2_mem_core _ _⟩ p hp).ae_eq
      (tensor_coeFn s t hst α)

theorem tensorValue_past (s t : Fin m → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (α : Fin m → ℕ) (r : ℝ≥0) (hα : ∀ i, α i ≠ 0 → t i ≤ r) :
    Measurable[naturalFiltration r] (tensorValue s t α) := by
  classical
  letI : MeasurableSpace SampleSpace := naturalFiltration r
  apply Finset.measurable_prod
  intro i _
  by_cases hi : α i = 0
  · simp only [hi, value_zero]; exact measurable_const
  · exact (polynomial (t i - s i : ℝ≥0) (α i)).continuous_eval.measurable.comp
      (Measurable.of_eval fun _ : Unit =>
        ((process_stronglyAdapted (t i)).measurable.mono
          (naturalFiltration.mono (hα i hi)) le_rfl).sub
        ((process_stronglyAdapted (s i)).measurable.mono
          (naturalFiltration.mono ((hst i).trans (hα i hi))) le_rfl))

theorem positive_tensor_mem_range (s t : Fin m → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (horder : ∀ i j, i < j → t i ≤ s j) (α : Fin m → ℕ) (hne : ∃ i, α i ≠ 0) :
    incrementPolynomial s t (tensorPolynomial (fun i => (t i - s i : ℝ≥0)) α)
      ∈ itoIntegral.toLinearMap.range := by
  classical
  let S := Finset.univ.filter (fun i => α i ≠ 0)
  have hS : S.Nonempty := by obtain ⟨i, hi⟩ := hne; exact ⟨i, by simp [S, hi]⟩
  let j := S.max' hS
  have hj : α j ≠ 0 := (Finset.mem_filter.mp (S.max'_mem hS)).2
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hj
  let β := Function.update α j 0
  have hβ (i : Fin m) (hi : β i ≠ 0) : t i ≤ s j := by
    have hij : i ≠ j := by intro he; subst i; simpa [β] using hi
    have hai : α i ≠ 0 := by simpa [β, hij] using hi
    exact horder i j (lt_of_le_of_ne (S.le_max' i (by simp [S, hai])) hij)
  obtain ⟨U, hU, _⟩ := GaussianWeightedIntegrand.exists_unique_weighted_representation
    (s j) (t j - s j) n (tensorValue s t β)
      (tensorValue_past s t hst β (s j) hβ) (tensorValue_memLp s t hst β 2 (by simp))
  refine ⟨(n + 1 : ℝ) • U, ?_⟩
  change itoIntegral ((n + 1 : ℝ) • U) = _
  rw [map_smul]
  apply Lp.ext
  filter_upwards [hU, tensor_coeFn s t hst α,
    Lp.coeFn_smul (n + 1 : ℝ) (itoIntegral U)] with ω hu ht hu'
  rw [hu', ht]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← hu, add_tsub_cancel_of_le (hst j)]
  change (∏ i, value (β i) _ _) * value (n + 1) _ _ = _
  have he : (∏ i, value (β i) (process (t i) ω - process (s i) ω)
      (t i - s i : ℝ≥0)) = ∏ i ∈ Finset.univ.erase j,
      value (α i) (process (t i) ω - process (s i) ω) (t i - s i : ℝ≥0) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    simp only [β, Function.update_self, value_zero, mul_one]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [he]
  simpa only [hn, tensorValue] using Finset.prod_erase_mul Finset.univ
    (fun i => value (α i) (process (t i) ω - process (s i) ω) (t i - s i : ℝ≥0))
    (Finset.mem_univ j)

theorem centered_tensor_mem_range (s t : Fin m → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (horder : ∀ i j, i < j → t i ≤ s j) (α : Fin m → ℕ) :
    centering (incrementPolynomial s t (tensorPolynomial (fun i => (t i - s i : ℝ≥0)) α))
      ∈ itoIntegral.toLinearMap.range := by
  by_cases hne : ∃ i, α i ≠ 0
  · obtain ⟨U, hU⟩ := positive_tensor_mem_range s t hst horder α hne
    change itoIntegral U = _ at hU
    rw [← hU, centering_apply, itoIntegral_centered, zero_smul, sub_zero]
    exact ⟨U, rfl⟩
  · have hz : ∀ i, α i = 0 := by simpa using hne
    have he : incrementPolynomial s t
        (tensorPolynomial (fun i => (t i - s i : ℝ≥0)) α) = gaussianOne := by
      apply Lp.ext
      filter_upwards [tensor_coeFn s t hst α, gaussianOne_coeFn] with ω ht h1
      simp [ht, h1, tensorValue, hz]
    rw [he]
    change gaussianOne - inner ℝ gaussianOne gaussianOne • _ ∈ _
    rw [GaussianDeterministicGraphCore.gaussianOne_inner_self, one_smul, sub_self]
    exact Submodule.zero_mem _

theorem centered_incrementPolynomial_mem_range (s t : Fin m → ℝ≥0)
    (hst : ∀ i, s i ≤ t i) (horder : ∀ i j, i < j → t i ≤ s j)
    (p : MvPolynomial (Fin m) ℝ) :
    centering (incrementPolynomial s t p) ∈ itoIntegral.toLinearMap.range := by
  have h : Submodule.span ℝ
      (Set.range (tensorPolynomial (fun i => (t i - s i : ℝ≥0)))) ≤
      itoIntegral.toLinearMap.range.comap (centering.toLinearMap.comp (incrementPolynomial s t)) := by
    apply Submodule.span_le.mpr
    rintro p ⟨α, rfl⟩
    exact centered_tensor_mem_range s t hst horder α
  rw [tensorPolynomial_span] at h
  exact h Submodule.mem_top

end OperatorDerivativeRewrite.Foundation.GaussianOrderedTensorRepresentation
