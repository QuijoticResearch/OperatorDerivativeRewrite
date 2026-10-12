import Foundation.GaussianChaosCylinders
import Foundation.GaussianBrownianGeneratedSpace

/-! Actual Gaussian conditional projections preserve the full derivative domain.
The generated family may be uncountable, correlated, or linearly dependent. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianConditionalGraph
open InfiniteGaussian GaussianNumberSectors
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
variable {I : Type*}

def generated (h : I → CoefficientSpace) : Submodule ℝ GaussianL2 :=
  lpMeas ℝ ℝ (MeasurableSpace.comap (firstChaosFamily h) inferInstance) 2 gaussianProduct

theorem generated_isClosed (h : I → CoefficientSpace) :
    IsClosed (generated h : Set GaussianL2) := by
  rw [generated, ← familyPolynomial_closure]
  exact Submodule.isClosed_topologicalClosure _

instance generated_complete (h : I → CoefficientSpace) : CompleteSpace (generated h) :=
  (generated_isClosed h).completeSpace_coe

def conditionalProjection (h : I → CoefficientSpace) : GaussianL2 →L[ℝ] GaussianL2 :=
  (generated h).starProjection

theorem generatedSigma_le (h : I → CoefficientSpace) :
    MeasurableSpace.comap (firstChaosFamily h) inferInstance ≤
      (inferInstance : MeasurableSpace SampleSpace) :=
  (Measurable.of_eval (fun i => (Lp.stronglyMeasurable (firstChaosEmbedding (h i))).measurable)).comap_le

theorem conditionalProjection_eq_condExpL2 (h : I → CoefficientSpace) (f : GaussianL2) :
    conditionalProjection h f = (condExpL2 ℝ ℝ (generatedSigma_le h) f : GaussianL2) := rfl

theorem conditionalProjection_ae_condExp (h : I → CoefficientSpace) (f : GaussianL2) :
    conditionalProjection h f =ᵐ[gaussianProduct]
      gaussianProduct[f | MeasurableSpace.comap (firstChaosFamily h) inferInstance] := by
  rw [conditionalProjection_eq_condExpL2]
  have hs := (Lp.memLp f).condExpL2_ae_eq_condExp (𝕜 := ℝ) (generatedSigma_le h)
  simpa only [Lp.toLp_coeFn] using hs

theorem projection_familyPolynomial (n : ℕ) (h : I → CoefficientSpace)
    (p : MvPolynomial I ℝ) :
    ∃ q : MvPolynomial I ℝ,
      projection n (familyPolynomialEmbedding h p) = familyPolynomialEmbedding h q := by
  obtain ⟨s, p, rfl⟩ := MvPolynomial.exists_finset_rename p
  rw [familyPolynomial_rename]
  obtain ⟨q, hq⟩ := projection_polynomial n (fun i : s => h i) p
  exact ⟨MvPolynomial.rename Subtype.val q, hq.trans (familyPolynomial_rename h s q).symm⟩

theorem projection_preserves_generated (n : ℕ) (h : I → CoefficientSpace)
    {f : GaussianL2} (hf : f ∈ generated h) : projection n f ∈ generated h := by
  have hs : (familyPolynomialEmbedding h).range.topologicalClosure ≤
      (generated h).comap (projection n).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro f ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := projection_familyPolynomial n h p
      change projection n (familyPolynomialEmbedding h p) ∈ generated h
      rw [hq]
      exact familyPolynomial_aestronglyMeasurable h q
    · exact (generated_isClosed h).preimage (projection n).continuous
  rw [familyPolynomial_closure] at hs
  exact hs hf

theorem projection_conditional_commute (n : ℕ) (h : I → CoefficientSpace) (f : GaussianL2) :
    projection n (conditionalProjection h f) = conditionalProjection h (projection n f) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact projection_preserves_generated n h ((generated h).starProjection_apply_mem f)
  · intro w hw
    rw [← map_sub]
    change inner ℝ ((sector n).starProjection (f - (generated h).starProjection f)) w = 0
    rw [(sector n).inner_starProjection_left_eq_right]
    exact (generated h).starProjection_inner_eq_zero f _
      (projection_preserves_generated n h hw)

theorem conditionalProjection_norm_le (h : I → CoefficientSpace) (f : GaussianL2) :
    ‖conditionalProjection h f‖ ≤ ‖f‖ := (generated h).norm_starProjection_apply_le f

theorem conditional_weighted_coefficient_le (h : I → CoefficientSpace) (f : GaussianL2) (n : ℕ) :
    (n : ℝ) * ‖projection n (conditionalProjection h f)‖ ^ 2 ≤
      (n : ℝ) * ‖projection n f‖ ^ 2 := by
  rw [projection_conditional_commute]
  exact mul_le_mul_of_nonneg_left
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (conditionalProjection_norm_le h _))
    (Nat.cast_nonneg n)

theorem conditionalProjection_mem_domain (h : I → CoefficientSpace)
    {f : GaussianL2} (hf : f ∈ closedCylindricalDerivative.domain) :
    conditionalProjection h f ∈ closedCylindricalDerivative.domain := by
  apply (derivative_domain_iff_weighted_chaos _).mpr
  exact ((derivative_domain_iff_weighted_chaos _).mp hf).of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
    (conditional_weighted_coefficient_le h f)

def conditionalDomain (h : I → CoefficientSpace) (f : closedCylindricalDerivative.domain) :
    closedCylindricalDerivative.domain :=
  ⟨conditionalProjection h f, conditionalProjection_mem_domain h f.property⟩

theorem conditional_derivative_norm_le (h : I → CoefficientSpace)
    (f : closedCylindricalDerivative.domain) :
    ‖closedCylindricalDerivative (conditionalDomain h f)‖ ≤ ‖closedCylindricalDerivative f‖ := by
  have hs := hasSum_le (conditional_weighted_coefficient_le h f)
    (derivative_energy_hasSum (closedCylindricalDerivative.mem_graph (conditionalDomain h f)))
    (derivative_energy_hasSum (closedCylindricalDerivative.mem_graph f))
  nlinarith [norm_nonneg (closedCylindricalDerivative (conditionalDomain h f)),
    norm_nonneg (closedCylindricalDerivative f)]

theorem projection_preserves_brownian (n : ℕ) {f : GaussianL2}
    (hf : f ∈ GaussianBrownianGeneratedSpace.brownianL2) :
    projection n f ∈ GaussianBrownianGeneratedSpace.brownianL2 :=
  projection_preserves_generated n
    (fun t => SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
      (GaussianTimeHilbert.timeVector t)) hf

theorem truncation_preserves_brownian (N : ℕ) {f : GaussianL2}
    (hf : f ∈ GaussianBrownianGeneratedSpace.brownianL2) :
    truncation N f ∈ GaussianBrownianGeneratedSpace.brownianL2 := by
  rw [truncation, ContinuousLinearMap.sum_apply]
  exact Submodule.sum_mem _ (fun n _ => projection_preserves_brownian n hf)

end OperatorDerivativeRewrite.Foundation.GaussianConditionalGraph
