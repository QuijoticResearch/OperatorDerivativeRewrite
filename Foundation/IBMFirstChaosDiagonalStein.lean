import Foundation.IBMScaledGaussianStein
import Foundation.InfiniteGaussianIsonormal

/-! Nonpolynomial Stein identities on the actual first-chaos source,
transported from verified weighted scalar IBP. Zero directions are included. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFirstChaosDiagonalStein
open InfiniteGaussian HelicalWeightedPressureIBP IBMScaledGaussianStein

theorem law_scaled_quarter (u : CoefficientSpace) :
    gaussianProduct.map (firstChaosEmbedding u) =
      ν.map (fun x : ℝ => (2 * ‖u‖) * x) := by
  rw [firstChaos_law, ν, gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.eq
    simp only [NNReal.coe_mk, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_div,
      NNReal.coe_one]
    ring

theorem integral_transport (u : CoefficientSpace) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ ω, f (firstChaosEmbedding u ω) ∂gaussianProduct) =
      ∫ x, f ((2 * ‖u‖) * x) ∂ν := by
  have h₁ := integral_map (μ := gaussianProduct)
    (Lp.stronglyMeasurable (firstChaosEmbedding u)).aemeasurable hf.aestronglyMeasurable
  have h₂ := integral_map (μ := ν)
    (show AEMeasurable (fun x : ℝ => (2 * ‖u‖) * x) ν from (by fun_prop))
    hf.aestronglyMeasurable
  rw [law_scaled_quarter] at h₁
  exact h₁.symm.trans h₂

theorem bounded_comp_memLp (u : CoefficientSpace) {φ : ℝ → ℝ}
    (hc : Continuous φ) {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    MemLp (fun ω => φ (firstChaosEmbedding u ω)) 2 gaussianProduct :=
  MemLp.of_bound (hc.comp_stronglyMeasurable
    (Lp.stronglyMeasurable (firstChaosEmbedding u))).aestronglyMeasurable A
    (Filter.Eventually.of_forall fun ω => hA _)

theorem first_integrable (u : CoefficientSpace) {φ : ℝ → ℝ}
    (hc : Continuous φ) {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    Integrable (fun ω => firstChaosEmbedding u ω * φ (firstChaosEmbedding u ω))
      gaussianProduct := (Lp.memLp (firstChaosEmbedding u)).integrable_mul
        (bounded_comp_memLp u hc hA)

theorem second_integrable (u : CoefficientSpace) {φ : ℝ → ℝ}
    (hc : Continuous φ) {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    Integrable (fun ω => (firstChaosEmbedding u ω)^2 * φ (firstChaosEmbedding u ω))
      gaussianProduct := by
  have hi := (Lp.memLp (firstChaosEmbedding u)).integrable_sq
  apply Integrable.mono' (hi.mul_const A)
    (((Lp.stronglyMeasurable (firstChaosEmbedding u)).pow 2).mul
      (hc.comp_stronglyMeasurable (Lp.stronglyMeasurable _))).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    change ‖(firstChaosEmbedding u ω)^2 * φ (firstChaosEmbedding u ω)‖ ≤
      (firstChaosEmbedding u ω)^2 * A
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hA _) (sq_nonneg _)

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {A B C : ℝ}
  (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖deriv φ x‖ ≤ B)
  (hC : ∀ x, ‖deriv (deriv φ) x‖ ≤ C)

include hφ hA hB in
/-- Genuine first source moment identity for arbitrary bounded C² tests. -/
theorem first_diagonal (u : CoefficientSpace) :
    (∫ ω, firstChaosEmbedding u ω * φ (firstChaosEmbedding u ω) ∂gaussianProduct) =
      ‖u‖^2 * ∫ ω, deriv φ (firstChaosEmbedding u ω) ∂gaussianProduct := by
  rw [integral_transport u (f := fun x => x * φ x)
    (measurable_id.mul hφ.continuous.measurable),
    integral_transport u (hφ.continuous_deriv (by norm_num)).measurable]
  have h := scaled_first hφ hA hB (2 * ‖u‖)
  have ha : (2 * ‖u‖)^2 / 4 = ‖u‖^2 := by ring
  simpa only [ha] using h

include hφ hA hB hC in
/-- The actual centered second source moment has the norm-four coefficient.
This is not restricted to polynomial observables or nonzero directions. -/
theorem second_diagonal (u : CoefficientSpace) :
    (∫ ω, ((firstChaosEmbedding u ω)^2 - ‖u‖^2) * φ (firstChaosEmbedding u ω)
      ∂gaussianProduct) =
      ‖u‖^4 * ∫ ω, deriv (deriv φ) (firstChaosEmbedding u ω) ∂gaussianProduct := by
  have hdc := (RealSteklovApprox.deriv_contDiff_one φ hφ).continuous_deriv_one
  rw [integral_transport u (f := fun x => (x^2 - ‖u‖^2) * φ x)
    (((measurable_id.pow_const 2).sub measurable_const).mul hφ.continuous.measurable),
    integral_transport u hdc.measurable]
  have h := scaled_second hφ hA hB hC (2 * ‖u‖)
  have ha : (2 * ‖u‖)^2 / 4 = ‖u‖^2 := by ring
  have hb : (2 * ‖u‖)^4 / 16 = ‖u‖^4 := by ring
  simpa only [ha, hb] using h

end OperatorDerivativeRewrite.Foundation.IBMFirstChaosDiagonalStein
