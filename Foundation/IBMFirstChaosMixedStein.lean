import Foundation.IBMFirstChaosDiagonalStein
import Foundation.FractionalCurrentObservationObstruction

/-! Mixed actual-source Stein moments from existing conditional Wick
projections. The singleton observation can be degenerate. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMFirstChaosMixedStein
open InfiniteGaussian IBMFirstChaosDiagonalStein GaussianConditionalGraph
open GaussianWickConditionalProjection GaussianTimeSpaceHermite

def testClass (u : CoefficientSpace) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) : GaussianL2 :=
  (bounded_comp_memLp u hc hA).toLp _

theorem testClass_coeFn (u : CoefficientSpace) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    testClass u hc hA =ᵐ[gaussianProduct] fun ω => φ (firstChaosEmbedding u ω) :=
  MemLp.coeFn_toLp _

theorem testClass_generated (u : CoefficientSpace) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    testClass u hc hA ∈ generated (fun _ : Unit => u) := by
  have hu : firstChaosEmbedding u ∈ generated (fun _ : Unit => u) := by
    apply firstChaos_mem_generated_of_sourceSpan
    exact (Submodule.span ℝ (Set.range (fun _ : Unit => u))).le_topologicalClosure
      (Submodule.subset_span ⟨(), rfl⟩)
  exact (hc.comp_aestronglyMeasurable hu).congr (testClass_coeFn u hc hA).symm

theorem test_pairing_projection (u : CoefficientSpace) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) (g : GaussianL2) :
    inner ℝ g (testClass u hc hA) =
      inner ℝ (conditionalProjection (fun _ : Unit => u) g) (testClass u hc hA) := by
  have he := (generated (fun _ : Unit => u)).starProjection_inner_eq_zero g _
    (testClass_generated u hc hA)
  rw [inner_sub_left] at he
  exact sub_eq_zero.mp he

def regression (u v : CoefficientSpace) : ℝ := inner ℝ u v / ‖u‖^2

theorem regression_energy (u v : CoefficientSpace) :
    regression u v * ‖u‖^2 = inner ℝ u v := by
  by_cases hu : u = 0
  · simp [hu, regression]
  · exact div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu))

theorem first_pairing (u v : CoefficientSpace) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    inner ℝ (firstChaosEmbedding v) (testClass u hc hA) =
      regression u v * inner ℝ (firstChaosEmbedding u) (testClass u hc hA) := by
  rw [test_pairing_projection u hc hA,
    conditional_firstChaos_projection,
    FractionalCurrentObservationObstruction.source_projection_single,
    map_smul, real_inner_smul_left]
  rfl

theorem wick_two_smul (a : ℝ) (u : CoefficientSpace) :
    (wick (a • u) 2 : GaussianL2) = a^2 • (wick u 2 : GaussianL2) := by
  apply Lp.ext
  filter_upwards [core_coeFn (a • u) (‖a • u‖^2) 2,
    core_coeFn u (‖u‖^2) 2,
    Lp.coeFn_smul (a^2) (wick u 2 : GaussianL2),
    Lp.coeFn_smul a (firstChaosEmbedding u)] with ω ha hu hs he
  change (wick (a • u) 2 : GaussianL2) ω = _ at ha
  change (wick u 2 : GaussianL2) ω = _ at hu
  rw [ha, hs, Pi.smul_apply, hu, value_two, value_two, map_smul]
  rw [he, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  simp only [smul_eq_mul, mul_pow, sq_abs]
  ring

theorem second_pairing (u v : CoefficientSpace) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    inner ℝ (wick v 2 : GaussianL2) (testClass u hc hA) =
      (regression u v)^2 * inner ℝ (wick u 2 : GaussianL2) (testClass u hc hA) := by
  rw [test_pairing_projection u hc hA,
    conditional_wick_projection,
    FractionalCurrentObservationObstruction.source_projection_single,
    wick_two_smul, real_inner_smul_left]
  rfl

theorem first_pairing_integral (u v : CoefficientSpace) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    inner ℝ (firstChaosEmbedding v) (testClass u hc hA) =
      ∫ ω, firstChaosEmbedding v ω * φ (firstChaosEmbedding u ω) ∂gaussianProduct := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [testClass_coeFn u hc hA] with ω he
  simp only [Real.inner_apply, he, mul_comm]

theorem second_pairing_integral (u v : CoefficientSpace) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    inner ℝ (wick v 2 : GaussianL2) (testClass u hc hA) =
      ∫ ω, ((firstChaosEmbedding v ω)^2 - ‖v‖^2) * φ (firstChaosEmbedding u ω)
        ∂gaussianProduct := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [testClass_coeFn u hc hA, core_coeFn v (‖v‖^2) 2] with ω he hv
  change (wick v 2 : GaussianL2) ω = _ at hv
  simp only [Real.inner_apply, he, hv, value_two, mul_comm]

theorem first_mixed_integrable (u v : CoefficientSpace) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    Integrable (fun ω => firstChaosEmbedding v ω * φ (firstChaosEmbedding u ω))
      gaussianProduct :=
  (Lp.memLp (firstChaosEmbedding v)).integrable_mul (bounded_comp_memLp u hc hA)

theorem second_mixed_integrable (u v : CoefficientSpace) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    Integrable (fun ω => (firstChaosEmbedding v ω)^2 * φ (firstChaosEmbedding u ω))
      gaussianProduct := by
  have hi := (Lp.memLp (firstChaosEmbedding v)).integrable_sq
  apply Integrable.mono' (hi.mul_const A)
    (((Lp.stronglyMeasurable (firstChaosEmbedding v)).pow 2).mul
      (hc.comp_stronglyMeasurable (Lp.stronglyMeasurable _))).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    change ‖(firstChaosEmbedding v ω)^2 * φ (firstChaosEmbedding u ω)‖ ≤
      (firstChaosEmbedding v ω)^2 * A
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hA _) (sq_nonneg _)

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {A B C : ℝ}
  (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖deriv φ x‖ ≤ B)
  (hC : ∀ x, ‖deriv (deriv φ) x‖ ≤ C)

include hφ hA hB in
theorem first_mixed (u v : CoefficientSpace) :
    (∫ ω, firstChaosEmbedding v ω * φ (firstChaosEmbedding u ω) ∂gaussianProduct) =
      inner ℝ u v * ∫ ω, deriv φ (firstChaosEmbedding u ω) ∂gaussianProduct := by
  rw [← first_pairing_integral u v hφ.continuous hA, first_pairing,
    first_pairing_integral, first_diagonal hφ hA hB, ← mul_assoc, regression_energy]

include hφ hA hB hC in
theorem second_centered_mixed (u v : CoefficientSpace) :
    (∫ ω, ((firstChaosEmbedding v ω)^2 - ‖v‖^2) * φ (firstChaosEmbedding u ω)
      ∂gaussianProduct) =
      (inner ℝ u v)^2 * ∫ ω, deriv (deriv φ) (firstChaosEmbedding u ω)
        ∂gaussianProduct := by
  rw [← second_pairing_integral u v hφ.continuous hA, second_pairing,
    second_pairing_integral, second_diagonal hφ hA hB hC]
  have he := congrArg (fun x : ℝ => x^2) (regression_energy u v)
  have hn : (regression u v)^2 * ‖u‖^4 = (inner ℝ u v)^2 := by
    nlinarith only [he]
  rw [← mul_assoc, hn]

include hφ hA hB hC in
/-- The uncentered second mixed moment on its genuine integrable domain. -/
theorem second_mixed (u v : CoefficientSpace) :
    (∫ ω, (firstChaosEmbedding v ω)^2 * φ (firstChaosEmbedding u ω) ∂gaussianProduct) =
      ‖v‖^2 * (∫ ω, φ (firstChaosEmbedding u ω) ∂gaussianProduct) +
      (inner ℝ u v)^2 * ∫ ω, deriv (deriv φ) (firstChaosEmbedding u ω)
        ∂gaussianProduct := by
  have he := second_centered_mixed hφ hA hB hC u v
  have hf : (fun ω => ((firstChaosEmbedding v ω)^2 - ‖v‖^2) *
      φ (firstChaosEmbedding u ω)) = fun ω =>
      (firstChaosEmbedding v ω)^2 * φ (firstChaosEmbedding u ω) -
        ‖v‖^2 * φ (firstChaosEmbedding u ω) := by funext ω; ring
  rw [hf, integral_sub (second_mixed_integrable u v hφ.continuous hA)
    (((bounded_comp_memLp u hφ.continuous hA).integrable (by norm_num)).const_mul _),
    integral_const_mul] at he
  linarith

end OperatorDerivativeRewrite.Foundation.IBMFirstChaosMixedStein
