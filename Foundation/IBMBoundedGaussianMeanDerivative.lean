import Foundation.IBMGaussianMeanDerivative
import Foundation.IBMFourierRidgeCoefficients

/-! Differentiating an actual bounded C2 Gaussian source mean. The original
Schwartz Taylor/Stein proof needs no Schwartz hypothesis at this order. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMBoundedGaussianMeanDerivative
open InfiniteGaussian IBMFirstChaosMixedStein

def mean (φ : ℝ → ℝ) (u : CoefficientSpace) : ℝ :=
  ∫ X, φ (firstChaosEmbedding u X) ∂gaussianProduct

def secondMean (φ : ℝ → ℝ) (u : CoefficientSpace) : ℝ :=
  ∫ X, deriv (deriv φ) (firstChaosEmbedding u X) ∂gaussianProduct

def derivative (φ : ℝ → ℝ) (u : CoefficientSpace) : CoefficientSpace →L[ℝ] ℝ :=
  secondMean φ u • innerSL ℝ u

theorem first_mixed_C1 {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {L M : ℝ}
    (hL : ∀ x, ‖ψ x‖ ≤ L) (hM : ∀ x, ‖deriv ψ x‖ ≤ M)
    (u v : CoefficientSpace) :
    (∫ X, firstChaosEmbedding v X*ψ (firstChaosEmbedding u X) ∂gaussianProduct) =
      inner ℝ u v*(∫ X, deriv ψ (firstChaosEmbedding u X) ∂gaussianProduct) := by
  have hdiag : (∫ X, firstChaosEmbedding u X*ψ (firstChaosEmbedding u X) ∂gaussianProduct) =
      ‖u‖^2*(∫ X, deriv ψ (firstChaosEmbedding u X) ∂gaussianProduct) := by
    rw [IBMFirstChaosDiagonalStein.integral_transport u (f := fun x => x*ψ x)
      (measurable_id.mul hψ.continuous.measurable),
      IBMFirstChaosDiagonalStein.integral_transport u hψ.continuous_deriv_one.measurable]
    let s : ℝ := 2*‖u‖
    have hc : Continuous (fun x => ψ (s*x)) := hψ.continuous.comp (continuous_const.mul continuous_id)
    have hd : Continuous (fun x => deriv ψ (s*x)) :=
      hψ.continuous_deriv_one.comp (continuous_const.mul continuous_id)
    have hD (x : ℝ) : HasDerivAt (fun t => ψ (s*t)) (s*deriv ψ (s*x)) x := by
      have ht := ((hψ.differentiable (by norm_num) (s*x)).hasDerivAt.comp x
        ((hasDerivAt_id x).const_mul s))
      convert ht using 1 <;> first | rfl | ring
    have he := HelicalWeightedPressureIBP.stein_integrable hD
      (IBMScaledGaussianStein.bounded_integrable hc (fun x => hL _))
      ((IBMScaledGaussianStein.bounded_integrable hd (fun x => hM _)).const_mul s)
      (IBMScaledGaussianStein.coordinate_mul_integrable hc (fun x => hL _))
    rw [integral_const_mul] at he
    have hf : (fun x : ℝ => (s*x)*ψ (s*x)) = fun x => s*(x*ψ (s*x)) := by
      funext x; ring
    change (∫ x, (s*x)*ψ (s*x) ∂HelicalWeightedPressureIBP.ν) = _
    rw [hf,integral_const_mul]
    dsimp [s] at he ⊢
    linear_combination -(2*‖u‖/4)*he
  rw [← first_pairing_integral u v hψ.continuous hL,first_pairing,
    first_pairing_integral,hdiag,← mul_assoc,regression_energy]

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {A B C : ℝ}
  (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖deriv φ x‖ ≤ B)
  (hC : ∀ x, ‖deriv (deriv φ) x‖ ≤ C)

include hφ hA hB hC in
theorem mean_remainder_bound (u v : CoefficientSpace) :
    ‖mean φ v-mean φ u-inner ℝ u (v-u)*secondMean φ u‖ ≤ (C/2)*‖v-u‖^2 := by
  let R : SampleSpace → ℝ := fun ω =>
    φ (firstChaosEmbedding v ω)-φ (firstChaosEmbedding u ω)-
      firstChaosEmbedding (v-u) ω*deriv φ (firstChaosEmbedding u ω)
  have hiu := (IBMFirstChaosDiagonalStein.bounded_comp_memLp u
    hφ.continuous hA).integrable (by norm_num)
  have hiv := (IBMFirstChaosDiagonalStein.bounded_comp_memLp v
    hφ.continuous hA).integrable (by norm_num)
  have him := first_mixed_integrable u (v-u) (hφ.continuous_deriv (by norm_num))
    hB
  have hir : Integrable R gaussianProduct := (hiv.sub hiu).sub him
  have hid : Integrable (fun ω => φ (firstChaosEmbedding v ω)-
      φ (firstChaosEmbedding u ω)) gaussianProduct := hiv.sub hiu
  have he : (∫ ω, R ω ∂gaussianProduct) =
      mean φ v-mean φ u-inner ℝ u (v-u)*secondMean φ u := by
    change (∫ ω, (φ (firstChaosEmbedding v ω)-
      φ (firstChaosEmbedding u ω))-
      firstChaosEmbedding (v-u) ω*deriv φ (firstChaosEmbedding u ω)
      ∂gaussianProduct) = _
    rw [integral_sub hid him, integral_sub hiv hiu,first_mixed_C1
      (RealSteklovApprox.deriv_contDiff_one φ hφ) hB hC]
    rfl
  have hb : ∀ᵐ ω ∂gaussianProduct, ‖R ω‖ ≤
      (C/2)*(firstChaosEmbedding (v-u) ω)^2 := by
    filter_upwards [Lp.coeFn_sub (firstChaosEmbedding v) (firstChaosEmbedding u)] with ω hs
    have hd : firstChaosEmbedding (v-u) ω = firstChaosEmbedding v ω-firstChaosEmbedding u ω := by
      rw [map_sub, hs, Pi.sub_apply]
    have ht := IBMGaussianMeanDerivative.first_order_remainder_bound hφ hC
      (firstChaosEmbedding u ω) (firstChaosEmbedding v ω)
    simpa only [R,hd,sq_abs,mul_comm] using ht
  have his := (Lp.memLp (firstChaosEmbedding (v-u))).integrable_sq
  have hm : (∫ ω, (firstChaosEmbedding (v-u) ω)^2 ∂gaussianProduct) = ‖v-u‖^2 := by
    have hn := BochnerL2Dominated.norm_sq_integral (firstChaosEmbedding (v-u))
    simpa only [Real.norm_eq_abs, sq_abs, firstChaosEmbedding.norm_map] using hn.symm
  rw [← he]
  calc
    ‖∫ ω, R ω ∂gaussianProduct‖ ≤ ∫ ω, ‖R ω‖ ∂gaussianProduct := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (C/2)*
        (firstChaosEmbedding (v-u) ω)^2 ∂gaussianProduct :=
      integral_mono_ae hir.norm (his.const_mul _) hb
    _ = _ := by rw [integral_const_mul, hm]

include hφ hA hB hC in
theorem mean_hasFDerivAt (u : CoefficientSpace) :
    HasFDerivAt (mean φ) (derivative φ u) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply (Asymptotics.IsBigO.of_bound (C/2) ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := CoefficientSpace) (n := 2) (by norm_num))
  exact Eventually.of_forall fun h => by
    simpa only [derivative,smul_apply,innerSL_apply_apply,smul_eq_mul,
      add_sub_cancel_left,norm_pow,norm_norm,mul_comm] using
        mean_remainder_bound hφ hA hB hC u (u+h)

theorem derivative_coefficient (u v : CoefficientSpace) :
    derivative φ u v = 2*IBMBoundedC2SecondProjection.coefficient φ u*inner ℝ u v := by
  simp only [derivative,secondMean,IBMBoundedC2SecondProjection.coefficient,
    smul_apply,innerSL_apply_apply,smul_eq_mul]
  ring

include hφ hB hC in
theorem derivative_bound (u : CoefficientSpace) : ‖derivative φ u‖ ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have htest : ‖testClass u (hφ.continuous_deriv (by norm_num)) hB‖ ≤ B := by
    apply le_trans (Lp.norm_le_of_ae_bound hB0 ?_)
    · simp [measureUnivNNReal]
    · filter_upwards [testClass_coeFn u (hφ.continuous_deriv (by norm_num)) hB] with X hX
      rw [hX]
      exact hB _
  apply ContinuousLinearMap.opNorm_le_bound _ hB0
  intro v
  have he : derivative φ u v =
      inner ℝ (firstChaosEmbedding v) (testClass u (hφ.continuous_deriv (by norm_num)) hB) := by
    rw [first_pairing_integral]
    rw [first_mixed_C1 (RealSteklovApprox.deriv_contDiff_one φ hφ) hB hC]
    simp only [derivative,secondMean,smul_apply,innerSL_apply_apply,smul_eq_mul,mul_comm]
  rw [he]
  apply (norm_inner_le_norm _ _).trans
  rw [firstChaosEmbedding.norm_map]
  nlinarith [norm_nonneg v]

end OperatorDerivativeRewrite.Foundation.IBMBoundedGaussianMeanDerivative
