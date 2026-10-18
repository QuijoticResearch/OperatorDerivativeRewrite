import Foundation.IBMSchwartzSecondProjection
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Differentiating genuine Schwartz Gaussian means in the source Hilbert
space. The quadratic remainder includes the zero observation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMGaussianMeanDerivative
open InfiniteGaussian IBMCorrectionStein IBMShiftedJetMoments IBMFirstChaosMixedStein

theorem first_order_remainder_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {C : ℝ} (hC : ∀ x, ‖deriv (deriv φ) x‖ ≤ C) (x y : ℝ) :
    ‖φ y-φ x-deriv φ x*(y-x)‖ ≤ (C/2)*|y-x|^2 := by
  by_cases hxy : x=y
  · subst y
    simp
  obtain ⟨z, _, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hxy hφ.contDiffOn
  have hd : iteratedDerivWithin 1 φ (uIcc x y) x = deriv φ x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      iteratedDerivWithin_eq_iteratedDeriv (n := 1) (uniqueDiffOn_uIcc hxy)
        (hφ.of_le (by norm_num)).contDiffAt left_mem_uIcc
  have he : taylorWithinEval φ 1 (uIcc x y) x y = φ x+deriv φ x*(y-x) := by
    rw [taylorWithinEval_succ φ 0, taylor_within_zero_eval, hd]
    norm_num
    ring
  rw [he] at hz
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hz
  norm_num at hz
  have hr : φ y-φ x-deriv φ x*(y-x) = deriv (deriv φ) z*(y-x)^2/2 := by
    linarith
  rw [hr, norm_div, norm_mul, norm_pow, Real.norm_eq_abs (y-x)]
  norm_num
  have ht := mul_le_mul_of_nonneg_right (hC z) (sq_nonneg (y-x))
  simp only [Real.norm_eq_abs] at ht
  nlinarith

theorem mean_remainder_bound (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v : CoefficientSpace) (j : ℕ) :
    ‖M g a v j 0-M g a u j 0-inner ℝ u (v-u)*M g a u (j+2) 0‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 (jet g (j+2))/2)*‖v-u‖^2 := by
  let R : SampleSpace → ℝ := fun ω =>
    shiftedJet g a j (firstChaosEmbedding v ω)-shiftedJet g a j (firstChaosEmbedding u ω)-
      firstChaosEmbedding (v-u) ω*shiftedJet g a (j+1) (firstChaosEmbedding u ω)
  have hiu := (IBMFirstChaosDiagonalStein.bounded_comp_memLp u
    (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)).integrable (by norm_num)
  have hiv := (IBMFirstChaosDiagonalStein.bounded_comp_memLp v
    (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)).integrable (by norm_num)
  have him := first_mixed_integrable u (v-u) (shiftedJet_smooth g a (j+1)).continuous
    (shiftedJet_bound g a (j+1))
  have hir : Integrable R gaussianProduct := (hiv.sub hiu).sub him
  have hid : Integrable (fun ω => shiftedJet g a j (firstChaosEmbedding v ω)-
      shiftedJet g a j (firstChaosEmbedding u ω)) gaussianProduct := hiv.sub hiu
  have he : (∫ ω, R ω ∂gaussianProduct) =
      M g a v j 0-M g a u j 0-inner ℝ u (v-u)*M g a u (j+2) 0 := by
    change (∫ ω, (shiftedJet g a j (firstChaosEmbedding v ω)-
      shiftedJet g a j (firstChaosEmbedding u ω))-
      firstChaosEmbedding (v-u) ω*shiftedJet g a (j+1) (firstChaosEmbedding u ω)
      ∂gaussianProduct) = _
    rw [integral_sub hid him, integral_sub hiv hiu, shifted_first]
    simp only [← moment_zero]
  have hb : ∀ᵐ ω ∂gaussianProduct, ‖R ω‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 (jet g (j+2))/2)*(firstChaosEmbedding (v-u) ω)^2 := by
    filter_upwards [Lp.coeFn_sub (firstChaosEmbedding v) (firstChaosEmbedding u)] with ω hs
    have hd : firstChaosEmbedding (v-u) ω = firstChaosEmbedding v ω-firstChaosEmbedding u ω := by
      rw [map_sub, hs, Pi.sub_apply]
    have ht := first_order_remainder_bound (shiftedJet_smooth g a j)
      (C := SchwartzMap.seminorm ℝ 0 0 (jet g (j+2)))
      (by simpa only [shiftedJet_deriv] using shiftedJet_bound g a (j+1+1))
      (firstChaosEmbedding u ω) (firstChaosEmbedding v ω)
    simpa only [R, shiftedJet_deriv, hd, sq_abs, mul_comm] using ht
  have his := (Lp.memLp (firstChaosEmbedding (v-u))).integrable_sq
  have hm : (∫ ω, (firstChaosEmbedding (v-u) ω)^2 ∂gaussianProduct) = ‖v-u‖^2 := by
    have hn := BochnerL2Dominated.norm_sq_integral (firstChaosEmbedding (v-u))
    simpa only [Real.norm_eq_abs, sq_abs, firstChaosEmbedding.norm_map] using hn.symm
  rw [← he]
  calc
    ‖∫ ω, R ω ∂gaussianProduct‖ ≤ ∫ ω, ‖R ω‖ ∂gaussianProduct := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (SchwartzMap.seminorm ℝ 0 0 (jet g (j+2))/2)*
        (firstChaosEmbedding (v-u) ω)^2 ∂gaussianProduct :=
      integral_mono_ae hir.norm (his.const_mul _) hb
    _ = _ := by rw [integral_const_mul, hm]

def meanDerivative (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    CoefficientSpace →L[ℝ] ℝ := M g a u (j+2) 0 • innerSL ℝ u

/-- Frechet differentiability on the whole existing source Hilbert space,
including u=0; no variance division or pathwise white-noise functional. -/
theorem mean_hasFDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    HasFDerivAt (fun v => M g a v j 0) (meanDerivative g a u j) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply (Asymptotics.IsBigO.of_bound
    (SchwartzMap.seminorm ℝ 0 0 (jet g (j+2))/2) ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := CoefficientSpace) (n := 2) (by norm_num))
  exact Eventually.of_forall fun h => by
    simpa only [meanDerivative, smul_apply, innerSL_apply_apply,
      smul_eq_mul, add_sub_cancel_left, norm_pow, norm_norm, mul_comm] using
      mean_remainder_bound g a u (u+h) j

theorem mean_comp_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    {u : ℝ → CoefficientSpace} {v : CoefficientSpace} {r : ℝ} (hu : HasDerivAt u v r) :
    HasDerivAt (fun x => M g a (u x) j 0) (inner ℝ (u r) v*M g a (u r) (j+2) 0) r := by
  simpa only [meanDerivative, smul_apply, innerSL_apply_apply,
    smul_eq_mul, mul_comm, Function.comp_def] using
    (mean_hasFDerivAt g a (u r) j).comp_hasDerivAt r hu

end OperatorDerivativeRewrite.Foundation.IBMGaussianMeanDerivative
