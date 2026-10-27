import Foundation.CauchyPoissonQuantitativeEntropy
/-! Off-diagonal small-time circle Poisson kernel. The drift is tangential
at the boundary; no interchange with a singular integral is asserted. -/
open Complex Filter Set
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonJumpLimit
open CauchyPoissonFlow
theorem radial_defect_derivative (q : ℝ) (hq : |q| < 1) (z : Circle) :
    HasDerivAt (fun t : ℝ => 1 - ‖evolution q t z‖^2) 2 0 := by
  have hd := evolution_derivative_zero q hq z
  have hc : (q:ℂ)/(1-(q:ℂ)^2) = ((q/(1-q^2):ℝ):ℂ) := by push_cast; rfl
  rw [hc] at hd
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  have hh := ((hr.pow 2).add (hi.pow 2)).const_sub 1
  have hz : (z : ℂ).re^2 + (z : ℂ).im^2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using (show Complex.normSq (z : ℂ) = 1 by rw [← Complex.sq_norm]; simp)
  convert hh using 1
  · funext t
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  · simp only [evolution_zero, Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_mul, add_zero, sub_zero]
    linear_combination -(2 + 2 * (q/(1-q^2)) * (z:ℂ).re) * hz
theorem off_diagonal_limit (q : ℝ) (hq : |q| < 1) (z w : Circle) (hwz : w ≠ z) :
    Tendsto (fun h : ℝ => h⁻¹ * poissonKernel 0 (evolution q h z) w)
      (𝓝[>] 0) (𝓝 (2 / ‖(w:ℂ)-(z:ℂ)‖^2)) := by
  have hn := (radial_defect_derivative q hq z).tendsto_slope_zero_right
  simp only [zero_add, evolution_zero, Circle.norm_coe, one_pow, sub_self, sub_zero,
    smul_eq_mul] at hn
  have hd : Tendsto (fun h : ℝ => ‖(w:ℂ)-evolution q h z‖^2)
      (𝓝[>] 0) (𝓝 (‖(w:ℂ)-(z:ℂ)‖^2)) := by
    have he : Tendsto (fun h : ℝ => evolution q h z) (𝓝[>] 0) (𝓝 (z:ℂ)) := by
      simpa only [evolution_zero] using
        (evolution_derivative_zero q hq z).continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    exact (tendsto_const_nhds.sub he).norm.pow 2
  have hne : ‖(w:ℂ)-(z:ℂ)‖^2 ≠ 0 := pow_ne_zero 2
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by intro h; exact hwz (Subtype.ext h))))
  convert hn.div hd hne using 1
  funext h
  simp only [poissonKernel, sub_zero, Circle.norm_coe, one_pow, Pi.div_apply]
  ring
end OperatorDerivativeRewrite.Foundation.CauchyPoissonJumpLimit









