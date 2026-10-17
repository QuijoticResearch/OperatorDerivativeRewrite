import Foundation.GaussianSmoothHeatMartingale
import Foundation.BrownianAugmentedMartingales
import Foundation.AmbientMartingaleModification

/-! Actual real Fourier martingales at every frequency. These are constructed
from the verified backward heat calculus, not a strong Markov assumption. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianFourierMartingales
open InfiniteGaussian IBMConstructedSources GaussianSmoothHeatMartingale
open BrownianMassClockStoppingTime
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

def cosine (u x : ℝ) : ℝ := Real.cos (u*x)
def sine (u x : ℝ) : ℝ := Real.sin (u*x)

theorem cosine_smooth (u : ℝ) : ContDiff ℝ 3 (cosine u) :=
  Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

theorem sine_smooth (u : ℝ) : ContDiff ℝ 3 (sine u) :=
  Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

theorem cosine_first (u : ℝ) : deriv (cosine u) = fun x => -u*sine u x := by
  funext x
  have hh := ((hasDerivAt_const_mul u (x := x)).cos).deriv
  change deriv (fun y => Real.cos (u*y)) x = -u*Real.sin (u*x)
  rw [hh]
  ring

theorem sine_first (u : ℝ) : deriv (sine u) = fun x => u*cosine u x := by
  funext x
  have hh := ((hasDerivAt_const_mul u (x := x)).sin).deriv
  change deriv (fun y => Real.sin (u*y)) x = u*Real.cos (u*x)
  rw [hh]
  ring

theorem cosine_second (u : ℝ) : deriv (deriv (cosine u)) = fun x => -(u^2)*cosine u x := by
  funext x
  rw [cosine_first,deriv_const_mul_field,sine_first]
  ring

theorem sine_second (u : ℝ) : deriv (deriv (sine u)) = fun x => -(u^2)*sine u x := by
  funext x
  rw [sine_first,deriv_const_mul_field,cosine_first]
  ring

theorem cosine_third (u : ℝ) : deriv (deriv (deriv (cosine u))) = fun x => u^3*sine u x := by
  funext x
  rw [cosine_second,deriv_const_mul_field,cosine_first]
  ring

theorem sine_third (u : ℝ) : deriv (deriv (deriv (sine u))) = fun x => -(u^3)*cosine u x := by
  funext x
  rw [sine_second,deriv_const_mul_field,sine_first]
  ring

theorem cosine_bound (c u x : ℝ) : ‖c*cosine u x‖ ≤ ‖c‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by
    simpa only [cosine,Real.norm_eq_abs] using Real.abs_cos_le_one (u*x))

theorem sine_bound (c u x : ℝ) : ‖c*sine u x‖ ≤ ‖c‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by
    simpa only [sine,Real.norm_eq_abs] using Real.abs_sin_le_one (u*x))

def weight (u t : ℝ) : ℝ := Real.exp (u^2*t/2)

theorem weight_smooth (u : ℝ) : ContDiff ℝ 1 (weight u) := by
  exact Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).div_const 2)

theorem weight_deriv (u t : ℝ) : deriv (weight u) t = u^2/2*weight u t := by
  have hh := (((hasDerivAt_const_mul (u^2) (x := t)).div_const 2).exp).deriv
  change deriv (fun s => Real.exp (u^2*s/2)) t = u^2/2*Real.exp (u^2*t/2)
  simpa only [mul_comm] using hh

theorem cosine_raw_martingale (u : ℝ) :
    Martingale (fun (t : ℝ≥0) ω => weight u t*cosine u (GaussianTimeProcess.process t ω))
      GaussianTimeProcess.naturalFiltration gaussianProduct := by
  have h0 : LipschitzWith ‖u‖₊ (cosine u) := by
    apply lipschitzWith_of_nnnorm_deriv_le ((cosine_smooth u).differentiable (by norm_num))
    intro x
    rw [cosine_first]
    have hb : ‖-u*sine u x‖ ≤ ‖u‖ := by
      simpa only [norm_neg] using sine_bound (-u) u x
    exact_mod_cast hb
  have h1 : LipschitzWith ‖u^2‖₊ (deriv (cosine u)) := by
    apply lipschitzWith_of_nnnorm_deriv_le
      ((cosine_smooth u).of_le (by norm_num)).differentiable_deriv_two
    intro x
    rw [cosine_second]
    have hb : ‖-(u^2)*cosine u x‖ ≤ ‖u^2‖ := by
      simpa only [norm_neg] using cosine_bound (-(u^2)) u x
    exact_mod_cast hb
  have hd : Differentiable ℝ (deriv (deriv (cosine u))) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      (cosine_smooth u).differentiable_iteratedDeriv 2 (by norm_num)
  have h2 : LipschitzWith ‖u^3‖₊ (deriv (deriv (cosine u))) := by
    apply lipschitzWith_of_nnnorm_deriv_le hd
    intro x
    rw [cosine_third]
    have hb : ‖u^3*sine u x‖ ≤ ‖u^3‖ := sine_bound (u^3) u x
    exact_mod_cast hb
  have h3 : ∀ x, ‖iteratedDeriv 3 (cosine u) x‖ ≤ ‖u^3‖ := by
    intro x
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,cosine_third] using
      sine_bound (u^3) u x
  have hh : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝ,
      deriv (weight u) t*cosine u x+(1/2 : ℝ)*weight u t*deriv (deriv (cosine u)) x = 0 := by
    intro t _ x
    rw [weight_deriv,cosine_second]
    ring
  exact heat_martingale (cosine u) (cosine_smooth u) h0 h1 h2 ‖u^3‖ h3
    (weight u) (weight_smooth u) hh

theorem sine_raw_martingale (u : ℝ) :
    Martingale (fun (t : ℝ≥0) ω => weight u t*sine u (GaussianTimeProcess.process t ω))
      GaussianTimeProcess.naturalFiltration gaussianProduct := by
  have h0 : LipschitzWith ‖u‖₊ (sine u) := by
    apply lipschitzWith_of_nnnorm_deriv_le ((sine_smooth u).differentiable (by norm_num))
    intro x
    rw [sine_first]
    exact_mod_cast cosine_bound u u x
  have h1 : LipschitzWith ‖u^2‖₊ (deriv (sine u)) := by
    apply lipschitzWith_of_nnnorm_deriv_le
      ((sine_smooth u).of_le (by norm_num)).differentiable_deriv_two
    intro x
    rw [sine_second]
    have hb : ‖-(u^2)*sine u x‖ ≤ ‖u^2‖ := by
      simpa only [norm_neg] using sine_bound (-(u^2)) u x
    exact_mod_cast hb
  have hd : Differentiable ℝ (deriv (deriv (sine u))) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      (sine_smooth u).differentiable_iteratedDeriv 2 (by norm_num)
  have h2 : LipschitzWith ‖u^3‖₊ (deriv (deriv (sine u))) := by
    apply lipschitzWith_of_nnnorm_deriv_le hd
    intro x
    rw [sine_third]
    have hb : ‖-(u^3)*cosine u x‖ ≤ ‖u^3‖ := by
      simpa only [norm_neg] using cosine_bound (-(u^3)) u x
    exact_mod_cast hb
  have h3 : ∀ x, ‖iteratedDeriv 3 (sine u) x‖ ≤ ‖u^3‖ := by
    intro x
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,sine_third,norm_neg] using
      cosine_bound (-(u^3)) u x
  have hh : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝ,
      deriv (weight u) t*sine u x+(1/2 : ℝ)*weight u t*deriv (deriv (sine u)) x = 0 := by
    intro t _ x
    rw [weight_deriv,sine_second]
    ring
  exact heat_martingale (sine u) (sine_smooth u) h0 h1 h2 ‖u^3‖ h3
    (weight u) (weight_smooth u) hh

def cosineProcess (u : ℝ) (t : ℝ≥0) (ω : SampleSpace) : ℝ :=
  weight u t*cosine u (clockPath ω t)

def sineProcess (u : ℝ) (t : ℝ≥0) (ω : SampleSpace) : ℝ :=
  weight u t*sine u (clockPath ω t)

theorem cosine_continuous (u : ℝ) (ω : SampleSpace) :
    Continuous (fun t => cosineProcess u t ω) :=
  ((weight_smooth u).continuous.comp continuous_subtype_val).mul
    ((cosine_smooth u).continuous.comp (clockPath ω).continuous)

theorem sine_continuous (u : ℝ) (ω : SampleSpace) :
    Continuous (fun t => sineProcess u t ω) :=
  ((weight_smooth u).continuous.comp continuous_subtype_val).mul
    ((sine_smooth u).continuous.comp (clockPath ω).continuous)

theorem cosine_martingale (u : ℝ) :
    Martingale (cosineProcess u) augmentedPast gaussianProduct := by
  apply AmbientMartingaleModification.martingale_modification gaussianProduct
    GaussianTimeProcess.naturalFiltration _ _ (cosine_raw_martingale u)
  · intro t
    exact (((cosine_smooth u).continuous.measurable.comp
      (BrownianAugmentedMartingales.brownian_coordinate_measurable t)).const_mul (weight u t))
  · intro t
    filter_upwards [clockPath_coordinate_ae t] with ω hω
    change weight u t*cosine u (clockPath ω t) = _
    rw [hω]

theorem sine_martingale (u : ℝ) :
    Martingale (sineProcess u) augmentedPast gaussianProduct := by
  apply AmbientMartingaleModification.martingale_modification gaussianProduct
    GaussianTimeProcess.naturalFiltration _ _ (sine_raw_martingale u)
  · intro t
    exact (((sine_smooth u).continuous.measurable.comp
      (BrownianAugmentedMartingales.brownian_coordinate_measurable t)).const_mul (weight u t))
  · intro t
    filter_upwards [clockPath_coordinate_ae t] with ω hω
    change weight u t*sine u (clockPath ω t) = _
    rw [hω]

end OperatorDerivativeRewrite.Foundation.BrownianFourierMartingales
