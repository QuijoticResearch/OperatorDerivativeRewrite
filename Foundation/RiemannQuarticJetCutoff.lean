import Foundation.RiemannQuarticCutoff
import Foundation.RiemannQuarticEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Effective bounds for actual complex Fourier jets on the whole real
spatial axis, rather than only the scalar kernel envelope. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticJetCutoff
open RiemannQuarticKernel RiemannQuarticDomain RiemannQuarticFlow
open RiemannQuarticEvolution RiemannQuarticCutoff

theorem integrand_norm_real (k : ℕ) (t x u : ℝ) (hu : 0 ≤ u) :
    ‖integrand k t (x : ℂ) u‖ = weighted k t 0 u := by
  have hp : ‖Complex.exp (Complex.I*(u : ℂ)*(x : ℂ))‖=1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  have hw := weighted_nonneg 0 t 0 u hu
  simp only [integrand, norm_mul, norm_pow, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg hu, one_mul, hp, mul_one]
  simp only [weighted, pow_zero, one_mul]
  ring

def cutoffJet (k : ℕ) (t : ℝ) (z : ℂ) (R : ℝ) : ℂ :=
  ∫ u in 0..R, integrand k t z u

theorem jet_minus_cutoff (k : ℕ) (t : ℝ) (z : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    jet k t z-cutoffJet k t z R = ∫ u in Ioi R, integrand k t z u := by
  have hi0 : IntegrableOn (integrand k t z) (Ici (0 : ℝ)) := integrand_integrable k t z
  have hi := hi0.mono_set Ioi_subset_Ici_self
  have h := intervalIntegral.integral_Ioi_sub_Ioi hi hR
  have he : jet k t z = ∫ u in Ioi (0 : ℝ), integrand k t z u := by
    exact integral_Ici_eq_integral_Ioi
  rw [← he] at h
  change jet k t z-(∫ u in Ioi R, integrand k t z u)=cutoffJet k t z R at h
  linear_combination h

theorem jet_cutoff_error (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    ‖jet k 8 (x : ℂ)-cutoffJet k 8 (x : ℂ) (8/5)‖ ≤ (1/10^28 : ℝ) := by
  rw [jet_minus_cutoff k 8 (x : ℂ) (8/5) (by norm_num)]
  have hs : Ioi (8/5 : ℝ) ⊆ Ici (0 : ℝ) := by
    intro u hu
    change 8/5 < u at hu
    change 0 ≤ u
    linarith
  have hi0 : IntegrableOn (integrand k 8 (x : ℂ)) (Ici (0 : ℝ)) :=
    integrand_integrable k 8 (x : ℂ)
  have hi := hi0.mono_set hs
  have hw := (weighted_integrable k 8 0).mono_set hs
  calc
    _ ≤ ∫ u in Ioi (8/5 : ℝ), ‖integrand k 8 (x : ℂ) u‖ := norm_integral_le_integral_norm _
    _ = ∫ u in Ioi (8/5 : ℝ), weighted k 8 0 u := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact integrand_norm_real k 8 x u (hs hu)
    _ ≤ _ := weighted_cutoff_error k hk

def cutoffDerivative (k : ℕ) (t : ℝ) (z : ℂ) (R : ℝ) : ℂ :=
  (cutoffJet k t z R+(-1 : ℂ)^k*cutoffJet k t (-z) R)/2

theorem derivative_cutoff_error (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    ‖iteratedDeriv k (flow 8) (x : ℂ)-cutoffDerivative k 8 (x : ℂ) (8/5)‖ ≤
      (1/10^28 : ℝ) := by
  rw [flow_iteratedDeriv]
  have hp := jet_cutoff_error k hk x
  have hm := jet_cutoff_error k hk (-x)
  simp only [Complex.ofReal_neg] at hm
  have he : symmetricJet k 8 (x : ℂ)-cutoffDerivative k 8 (x : ℂ) (8/5) =
      ((jet k 8 (x : ℂ)-cutoffJet k 8 (x : ℂ) (8/5))+
        (-1 : ℂ)^k*(jet k 8 (-(x : ℂ))-cutoffJet k 8 (-(x : ℂ)) (8/5)))/2 := by
    unfold symmetricJet cutoffDerivative
    ring
  rw [he, norm_div]
  have hn : ‖(-1 : ℂ)^k‖=1 := by simp
  have h := norm_add_le (jet k 8 (x : ℂ)-cutoffJet k 8 (x : ℂ) (8/5))
    ((-1 : ℂ)^k*(jet k 8 (-(x : ℂ))-cutoffJet k 8 (-(x : ℂ)) (8/5)))
  rw [norm_mul, hn, one_mul] at h
  norm_num only [Complex.norm_ofNat] at *
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticJetCutoff
