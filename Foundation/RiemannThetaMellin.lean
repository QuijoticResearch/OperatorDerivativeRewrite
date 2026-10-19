import Foundation.RiemannThetaCosine
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! The actual log-Mellin integrand of Mathlib's pole-removed completed zeta. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannThetaMellin
open RiemannQuarticKernel RiemannThetaDifferentiation RiemannThetaModularity
open RiemannThetaDecay RiemannThetaCosine

abbrev pair := HurwitzZeta.hurwitzEvenFEPair 0

def logIntegrand (s : ℂ) (w : ℝ) : ℂ :=
  Complex.exp (s*(w : ℂ))*pair.f_modif (Real.exp w)

theorem exponential_mellin_factor (s : ℂ) (w : ℝ) :
    (Real.exp w : ℂ)*(Real.exp w : ℂ)^(s-1) = Complex.exp (s*(w : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos w).ne'),
    ← Complex.ofReal_log (Real.exp_pos w).le, Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  ring

theorem logIntegrand_integrable (s : ℂ) : Integrable (logIntegrand s) := by
  have hi : MellinConvergent pair.f_modif s :=
    (pair.isStrongFEPair_toStrongFEPair.hasMellin s).1
  have h := (integrable_comp_exp
    (fun v : ℝ => (v : ℂ)^(s-1)*pair.f_modif v)).mpr hi
  apply h.congr
  exact Eventually.of_forall fun w => by
    dsimp only
    rw [Complex.real_smul, ← mul_assoc, exponential_mellin_factor]
    rfl

theorem lambda_zero_log_integral (s : ℂ) : pair.Λ₀ s = ∫ w, logIntegrand s w := by
  change (∫ v in Ioi (0 : ℝ), (v : ℂ)^(s-1)*pair.f_modif v) = _
  rw [← integral_comp_exp]
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    dsimp only
    rw [Complex.real_smul, ← mul_assoc, exponential_mellin_factor]
    rfl

theorem modif_positive (v : ℝ) (hv : 1 < v) :
    pair.f_modif v = (2*thetaMoment 0 v : ℝ) := by
  have hc := cosKernel_eq_thetaMoment v (by linarith)
  unfold WeakFEPair.f_modif
  rw [Pi.add_apply, indicator_of_mem (show v ∈ Ioi (1 : ℝ) from hv),
    indicator_of_notMem (notMem_Ioo_of_ge hv.le), add_zero]
  simp only [pair, HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, ite_true]
  rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero, hc]
  push_cast
  ring

theorem pair_modif_symmetry : pair.g_modif = pair.f_modif := by
  funext v
  simp only [WeakFEPair.g_modif, WeakFEPair.f_modif, pair,
    HurwitzZeta.hurwitzEvenFEPair, HurwitzZeta.evenKernel_eq_cosKernel_of_zero,
    ite_true, one_mul, inv_one]

theorem modif_reflection (w : ℝ) :
    pair.f_modif (Real.exp (-w)) =
      (Real.exp (w/2) : ℂ)*pair.f_modif (Real.exp w) := by
  have h := pair.hf_modif_FE (Real.exp w) (Real.exp_pos _)
  have hi : 1/Real.exp w = Real.exp (-w) := by rw [one_div, Real.exp_neg]
  have hp : Real.exp w^(1/2 : ℝ) = Real.exp (w/2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hi, pair_modif_symmetry] at h
  simpa only [show pair.ε=1 by rfl, show pair.k=(1/2 : ℝ) by rfl,
    one_mul, smul_eq_mul, hp] using h

theorem logIntegrand_pair (x w : ℝ) (hw : 0 < w) :
    logIntegrand ((1 : ℂ)/4+Complex.I*(x : ℂ)/4) w+
      logIntegrand ((1 : ℂ)/4+Complex.I*(x : ℂ)/4) (-w) =
      (4*Real.exp (w/4)*thetaMoment 0 (Real.exp w)*Real.cos (x*w/4) : ℝ) := by
  have hv : 1 < Real.exp w := Real.one_lt_exp_iff.mpr hw
  unfold logIntegrand
  rw [modif_reflection, modif_positive _ hv]
  simp only [Complex.ofReal_neg]
  have hp : Complex.exp (((1 : ℂ)/4+Complex.I*(x : ℂ)/4)*(w : ℂ)) =
      (Real.exp (w/4) : ℂ)*Complex.exp (((x*w/4 : ℝ) : ℂ)*Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm : Complex.exp (((1 : ℂ)/4+Complex.I*(x : ℂ)/4)*(-w : ℂ))*
      (Real.exp (w/2) : ℂ) =
      (Real.exp (w/4) : ℂ)*Complex.exp (-((x*w/4 : ℝ) : ℂ)*Complex.I) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (Complex.exp (((1 : ℂ)/4+Complex.I*(x : ℂ)/4)*(w : ℂ))+
        Complex.exp (((1 : ℂ)/4+Complex.I*(x : ℂ)/4)*(-w : ℂ))*
          (Real.exp (w/2) : ℂ))*(2*thetaMoment 0 (Real.exp w) : ℝ) := by ring
    _ = (Real.exp (w/4) : ℂ)*(2*Complex.cos ((x*w/4 : ℝ) : ℂ))*
        (2*thetaMoment 0 (Real.exp w) : ℝ) := by
      rw [hp, hm, Complex.two_cos]
      ring
    _ = _ := by rw [← Complex.ofReal_cos]; push_cast; ring

end OperatorDerivativeRewrite.Foundation.RiemannThetaMellin
