import Foundation.RiemannThetaModularity
import Foundation.RiemannQuarticDomain

/-! Integrability and actual endpoint decay for the theta primitive and its derivative. -/
noncomputable section
open MeasureTheory Filter Set Real Asymptotics
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannThetaDecay
open RiemannQuarticKernel RiemannQuarticDomain RiemannThetaDifferentiation

def tiltedTheta (k : ℕ) (a u : ℝ) : ℝ := exp (a*u)*thetaMoment k (exp (4*u))

theorem tiltedTheta_isBigO (k : ℕ) (a : ℝ) :
    tiltedTheta k a =O[atTop] fun u : ℝ => exp (-u) := by
  apply IsBigO.of_bound (thetaMoment k (1/2))
  filter_upwards [quartic_exponent_dominated 0 (a+1), eventually_ge_atTop (0 : ℝ)] with u he hu
  have hθ := thetaMoment_decay k (exp (4*u)) (one_le_exp (by positivity))
  have hpos := thetaMoment_nonneg k (exp (4*u))
  have hpos0 := thetaMoment_nonneg k (1/2)
  simp only [tiltedTheta, Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _),
    abs_of_nonneg hpos]
  calc
    _ ≤ exp (a*u)*(thetaMoment k (1/2)*exp (-Real.pi*exp (4*u)/2)) :=
      mul_le_mul_of_nonneg_left hθ (exp_pos _).le
    _ = thetaMoment k (1/2)*exp (a*u-Real.pi*exp (4*u)/2) := by
      rw [sub_eq_add_neg, exp_add]
      ring
    _ ≤ thetaMoment k (1/2)*exp (-u) := by
      apply mul_le_mul_of_nonneg_left _ hpos0
      apply exp_le_exp.mpr
      simp only [zero_mul, zero_add] at he
      linarith

theorem tiltedTheta_integrable (k : ℕ) (a : ℝ) :
    IntegrableOn (tiltedTheta k a) (Ici 0) := by
  apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
  apply integrable_of_isBigO_exp_neg (b := 1) zero_lt_one
  · exact (by fun_prop : Continuous (fun u : ℝ => exp (a*u))).continuousOn.mul
      (thetaMoment_exp_continuousOn k)
  · simpa only [neg_one_mul] using tiltedTheta_isBigO k a

theorem tiltedTheta_tendsto (k : ℕ) (a : ℝ) :
    Tendsto (tiltedTheta k a) atTop (𝓝 0) :=
  (tiltedTheta_isBigO k a).trans_tendsto Real.tendsto_exp_neg_atTop_nhds_zero

theorem psi_isBigO : psi =O[atTop] fun u : ℝ => exp (-u) := by
  have he : tiltedTheta 0 1 = psi := by funext u; simp [tiltedTheta, psi]
  rw [← he]
  exact tiltedTheta_isBigO 0 1

theorem psiPrime_isBigO : psiPrime =O[atTop] fun u : ℝ => exp (-u) := by
  have h := psi_isBigO.sub ((tiltedTheta_isBigO 2 5).const_mul_left (4*Real.pi))
  have he : psiPrime = psi - fun u => (4*Real.pi)*tiltedTheta 2 5 u := by
    funext u
    simp only [psiPrime, tiltedTheta, Pi.sub_apply]
    ring
  rw [he]
  exact h

theorem psi_integrable : IntegrableOn psi (Ici 0) := by
  have he : tiltedTheta 0 1 = psi := by funext u; simp [tiltedTheta, psi]
  rw [← he]
  exact tiltedTheta_integrable 0 1

theorem psiPrime_integrable : IntegrableOn psiPrime (Ici 0) := by
  have h := psi_integrable.sub ((tiltedTheta_integrable 2 5).const_mul (4*Real.pi))
  have he : psiPrime = psi - fun u => (4*Real.pi)*tiltedTheta 2 5 u := by
    funext u
    simp only [psiPrime, tiltedTheta, Pi.sub_apply]
    ring
  rw [he]
  exact h

theorem kernel_integrable : IntegrableOn kernel (Ici 0) := by
  have he : weighted 0 0 0 = kernel := by funext u; simp [weighted]
  rw [← he]
  exact weighted_integrable 0 0 0

theorem psiSecond_integrable : IntegrableOn psiSecond (Ici 0) := by
  have h := psi_integrable.add (kernel_integrable.const_mul 8)
  have he : psiSecond = fun u => psi u+8*kernel u := by
    funext u
    have hh := kernel_differential_identity u
    linarith
  rw [he]
  exact h

end OperatorDerivativeRewrite.Foundation.RiemannThetaDecay
