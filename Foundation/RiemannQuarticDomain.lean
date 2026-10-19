import Foundation.RiemannQuarticKernel

/-! All polynomial moments and all quartic/linear exponential tilts of the
literal arithmetic kernel are genuinely integrable on the positive half-line. -/
noncomputable section
open MeasureTheory Filter Set Real Asymptotics
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticDomain
open RiemannQuarticKernel

def weighted (k : ℕ) (T B u : ℝ) : ℝ := u^k*exp (T*u^4+B*u)*kernel u

theorem weighted_continuousOn (k : ℕ) (T B : ℝ) :
    ContinuousOn (weighted k T B) (Ici 0) :=
  (by fun_prop : Continuous (fun u : ℝ => u^k*exp (T*u^4+B*u))).continuousOn.mul
    kernel_continuousOn

theorem weighted_mono (k : ℕ) {T U B C u : ℝ} (hT : T ≤ U) (hB : B ≤ C)
    (hu : 0 ≤ u) : weighted k T B u ≤ weighted k U C u := by
  unfold weighted
  apply mul_le_mul_of_nonneg_right _ (kernel_pos u hu).le
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
  apply exp_le_exp.mpr
  exact add_le_add (mul_le_mul_of_nonneg_right hT (pow_nonneg hu _))
    (mul_le_mul_of_nonneg_right hB hu)

theorem quartic_exponent_dominated (T B : ℝ) :
    ∀ᶠ u : ℝ in atTop, T*u^4+B*u ≤ Real.pi*exp (4*u)/2 := by
  have h4 := (isLittleO_pow_exp_pos_mul_atTop 4 (b := 4) (by norm_num)).const_mul_left T
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 1 (b := 4) (by norm_num)).const_mul_left B
  have h := (h4.add h1).bound (half_pos Real.pi_pos)
  filter_upwards [h] with u hu
  simp only [pow_one, Real.norm_eq_abs, abs_of_pos (exp_pos _)] at hu
  exact (le_abs_self _).trans (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hu)

theorem weighted_isBigO (k : ℕ) (T B : ℝ) :
    weighted k T B =O[atTop] (fun u : ℝ => exp (-u)) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop k (b := 1) (by norm_num)).bound zero_lt_one
  have he := quartic_exponent_dominated T (B+11)
  apply IsBigO.of_bound envelopeConstant
  filter_upwards [hp, he, eventually_ge_atTop (0 : ℝ)] with u hu he hu0
  simp only [Real.norm_eq_abs, one_mul, abs_of_pos (exp_pos _)] at hu
  have hh : exp (T*u^4+B*u)*exp (9*u-Real.pi*exp (4*u)/2)*exp u ≤ exp (-u) := by
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    linarith
  change |weighted k T B u| ≤ envelopeConstant*|exp (-u)|
  rw [weighted, abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
  calc
    _ ≤ exp u*exp (T*u^4+B*u)*
        (envelopeConstant*exp (9*u-Real.pi*exp (4*u)/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hu (exp_pos _).le)
        (kernel_decay u hu0) (abs_nonneg _) (by positivity)
    _ = envelopeConstant*(exp (T*u^4+B*u)*exp (9*u-Real.pi*exp (4*u)/2)*exp u) := by ring
    _ ≤ envelopeConstant*exp (-u) := mul_le_mul_of_nonneg_left hh envelopeConstant_nonneg

theorem weighted_integrable (k : ℕ) (T B : ℝ) :
    IntegrableOn (weighted k T B) (Ici 0) := by
  apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
  simpa only [neg_one_mul] using
    integrable_of_isBigO_exp_neg (b := 1) zero_lt_one
      (weighted_continuousOn k T B) (by simpa only [neg_one_mul] using weighted_isBigO k T B)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticDomain
