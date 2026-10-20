import Foundation.RiemannQuarticDomain

/-! All polynomial moments and all integer-even/linear exponential tilts of the
literal arithmetic kernel are genuinely integrable on the positive half-line. -/
noncomputable section
open MeasureTheory Filter Set Real Asymptotics
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenDomain
open RiemannQuarticKernel

def weighted (m k : ℕ) (T B u : ℝ) : ℝ := u^k*exp (T*u^(2*m)+B*u)*kernel u

theorem weighted_continuousOn (m k : ℕ) (T B : ℝ) :
    ContinuousOn (weighted m k T B) (Ici 0) :=
  (by fun_prop : Continuous (fun u : ℝ => u^k*exp (T*u^(2*m)+B*u))).continuousOn.mul
    kernel_continuousOn

theorem weighted_mono (m k : ℕ) {T U B C u : ℝ} (hT : T ≤ U) (hB : B ≤ C)
    (hu : 0 ≤ u) : weighted m k T B u ≤ weighted m k U C u := by
  unfold weighted
  apply mul_le_mul_of_nonneg_right _ (kernel_pos u hu).le
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
  apply exp_le_exp.mpr
  exact add_le_add (mul_le_mul_of_nonneg_right hT (pow_nonneg hu _))
    (mul_le_mul_of_nonneg_right hB hu)

theorem even_exponent_dominated (m : ℕ) (T B : ℝ) :
    ∀ᶠ u : ℝ in atTop, T*u^(2*m)+B*u ≤ Real.pi*exp (4*u)/2 := by
  have h4 := (isLittleO_pow_exp_pos_mul_atTop (2*m) (b := 4) (by norm_num)).const_mul_left T
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 1 (b := 4) (by norm_num)).const_mul_left B
  have h := (h4.add h1).bound (half_pos Real.pi_pos)
  filter_upwards [h] with u hu
  simp only [pow_one, Real.norm_eq_abs, abs_of_pos (exp_pos _)] at hu
  exact (le_abs_self _).trans (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hu)

theorem weighted_isBigO (m k : ℕ) (T B : ℝ) :
    weighted m k T B =O[atTop] (fun u : ℝ => exp (-u)) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop k (b := 1) (by norm_num)).bound zero_lt_one
  have he := even_exponent_dominated m T (B+11)
  apply IsBigO.of_bound envelopeConstant
  filter_upwards [hp, he, eventually_ge_atTop (0 : ℝ)] with u hu he hu0
  simp only [Real.norm_eq_abs, one_mul, abs_of_pos (exp_pos _)] at hu
  have hh : exp (T*u^(2*m)+B*u)*exp (9*u-Real.pi*exp (4*u)/2)*exp u ≤ exp (-u) := by
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    linarith
  change |weighted m k T B u| ≤ envelopeConstant*|exp (-u)|
  rw [weighted, abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
  calc
    _ ≤ exp u*exp (T*u^(2*m)+B*u)*
        (envelopeConstant*exp (9*u-Real.pi*exp (4*u)/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hu (exp_pos _).le)
        (kernel_decay u hu0) (abs_nonneg _) (by positivity)
    _ = envelopeConstant*(exp (T*u^(2*m)+B*u)*exp (9*u-Real.pi*exp (4*u)/2)*exp u) := by ring
    _ ≤ envelopeConstant*exp (-u) := mul_le_mul_of_nonneg_left hh envelopeConstant_nonneg

theorem weighted_integrable (m k : ℕ) (T B : ℝ) :
    IntegrableOn (weighted m k T B) (Ici 0) := by
  apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
  simpa only [neg_one_mul] using
    integrable_of_isBigO_exp_neg (b := 1) zero_lt_one
      (weighted_continuousOn m k T B) (by simpa only [neg_one_mul] using weighted_isBigO m k T B)

theorem weighted_quartic (k : ℕ) (t B u : ℝ) :
    weighted 2 k t B u=RiemannQuarticDomain.weighted k t B u := rfl

end OperatorDerivativeRewrite.Foundation.RiemannEvenDomain
