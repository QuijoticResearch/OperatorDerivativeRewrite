import Foundation.SU2HomogeneousExchangeTrial
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! A Jensen pressure floor for any supplied uniformly positive bounded
homogeneous eigenfunction. This proves a needed normalization bound, NOT
existence of a vacuum. It tests the specific bare exchange-trial route. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2HomogeneousEigenvalueFloor
open SU2SevenLinkTransfer SU2SevenLinkVariational SU2SevenLinkParity
open SU2HomogeneousPlaquetteObstruction SU2HomogeneousExchangeTrial

private theorem potential_mean : (∫ s, potential s ∂haar)=0 := by
  have hx := BoundedExponentialTiltResponse.bounded_power_integrable haar first first_measurable first_bound 1
  have hy := BoundedExponentialTiltResponse.bounded_power_integrable haar second second_measurable second_bound 1
  simp only [pow_one] at hx hy
  have hy0 : (∫ s, second s ∂haar)=0 := by
    simpa only [mul_one] using odd_even_orthogonal second (fun _ => 1) second_flip (fun _ => rfl)
  unfold potential
  rw [integral_div,integral_add hx hy,haar_first_mean,hy0]
  norm_num

/-- The actual Haar-stationary kinetic transfer forces lam>=1 for a uniformly
positive bounded measurable eigenfunction of the homogeneous spatial sandwich.
No spectral radius identity, eigenbranch, or existence hypothesis is concealed. -/
theorem eigenvalue_ge_one (β t lam l u : ℝ) (ψ : State → ℝ)
    (hlam : 0 < lam) (hl : 0 < l) (hψ : Measurable ψ)
    (hb : ∀ s, l ≤ ψ s ∧ ψ s ≤ u)
    (heigen : ∀ s, homogeneousStep β t ψ s=lam*ψ s) : 1 ≤ lam := by
  let q := fun s => t*potential s+Real.log (ψ s)
  let M := |t|+|Real.log l|+|Real.log u|
  have hpos (s : State) : 0 < ψ s := hl.trans_le (hb s).1
  have hq : Measurable q := (measurable_const.mul potential_measurable).add hψ.log
  have hbound (s : State) : |q s| ≤ M := by
    have hlo := Real.log_le_log hl (hb s).1
    have hup := Real.log_le_log (hpos s) (hb s).2
    have hlog : |Real.log (ψ s)| ≤ |Real.log l|+|Real.log u| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (Real.log l),le_abs_self (Real.log u),abs_nonneg (Real.log l),abs_nonneg (Real.log u)]
    have hv : |t*potential s| ≤ |t| := by
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (potential_bound s) (abs_nonneg t)
    exact (abs_add_le _ _).trans (by dsimp [M]; linarith)
  have hEq (s : State) : Real.exp (q s)=weight t s*ψ s := by
    dsimp [q]
    rw [Real.exp_add,Real.exp_log (hpos s)]
    rfl
  have hExpMeas : Measurable (fun s => Real.exp (q s)) := hq.exp
  have hExpBound (s : State) : |Real.exp (q s)| ≤ Real.exp M := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hbound s))
  have hK (s : State) : weight t s*SU2SevenLinkTransfer.step β (fun r => Real.exp (q r)) s=lam*ψ s := by
    simpa only [hEq,homogeneousStep] using heigen s
  have hpoint (s : State) : SU2SevenLinkTransfer.step β q s ≤ Real.log lam+q s-2*t*potential s := by
    letI := noise_probability β
    have hiq := step_integrable β q hq M hbound s
    have hie := step_integrable β (fun r => Real.exp (q r)) hExpMeas (Real.exp M) hExpBound s
    have hj := ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all (noise β) (fun _ => Set.mem_univ _)) hiq hie
    change Real.exp (SU2SevenLinkTransfer.step β q s) ≤ SU2SevenLinkTransfer.step β (fun r => Real.exp (q r)) s at hj
    have hrepr : SU2SevenLinkTransfer.step β (fun r => Real.exp (q r)) s=
        Real.exp (Real.log lam+Real.log (ψ s)-t*potential s) := by
      rw [Real.exp_sub,Real.exp_add,Real.exp_log hlam,Real.exp_log (hpos s)]
      apply (eq_div_iff (Real.exp_ne_zero (t*potential s))).mpr
      exact (by simpa only [weight,mul_comm] using hK s)
    rw [hrepr] at hj
    have hh := Real.exp_le_exp.mp hj
    dsimp [q]
    linarith
  have hIq : Integrable q haar := by
    apply Integrable.of_bound hq.aestronglyMeasurable M
    filter_upwards with s
    simpa only [Real.norm_eq_abs] using hbound s
  have hIK : Integrable (SU2SevenLinkTransfer.step β q) haar := by
    simpa only [one_mul] using pairing_integrable β (fun _ => 1) q measurable_const hq 1 M (fun _ => by norm_num) hbound
  have hIv := BoundedExponentialTiltResponse.bounded_power_integrable haar potential potential_measurable potential_bound 1
  simp only [pow_one] at hIv
  have hIr := ((integrable_const (Real.log lam)).add hIq).sub (hIv.const_mul (2*t))
  have hi := integral_mono hIK hIr hpoint
  rw [step_haar_stationary β q hq M hbound] at hi
  have hsub := integral_sub ((integrable_const (Real.log lam)).add hIq) (hIv.const_mul (2*t))
  have hadd := integral_add (integrable_const (Real.log lam)) hIq
  simp only [Pi.add_apply,Pi.sub_apply] at hsub hadd
  change (∫ s, q s ∂haar) ≤ ∫ s, Real.log lam+q s-(2*t)*potential s ∂haar at hi
  rw [hsub,hadd,integral_const_mul,potential_mean] at hi
  simp only [integral_const,probReal_univ,one_smul,mul_zero,sub_zero] at hi
  have hlog : 0 ≤ Real.log lam := by linarith
  have h := Real.exp_le_exp.mpr hlog
  simpa only [Real.exp_zero,Real.exp_log hlam] using h

/-- The bare exchange trial cannot yield a normalized quotient above c^4 for
ANY actual positive bounded homogeneous eigenfunction satisfying the exact
operator equation. This does not rule out corrected trials or a mass gap. -/
theorem bare_normalized_no_inflation (β t lam l u : ℝ) (ψ : State → ℝ)
    (hlam : 0 < lam) (hl : 0 < l) (hψ : Measurable ψ)
    (hb : ∀ s, l ≤ ψ s ∧ ψ s ≤ u)
    (heigen : ∀ s, homogeneousStep β t ψ s=lam*ψ s) :
    quotient β t/lam ≤ SU2WilsonConvolution.coefficient β^4 :=
  normalized_quotient_le_kinetic β t lam (eigenvalue_ge_one β t lam l u ψ hlam hl hψ hb heigen)

end OperatorDerivativeRewrite.Foundation.SU2HomogeneousEigenvalueFloor
