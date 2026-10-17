import Foundation.MixedCubicNinthRealization
import Mathlib.Topology.Order.IntermediateValue

/-! The quartic null boundary excludes the next mixed moment, completing degree-nine realization. -/
noncomputable section
open MeasureTheory Polynomial Set
namespace OperatorDerivativeRewrite.Foundation.MixedCubicQuarticBoundary
open MixedCubicMomentPositivity MixedCubicThirdDegree MixedCubicFourthDegree
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

theorem quartic_cross (v k c b a d e : ℝ) :
    expectation v k ((X : Polynomial ℝ)*(quartic c b a d e)^2) =
      2*v*c*b+k*(b^2+2*c*a)+3*v^2*(2*c*d+2*b*a)+
      10*v*k*(a^2+2*c*e+2*b*d)+(15*v^3+10*k^2)*(2*b*e+2*a*d)+
      105*v^2*k*(d^2+2*a*e)+(105*v^4+280*v*k^2)*2*d*e+
      (1260*v^3*k+280*k^3)*e^2 := by
  have he : (X : Polynomial ℝ)*(quartic c b a d e)^2 = c^2 • X^1+
      (2*c*b) • X^2+(b^2+2*c*a) • X^3+(2*c*d+2*b*a) • X^4+
      (a^2+2*c*e+2*b*d) • X^5+(2*b*e+2*a*d) • X^6+
      (d^2+2*a*e) • X^7+(2*d*e) • X^8+e^2 • X^9 := by
    simp only [quartic,cubic,Algebra.smul_def,map_add,map_mul,map_pow,map_ofNat]
    ring
  rw [he]
  simp only [map_add,map_smul,smul_eq_mul,expectation_X_pow]
  norm_num [moment]
  ring

theorem null_cross_value (v k : ℝ) :
    expectation v k ((X : Polynomial ℝ)*(determinantQuartic v k)^2) =
      13824*v^15*k-65664*v^12*k^3+112320*v^9*k^5+
      187920*v^6*k^7-77760*v^3*k^9+14580*k^11 := by
  rw [determinantQuartic,centeredQuartic_expansion,quartic_cross]
  unfold determinant
  ring

theorem null_cross_identity (v k : ℝ) :
    v*expectation v k ((X : Polynomial ℝ)*(determinantQuartic v k)^2) =
      (-9*k^5+48*v^3*k^3-108*v^6*k)*fourthDeterminant v k+
      864*v^10*k*(52*v^6-272*v^3*k^2+213*k^4) := by
  rw [null_cross_value]
  unfold fourthDeterminant
  ring

theorem boundary_equation (v k : ℝ) (hv : 0 < v) (h4 : fourthDeterminant v k = 0) :
    8*v^9-40*v^6*k^2-45*k^6 = 0 := by
  have he : (36*v)*(8*v^9-40*v^6*k^2-45*k^6) = fourthDeterminant v k := by
    unfold fourthDeterminant
    ring
  rw [h4] at he
  exact (mul_eq_zero.mp he).resolve_left (mul_pos (by norm_num) hv).ne'

theorem boundary_upper (v k : ℝ) (hv : 0 < v) (h4 : fourthDeterminant v k = 0) :
    5*k^2 ≤ v^3 := by
  have he := boundary_equation v k hv h4
  have hf : 0 ≤ v^6*(8*v^3-40*k^2) := by nlinarith [sq_nonneg (k^3)]
  have hx := (mul_nonneg_iff_of_pos_left (pow_pos hv 6)).mp hf
  linarith

theorem boundary_lower (v k : ℝ) (hv : 0 < v) (h4 : fourthDeterminant v k = 0) :
    v^3 < 6*k^2 := by
  have he := boundary_equation v k hv h4
  by_contra hn
  have hk : 6*k^2 ≤ v^3 := le_of_not_gt hn
  have h1 := mul_nonneg (pow_nonneg hv.le 6) (sub_nonneg.mpr hk)
  have h2 := mul_nonneg (mul_nonneg (pow_nonneg hv.le 3) (sq_nonneg k)) (sub_nonneg.mpr hk)
  have h3 := mul_nonneg (sq_nonneg (k^2)) (sub_nonneg.mpr hk)
  nlinarith [pow_pos hv 9]

theorem boundary_factor_positive (v k : ℝ) (hv : 0 < v) (h4 : fourthDeterminant v k = 0) :
    0 < 52*v^6-272*v^3*k^2+213*k^4 := by
  have hu := boundary_upper v k hv h4
  have hl := boundary_lower v k hv h4
  have h1 := mul_nonneg (pow_nonneg hv.le 3) (sub_nonneg.mpr hu)
  have h2 := mul_nonneg (pow_nonneg hv.le 3) (sub_nonneg.mpr hl.le)
  have h3 := mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hl.le)
  nlinarith [pow_pos hv 6]

theorem boundary_skew_ne_zero (v k : ℝ) (hv : 0 < v) (h4 : fourthDeterminant v k = 0) :
    k ≠ 0 := by
  have he := boundary_equation v k hv h4
  intro hk
  rw [hk] at he
  norm_num at he
  nlinarith [pow_pos hv 9]

theorem null_cross_ne_zero (v k : ℝ) (hv : 0 < v) (h4 : fourthDeterminant v k = 0) :
    expectation v k ((X : Polynomial ℝ)*(determinantQuartic v k)^2) ≠ 0 := by
  have he := null_cross_identity v k
  rw [h4,mul_zero,zero_add] at he
  have hp : 864*v^10*k*(52*v^6-272*v^3*k^2+213*k^4) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hv.ne'))
      (boundary_skew_ne_zero v k hv h4)) (boundary_factor_positive v k hv h4).ne'
  intro hn
  rw [hn,mul_zero] at he
  exact hp he.symm

theorem no_boundary_nine_moments (μ : Measure ℝ) (v k : ℝ) (hv : 0 < v)
    (h4 : fourthDeterminant v k = 0) (hi : ∀ n ≤ 9, Integrable (fun x : ℝ => x^n) μ) :
    ¬ ∀ n ≤ 9, (∫ x : ℝ, x^n ∂μ) = moment v k n := by
  intro hm
  let Q := determinantQuartic v k
  have hQ : Q.natDegree ≤ 4 := determinantQuartic_degree v k
  have hQ2 : (Q^2).natDegree ≤ 8 := natDegree_pow_le.trans (by omega)
  have hc : ((X : Polynomial ℝ)*Q^2).natDegree ≤ 9 :=
    natDegree_mul_le.trans (by simp only [natDegree_X]; omega)
  have hmatch : ∀ n ≤ 9, (∫ x : ℝ, x^n ∂μ) = expectation v k (X^n) := by
    intro n hn
    rw [expectation_X_pow]
    exact hm n hn
  obtain ⟨hiQ,heQ⟩ := TruncatedPolynomialIntegration.polynomial_integral_match μ
    (expectation v k) 9 hi hmatch (Q^2) (hQ2.trans (by omega))
  have hzero : expectation v k (Q^2) = 0 := by
    rw [show Q = determinantQuartic v k from rfl,determinantQuartic_value,h4,mul_zero]
  rw [hzero] at heQ
  have hae := (integral_eq_zero_iff_of_nonneg
    (show 0 ≤ fun x => (Q^2).eval x from fun x => by
      simpa only [eval_pow,Pi.zero_apply] using sq_nonneg (Q.eval x)) hiQ).mp heQ
  have hz : (fun x => ((X : Polynomial ℝ)*Q^2).eval x) =ᵐ[μ] 0 := by
    filter_upwards [hae] with x hx
    simp only [eval_mul,eval_X,hx,mul_zero,Pi.zero_apply]
  have he := (TruncatedPolynomialIntegration.polynomial_integral_match μ
    (expectation v k) 9 hi hmatch (X*Q^2) hc).2
  have hx : expectation v k (X*Q^2) = 0 := by
    rw [← he,integral_congr_ae hz]
    simp
  exact null_cross_ne_zero v k hv h4 hx

theorem boundary_eight_but_not_nine (v k : ℝ) (hv : 0 < v) (h4 : fourthDeterminant v k = 0) :
    (∃ μ, MixedCubicBoundaryQuartic.RepresentsEight μ v k) ∧
      ¬ ∃ μ, MixedCubicNinthRealization.RepresentsNine μ v k := by
  refine ⟨⟨MixedCubicEighthRealization.law v k,
    MixedCubicEighthRealization.law_represents_eight v k hv h4.ge⟩,?_⟩
  rintro ⟨μ,hprob,hi,hm⟩
  exact no_boundary_nine_moments μ v k hv h4 hi hm

theorem mixed_nine_realizable_iff (v k : ℝ) :
    (∃ μ, MixedCubicNinthRealization.RepresentsNine μ v k) ↔
      (v=0 ∧ k=0) ∨ (0<v ∧ 0<fourthDeterminant v k) := by
  constructor
  · intro h
    rcases MixedCubicNinthRealization.nine_parameter_necessary v k h with hz | ⟨hv,h4⟩
    · exact Or.inl hz
    · have hpos : 0 < fourthDeterminant v k := by
        by_contra hn
        have he := le_antisymm (le_of_not_gt hn) h4
        exact (boundary_eight_but_not_nine v k hv he).2 h
      exact Or.inr ⟨hv,hpos⟩
  · rintro (⟨rfl,rfl⟩ | ⟨hv,h4⟩)
    · exact ⟨Measure.dirac 0,MixedCubicNinthRealization.zero_representation⟩
    · exact ⟨MixedCubicNinthRealization.law v k
        (MixedCubicNinthRealization.steering v k (moment v k 9)),
        MixedCubicNinthRealization.strict_mixed_nine_realization v k hv h4⟩

theorem boundary_exists : ∃ k : ℝ, 0<k ∧ k<1/2 ∧ fourthDeterminant 1 k = 0 := by
  have hc : Continuous (fun k : ℝ => fourthDeterminant 1 k) := by
    unfold fourthDeterminant
    fun_prop
  have hz : (0 : ℝ) ∈ Icc (fourthDeterminant 1 (1/2)) (fourthDeterminant 1 0) := by
    norm_num [fourthDeterminant]
  obtain ⟨k,hk,he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1/2) hc.continuousOn hz
  have hk0 : k≠0 := by intro h; rw [h] at he; norm_num [fourthDeterminant] at he
  have hkh : k≠1/2 := by intro h; rw [h] at he; norm_num [fourthDeterminant] at he
  exact ⟨k,lt_of_le_of_ne hk.1 (Ne.symm hk0),lt_of_le_of_ne hk.2 hkh,he⟩

theorem nonvacuous_gap : ∃ k : ℝ, 0<k ∧ k<1/2 ∧
    (∃ μ, MixedCubicBoundaryQuartic.RepresentsEight μ 1 k) ∧
      ¬ ∃ μ, MixedCubicNinthRealization.RepresentsNine μ 1 k := by
  obtain ⟨k,hk0,hk1,h4⟩ := boundary_exists
  exact ⟨k,hk0,hk1,boundary_eight_but_not_nine 1 k (by norm_num) h4⟩

end OperatorDerivativeRewrite.Foundation.MixedCubicQuarticBoundary
