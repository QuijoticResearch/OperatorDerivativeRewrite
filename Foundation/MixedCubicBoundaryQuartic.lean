import Foundation.RegularMixedMomentExtension

/-! A sharp finite-degree gap: mixed cubic positivity at its boundary fails at degree four. -/
noncomputable section
open MeasureTheory Polynomial
namespace OperatorDerivativeRewrite.Foundation.MixedCubicBoundaryQuartic
open MixedCubicMomentPositivity MixedCubicThirdDegree
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem moments_seven_eight (v k : ℝ) :
    moment v k 7 = 105*v^2*k ∧ moment v k 8 = 105*v^4+280*v*k^2 := by
  norm_num [moment]
  constructor <;> ring

def nullCubic (v k : ℝ) : Polynomial ℝ :=
  centered v k 0 (6*v*k^2) (-6*v^2*k) (delta v k)

theorem nullCubic_expansion (v k : ℝ) :
    nullCubic v k = cubic (4*v^3*k+k^3) (-6*v^4+9*v*k^2) (-6*v^2*k) (delta v k) := by
  simp only [nullCubic,centered,cubic,Algebra.smul_def,map_add,map_sub,map_mul,
    map_pow,map_ofNat,map_neg,map_zero]
  unfold delta
  simp only [map_sub,map_mul,map_pow,map_ofNat]
  ring

theorem nullCubic_degree (v k : ℝ) : (nullCubic v k).natDegree ≤ 3 :=
  centered_natDegree _ _ _ _ _ _

theorem shifted_degree (v k : ℝ) : ((X : Polynomial ℝ)*nullCubic v k).natDegree ≤ 4 := by
  have hx : (X : Polynomial ℝ).natDegree ≤ 1 := by simp
  exact natDegree_mul_le.trans (by have := nullCubic_degree v k; omega)

theorem nullCubic_square (v k : ℝ) :
    expectation v k ((nullCubic v k)^2) = delta v k*determinant v k :=
  determinant_witness_value v k

theorem shifted_square_value (v k : ℝ) :
    expectation v k (((X : Polynomial ℝ)*nullCubic v k)^2) =
      168*v^10-420*v^7*k^2-30*v^4*k^4+99*v*k^6 := by
  let A := 4*v^3*k+k^3
  let B := -6*v^4+9*v*k^2
  let C := -6*v^2*k
  let D := delta v k
  have he : ((X : Polynomial ℝ)*nullCubic v k)^2 =
      A^2 • X^2+(2*A*B) • X^3+(B^2+2*A*C) • X^4+
      (2*A*D+2*B*C) • X^5+(C^2+2*B*D) • X^6+
      (2*C*D) • X^7+D^2 • X^8 := by
    rw [nullCubic_expansion]
    dsimp [A,B,C,D,cubic]
    simp only [Algebra.smul_def,map_add,map_mul,map_pow,map_ofNat]
    ring
  rw [he]
  simp only [map_add,map_smul,smul_eq_mul,expectation_X_pow]
  norm_num [moment]
  dsimp [A,B,C,D,delta]
  ring

theorem shifted_square_determinant_identity (v k : ℝ) :
    3*expectation v k (((X : Polynomial ℝ)*nullCubic v k)^2) =
      (98*v^4-33*v*k^2)*determinant v k+48*v^7*(31*k^2-14*v^3) := by
  rw [shifted_square_value]
  unfold determinant
  ring

theorem boundary_skew_bound (v k : ℝ) (hv : 0 < v) (hD : determinant v k = 0) :
    9*k^2 < 4*v^3 := by
  by_contra h
  have hk : 4*v^3 ≤ 9*k^2 := le_of_not_gt h
  have h1 := mul_nonneg (pow_nonneg hv.le 3) (sub_nonneg.mpr hk)
  have h2 := mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hk)
  unfold determinant at hD
  nlinarith [pow_pos hv 6]

theorem shifted_square_negative (v k : ℝ) (hv : 0 < v) (hD : determinant v k = 0) :
    expectation v k (((X : Polynomial ℝ)*nullCubic v k)^2) < 0 := by
  have hb := boundary_skew_bound v k hv hD
  have hn : 31*k^2-14*v^3 < 0 := by nlinarith [sq_nonneg k,pow_pos hv 3]
  have hi := shifted_square_determinant_identity v k
  rw [hD,mul_zero,zero_add] at hi
  have hp := mul_neg_of_pos_of_neg (mul_pos (by norm_num : (0 : ℝ) < 48) (pow_pos hv 7)) hn
  linarith

theorem boundary_cubic_positive (v k : ℝ) (hv : 0 < v) (hD : determinant v k = 0) :
    ∀ g : Polynomial ℝ, g.natDegree ≤ 3 → 0 ≤ expectation v k (g^2) :=
  (cubic_positivity_iff v k hv).mpr hD.ge

theorem boundary_not_quartic_positive (v k : ℝ) (hv : 0 < v) (hD : determinant v k = 0) :
    ¬ ∀ g : Polynomial ℝ, g.natDegree ≤ 4 → 0 ≤ expectation v k (g^2) := by
  intro h
  exact (not_le_of_gt (shifted_square_negative v k hv hD))
    (h (X*nullCubic v k) (shifted_degree v k))

theorem no_boundary_eight_moments (μ : Measure ℝ) (v k : ℝ) (hv : 0 < v)
    (hD : determinant v k = 0) (hi : ∀ n ≤ 8, Integrable (fun x : ℝ => x^n) μ) :
    ¬ ∀ n ≤ 8, (∫ x : ℝ, x^n ∂μ) = moment v k n := by
  intro hm
  let P := (X : Polynomial ℝ)*nullCubic v k
  have hP : P.natDegree ≤ 4 := shifted_degree v k
  have hP2 : (P^2).natDegree ≤ 8 := natDegree_pow_le.trans (by omega)
  have hmatch : ∀ n ≤ 8, (∫ x : ℝ, x^n ∂μ) = expectation v k (X^n) := by
    intro n hn
    rw [expectation_X_pow]
    exact hm n hn
  have he := (TruncatedPolynomialIntegration.polynomial_integral_match μ
    (expectation v k) 8 hi hmatch (P^2) hP2).2
  have hn : 0 ≤ expectation v k (P^2) := by
    rw [← he]
    apply integral_nonneg
    intro x
    simpa only [eval_pow,Pi.zero_apply] using sq_nonneg (P.eval x)
  exact (not_le_of_gt (shifted_square_negative v k hv hD)) hn

def RepresentsEight (μ : Measure ℝ) (v k : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ n ≤ 8, Integrable (fun x : ℝ => x^n) μ) ∧
    ∀ n ≤ 8, (∫ x : ℝ, x^n ∂μ) = moment v k n

theorem boundary_realizability_gap (v k : ℝ) (hv : 0 < v) (hD : determinant v k = 0) :
    (∃ μ, RegularMixedMomentExtension.RepresentsSix μ v k) ∧
      ¬ ∃ μ, RepresentsEight μ v k := by
  refine ⟨(RegularMixedMomentExtension.mixed_six_realizable_iff v k).mpr ⟨hv.le,hD.ge⟩, ?_⟩
  rintro ⟨μ,hprob,hi,hm⟩
  exact no_boundary_eight_moments μ v k hv hD hi hm

def boundarySkew : ℝ := Real.sqrt ((2*Real.sqrt 7-4)/3)

theorem boundarySkew_square : boundarySkew^2 = (2*Real.sqrt 7-4)/3 := by
  apply Real.sq_sqrt
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  have hp := Real.sqrt_nonneg (7 : ℝ)
  have hn : 0 ≤ 2*Real.sqrt 7-4 := by nlinarith
  exact div_nonneg hn (by norm_num)

theorem boundarySkew_determinant : determinant 1 boundarySkew = 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  have hk4 : boundarySkew^4 = (boundarySkew^2)^2 := by ring
  unfold determinant
  rw [hk4,boundarySkew_square]
  norm_num
  nlinarith

theorem concrete_realizability_gap :
    (∃ μ, RegularMixedMomentExtension.RepresentsSix μ 1 boundarySkew) ∧
      ¬ ∃ μ, RepresentsEight μ 1 boundarySkew :=
  boundary_realizability_gap 1 boundarySkew (by norm_num) boundarySkew_determinant

theorem null_cross_value (v k : ℝ) :
    expectation v k ((X : Polynomial ℝ)*(nullCubic v k)^2) =
      72*v^8*k-72*v^5*k^3+126*v^2*k^5 := by
  let A := 4*v^3*k+k^3
  let B := -6*v^4+9*v*k^2
  let C := -6*v^2*k
  let D := delta v k
  have he : (X : Polynomial ℝ)*(nullCubic v k)^2 =
      A^2 • X^1+(2*A*B) • X^2+(B^2+2*A*C) • X^3+
      (2*A*D+2*B*C) • X^4+(C^2+2*B*D) • X^5+
      (2*C*D) • X^6+D^2 • X^7 := by
    rw [nullCubic_expansion]
    dsimp [A,B,C,D,cubic]
    simp only [Algebra.smul_def,map_add,map_mul,map_pow,map_ofNat,map_neg,map_sub]
    ring
  rw [he]
  simp only [map_add,map_smul,smul_eq_mul,expectation_X_pow]
  norm_num [moment]
  dsimp [A,B,C,D,delta]
  ring

theorem null_cross_determinant_identity (v k : ℝ) :
    expectation v k ((X : Polynomial ℝ)*(nullCubic v k)^2) =
      -14*v^2*k*determinant v k+24*v^5*k*(10*v^3-17*k^2) := by
  rw [null_cross_value]
  unfold determinant
  ring

theorem boundary_skew_ne_zero (v k : ℝ) (hv : 0 < v) (hD : determinant v k = 0) :
    k ≠ 0 := by
  intro hk
  unfold determinant at hD
  rw [hk] at hD
  norm_num at hD
  nlinarith [pow_pos hv 6]

theorem null_cross_ne_zero (v k : ℝ) (hv : 0 < v) (hD : determinant v k = 0) :
    expectation v k ((X : Polynomial ℝ)*(nullCubic v k)^2) ≠ 0 := by
  have hb := boundary_skew_bound v k hv hD
  have hn : 0 < 10*v^3-17*k^2 := by nlinarith [pow_pos hv 3,sq_nonneg k]
  rw [null_cross_determinant_identity,hD,mul_zero,zero_add]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hv.ne'))
    (boundary_skew_ne_zero v k hv hD)) hn.ne'

theorem no_boundary_seven_moments (μ : Measure ℝ) (v k : ℝ) (hv : 0 < v)
    (hD : determinant v k = 0) (hi : ∀ n ≤ 7, Integrable (fun x : ℝ => x^n) μ) :
    ¬ ∀ n ≤ 7, (∫ x : ℝ, x^n ∂μ) = moment v k n := by
  intro hm
  let P := nullCubic v k
  have hp : P.natDegree ≤ 3 := nullCubic_degree v k
  have hp2 : (P^2).natDegree ≤ 6 := natDegree_pow_le.trans (by omega)
  have hcross : ((X : Polynomial ℝ)*P^2).natDegree ≤ 7 :=
    natDegree_mul_le.trans (by simp only [natDegree_X]; omega)
  have hmatch : ∀ n ≤ 7, (∫ x : ℝ, x^n ∂μ) = expectation v k (X^n) := by
    intro n hn
    rw [expectation_X_pow]
    exact hm n hn
  obtain ⟨hiP,heP⟩ := TruncatedPolynomialIntegration.polynomial_integral_match μ
    (expectation v k) 7 hi hmatch (P^2) (hp2.trans (by omega))
  have hzero : expectation v k (P^2) = 0 := by
    rw [show P = nullCubic v k from rfl,nullCubic_square,hD,mul_zero]
  rw [hzero] at heP
  have hae := (integral_eq_zero_iff_of_nonneg
    (show 0 ≤ fun x => (P^2).eval x from fun x => by
      simpa only [eval_pow,Pi.zero_apply] using sq_nonneg (P.eval x)) hiP).mp heP
  have hz : (fun x => ((X : Polynomial ℝ)*P^2).eval x) =ᵐ[μ] 0 := by
    filter_upwards [hae] with x hx
    simp only [eval_mul,eval_X,hx,mul_zero,Pi.zero_apply]
  have he := (TruncatedPolynomialIntegration.polynomial_integral_match μ
    (expectation v k) 7 hi hmatch (X*P^2) hcross).2
  have hc0 : expectation v k (X*P^2) = 0 := by
    rw [← he,integral_congr_ae hz]
    simp
  exact null_cross_ne_zero v k hv hD hc0

def RepresentsSeven (μ : Measure ℝ) (v k : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ n ≤ 7, Integrable (fun x : ℝ => x^n) μ) ∧
    ∀ n ≤ 7, (∫ x : ℝ, x^n ∂μ) = moment v k n

theorem boundary_seven_gap (v k : ℝ) (hv : 0 < v) (hD : determinant v k = 0) :
    (∃ μ, RegularMixedMomentExtension.RepresentsSix μ v k) ∧
      ¬ ∃ μ, RepresentsSeven μ v k := by
  refine ⟨(boundary_realizability_gap v k hv hD).1, ?_⟩
  rintro ⟨μ,hprob,hi,hm⟩
  exact no_boundary_seven_moments μ v k hv hD hi hm

theorem concrete_seven_gap :
    (∃ μ, RegularMixedMomentExtension.RepresentsSix μ 1 boundarySkew) ∧
      ¬ ∃ μ, RepresentsSeven μ 1 boundarySkew :=
  boundary_seven_gap 1 boundarySkew (by norm_num) boundarySkew_determinant

end OperatorDerivativeRewrite.Foundation.MixedCubicBoundaryQuartic
