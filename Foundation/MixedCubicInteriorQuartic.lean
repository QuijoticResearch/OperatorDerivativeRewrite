import Foundation.MixedCubicBoundaryQuartic

/-! An open parameter region with strict cubic positivity and failed quartic positivity. -/
noncomputable section
open MeasureTheory Polynomial Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.MixedCubicInteriorQuartic
open MixedCubicMomentPositivity MixedCubicThirdDegree MixedCubicBoundaryQuartic
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem centered_zero_iff (v k : ℝ) (hv : 0 < v) (hD : 0 < determinant v k)
    (c b a d : ℝ) :
    expectation v k ((centered v k c b a d)^2) = 0 ↔ c=0 ∧ b=0 ∧ a=0 ∧ d=0 := by
  constructor
  · intro he
    have hd := determinant_nonneg_delta_pos v k hv hD.le
    have h1 := mul_nonneg (mul_pos hv hd).le (sq_nonneg c)
    have h2 := mul_nonneg hd.le (sq_nonneg (v*b+k*a))
    have h3 := sq_nonneg (delta v k*a+6*v^2*k*d)
    have h4 := mul_nonneg (mul_pos hv hD).le (sq_nonneg d)
    have hsum := weighted_square_decomposition v k c b a d
    rw [he,mul_zero] at hsum
    have hcTerm : v*delta v k*c^2 = 0 := by nlinarith only [hsum,h1,h2,h3,h4]
    have hdTerm : v*determinant v k*d^2 = 0 := by nlinarith only [hsum,h1,h2,h3,h4]
    have haTerm : (delta v k*a+6*v^2*k*d)^2 = 0 := by nlinarith only [hsum,h1,h2,h3,h4]
    have hbTerm : delta v k*(v*b+k*a)^2 = 0 := by nlinarith only [hsum,h1,h2,h3,h4]
    have hc : c=0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hcTerm).resolve_left (mul_pos hv hd).ne')
    have hdz : d=0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hdTerm).resolve_left (mul_pos hv hD).ne')
    have haz : a=0 := by
      have h := sq_eq_zero_iff.mp haTerm
      rw [hdz] at h
      simp only [mul_zero,add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hd.ne'
    have hbz : b=0 := by
      have h := sq_eq_zero_iff.mp ((mul_eq_zero.mp hbTerm).resolve_left hd.ne')
      rw [haz] at h
      simp only [mul_zero,add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hv.ne'
    exact ⟨hc,hbz,haz,hdz⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    simp [centered,cubic]

theorem strict_cubic_positive (v k : ℝ) (hv : 0 < v) (hD : 0 < determinant v k)
    (g : Polynomial ℝ) (hg : g.natDegree ≤ 3) (hgn : g ≠ 0) :
    0 < expectation v k (g^2) := by
  have hnonneg := (cubic_positivity_iff v k hv).mpr hD.le g hg
  have hne : expectation v k (g^2) ≠ 0 := by
    intro he
    rw [cubic_of_natDegree g hg,cubic_as_centered] at he
    obtain ⟨hc,hb,ha,hd⟩ := (centered_zero_iff v k hv hD _ _ _ _).mp he
    have hc0 : g.coeff 0 = 0 := by simpa [ha,hd] using hc
    have hb0 : g.coeff 1 = 0 := by simpa [hd] using hb
    apply hgn
    rw [cubic_of_natDegree g hg]
    simp [cubic,hc0,hb0,ha,hd]
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

def quarticValue (v k : ℝ) : ℝ :=
  168*v^10-420*v^7*k^2-30*v^4*k^4+99*v*k^6

theorem quarticValue_eq (v k : ℝ) :
    quarticValue v k = expectation v k (((X : Polynomial ℝ)*nullCubic v k)^2) :=
  (shifted_square_value v k).symm

theorem rational_determinant : determinant 1 (13/20) = 40551/160000 := by
  norm_num [determinant]

theorem rational_quarticValue : quarticValue 1 (13/20) = -469677909/64000000 := by
  norm_num [quarticValue]

def failureRegion : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < determinant p.1 p.2 ∧ quarticValue p.1 p.2 < 0}

theorem failureRegion_isOpen : IsOpen failureRegion := by
  have hD : Continuous (fun p : ℝ × ℝ => determinant p.1 p.2) := by
    unfold determinant
    fun_prop
  have hQ : Continuous (fun p : ℝ × ℝ => quarticValue p.1 p.2) := by
    unfold quarticValue
    fun_prop
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const hD).inter (isOpen_lt hQ continuous_const))

theorem rational_mem_failureRegion : ((1,13/20) : ℝ × ℝ) ∈ failureRegion := by
  change 0 < (1 : ℝ) ∧ 0 < determinant 1 (13/20) ∧ quarticValue 1 (13/20) < 0
  rw [rational_determinant,rational_quarticValue]
  norm_num

theorem failureRegion_neighborhood : failureRegion ∈ 𝓝 ((1,13/20) : ℝ × ℝ) :=
  failureRegion_isOpen.mem_nhds rational_mem_failureRegion

theorem region_strict_cubic (p : ℝ × ℝ) (hp : p ∈ failureRegion) :
    ∀ g : Polynomial ℝ, g.natDegree ≤ 3 → g ≠ 0 → 0 < expectation p.1 p.2 (g^2) :=
  strict_cubic_positive p.1 p.2 hp.1 hp.2.1

theorem region_negative_quartic (p : ℝ × ℝ) (hp : p ∈ failureRegion) :
    ∃ g : Polynomial ℝ, g.natDegree ≤ 4 ∧ expectation p.1 p.2 (g^2) < 0 := by
  refine ⟨X*nullCubic p.1 p.2,shifted_degree _ _,?_⟩
  rw [← quarticValue_eq]
  exact hp.2.2

theorem region_six_realizable (p : ℝ × ℝ) (hp : p ∈ failureRegion) :
    ∃ μ, RegularMixedMomentExtension.RepresentsSix μ p.1 p.2 :=
  (RegularMixedMomentExtension.mixed_six_realizable_iff _ _).mpr ⟨hp.1.le,hp.2.1.le⟩

theorem negative_quartic_no_eight (μ : Measure ℝ) (v k : ℝ)
    (hneg : quarticValue v k < 0) (hi : ∀ n ≤ 8, Integrable (fun x : ℝ => x^n) μ) :
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
  exact (not_le_of_gt hneg) (by simpa only [quarticValue_eq] using hn)

theorem region_not_eight (p : ℝ × ℝ) (hp : p ∈ failureRegion) :
    ¬ ∃ μ, RepresentsEight μ p.1 p.2 := by
  rintro ⟨μ,hprob,hi,hm⟩
  exact negative_quartic_no_eight μ p.1 p.2 hp.2.2 hi hm

theorem rational_strict_cubic : ∀ g : Polynomial ℝ, g.natDegree ≤ 3 → g ≠ 0 →
    0 < expectation 1 (13/20) (g^2) :=
  region_strict_cubic _ rational_mem_failureRegion

theorem rational_realizability_gap :
    (∃ μ, RegularMixedMomentExtension.RepresentsSix μ 1 (13/20)) ∧
      ¬ ∃ μ, RepresentsEight μ 1 (13/20) :=
  ⟨region_six_realizable _ rational_mem_failureRegion,
    region_not_eight _ rational_mem_failureRegion⟩

end OperatorDerivativeRewrite.Foundation.MixedCubicInteriorQuartic
