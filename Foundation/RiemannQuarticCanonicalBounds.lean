import Foundation.RiemannQuarticCanonicalDerivative
import Mathlib.Analysis.Complex.AbsMax

/-! Actual bounds for the finite-disk zero-free remainder, obtained from
boundary values and the normalization at zero rather than an uncontrolled
division of entire functions. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalBounds
open RiemannQuarticFlow RiemannQuarticReality RiemannQuarticZeroCounting
open RiemannQuarticCanonicalDerivative

theorem canonical_norm_at_origin (R : ℝ) (hR : 0 < R) (a : ℂ) (ha : a ≠ 0) :
    ‖canonicalFactor R a 0‖ = R/‖a‖ := by
  rw [canonicalFactor_apply]
  simp only [mul_zero,sub_zero,zero_sub,norm_div,norm_pow,norm_mul,norm_neg,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  field_simp

theorem canonical_product_boundary_norm (t R : ℝ) (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
    ‖∏ᶠ a : ℂ, canonicalFactor R a z ^ (divisor (flow t) (ball 0 R) a)‖ = 1 := by
  classical
  let d := divisor (flow t) (ball (0 : ℂ) R)
  have hs : (Function.support d).Finite :=
    ((flow_analytic t).mono (subset_univ (closedBall (0 : ℂ) R))).meromorphicOn.divisor_ball_support_finite
  have hsup : Function.mulSupport (fun a => canonicalFactor R a z ^ d a) ⊆ Function.support d := by
    intro a ha
    by_contra h
    have he : d a = 0 := by simpa only [Function.mem_support,not_not] using h
    simp only [Function.mem_mulSupport,he,zpow_zero,ne_eq,not_true_eq_false] at ha
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hsup hs,norm_prod]
  apply Finset.prod_eq_one
  intro a ha
  have hd : d a ≠ 0 := by simpa only [Set.Finite.mem_toFinset,Function.mem_support] using ha
  rw [norm_zpow,norm_canonicalFactor_eval_circle_eq_one (d.supportWithinDomain hd) hz,one_zpow]

theorem canonical_product_origin_norm_ge_one (t R : ℝ) (hR : 0 < R) :
    1 ≤ ‖∏ᶠ a : ℂ, canonicalFactor R a 0 ^ (divisor (flow t) (ball 0 R) a)‖ := by
  classical
  let d := divisor (flow t) (ball (0 : ℂ) R)
  have hs : (Function.support d).Finite :=
    ((flow_analytic t).mono (subset_univ (closedBall (0 : ℂ) R))).meromorphicOn.divisor_ball_support_finite
  have hsup : Function.mulSupport (fun a => canonicalFactor R a 0 ^ d a) ⊆ Function.support d := by
    intro a ha
    by_contra h
    have he : d a = 0 := by simpa only [Function.mem_support,not_not] using h
    simp only [Function.mem_mulSupport,he,zpow_zero,ne_eq,not_true_eq_false] at ha
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hsup hs,norm_prod]
  apply Finset.one_le_prod₀
  intro a ha
  have hd : d a ≠ 0 := by simpa only [Set.Finite.mem_toFinset,Function.mem_support] using ha
  have ha0 : a ≠ 0 := by
    intro he
    subst a
    exact hd (ball_divisor_zero_at_origin t R)
  have hnorm : ‖a‖ < R := mem_ball_zero_iff.mp (d.supportWithinDomain hd)
  rw [norm_zpow,canonical_norm_at_origin R hR a ha0]
  exact one_le_zpow₀ ((le_div_iff₀ (norm_pos_iff.mpr ha0)).mpr (by linarith))
    (((flow_analytic t).mono (subset_univ (ball (0 : ℂ) R))).divisor_nonneg a)

theorem remainder_boundary_norm (t R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp (flow t) h R)
    (hne : ∀ z ∈ sphere (0 : ℂ) R, flow t z ≠ 0) :
    ∀ z ∈ sphere (0 : ℂ) R, ‖h z‖ = ‖flow t z‖ := by
  intro z hz
  rw [canonical_remainder_eq_at_ne_zero t R hR h D
    (RiemannQuarticDiskDecomposition.boundary_divisor_eq_zero t R hne)
    z (sphere_subset_closedBall hz) (hne z hz),norm_mul,canonical_product_boundary_norm t R z hz,one_mul]

theorem remainder_origin_norm_lower (t R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) : ‖flow t 0‖ ≤ ‖h 0‖ := by
  have hn : flow t 0 ≠ 0 := by simpa using flow_ne_zero_on_imaginary_axis t 0
  rw [canonical_remainder_eq_at_ne_zero t R hR h D hboundary 0 (mem_closedBall_self hR.le) hn,
    norm_mul]
  nlinarith [canonical_product_origin_norm_ge_one t R hR,norm_nonneg (flow t 0)]

theorem remainder_norm_bound (t : ℝ) (C : ℝ)
    (hgrowth : ∀ z : ℂ, ‖flow t z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖))
    (R : ℝ) (hR : 0 < R) (h : ℂ → ℂ) (D : ECanonicalDecomp (flow t) h R)
    (hne : ∀ z ∈ sphere (0 : ℂ) R, flow t z ≠ 0) :
    ∀ z ∈ closedBall (0 : ℂ) R, ‖h z‖ ≤ C*Real.exp (R*Real.sqrt R) := by
  have hd : DiffContOnCl ℂ h (ball (0 : ℂ) R) :=
    D.analyticOnNhd.differentiableOn.diffContOnCl_ball subset_rfl
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_
    (by simpa only [closure_ball (0 : ℂ) (ne_of_gt hR)] using hz)
  intro w hw
  have hs : w ∈ sphere (0 : ℂ) R := by
    simpa only [frontier_ball (0 : ℂ) (ne_of_gt hR)] using hw
  rw [remainder_boundary_norm t R hR h D hne w hs]
  have hn : ‖w‖ = R := mem_sphere_zero_iff_norm.mp hs
  simpa only [hn] using hgrowth w

theorem sphere_zero_free_of_boundary_divisor_zero (t R : ℝ)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) :
    ∀ z ∈ sphere (0 : ℂ) R, flow t z ≠ 0 := by
  have he := ((flow_analytic t).mono (subset_univ (sphere (0 : ℂ) R))).meromorphicNFOn
    |>.zero_set_eq_divisor_support (fun z => flow_zero_order_finite t z)
  intro z hz hzero
  have hm : z ∈ sphere (0 : ℂ) R ∩ (flow t) ⁻¹' {0} := ⟨hz,hzero⟩
  rw [he] at hm
  simp only [Function.mem_support,hboundary,Function.locallyFinsuppWithin.coe_zero,
    Pi.zero_apply,ne_eq,not_true_eq_false] at hm

theorem exists_normalized_remainder_real_part_bound (t : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 1 ≤ R → ∀ r : ℝ, 2*R < r → r < 2*R+1 →
      ∀ h g : ℂ → ℂ, ECanonicalDecomp (flow t) h r →
        divisor (flow t) (sphere 0 r) = 0 →
        (∀ z ∈ ball (0 : ℂ) r, Complex.exp (g z) = h z/h 0) →
        ∀ z ∈ ball (0 : ℂ) (2*R), (g z).re ≤ A+6*(R*Real.sqrt R) := by
  obtain ⟨C,hC,hgrowth⟩ := RiemannQuarticEntireGrowth.exists_subquadratic_growth t
  have hp : 0 < ‖flow t 0‖ := norm_pos_iff.mpr (by
    simpa using flow_ne_zero_on_imaginary_axis t 0)
  have hCp : 0 < C/‖flow t 0‖ := div_pos hC hp
  refine ⟨|Real.log (C/‖flow t 0‖)|+1,by positivity,?_⟩
  intro R hR r hr hr1 h g D hboundary he z hz
  have hRp : 0 < R := by linarith
  have hrp : 0 < r := by linarith
  have hzr : z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr
    ((mem_ball_zero_iff.mp hz).trans hr)
  have hlower := remainder_origin_norm_lower t r hrp h D hboundary
  have hhz : 0 < ‖h 0‖ := lt_of_lt_of_le hp hlower
  have hb := remainder_norm_bound t C hgrowth r hrp h D
    (sphere_zero_free_of_boundary_divisor_zero t r hboundary) z (ball_subset_closedBall hzr)
  have hnorm : ‖h z‖/‖h 0‖ ≤ (C/‖flow t 0‖)*Real.exp (r*Real.sqrt r) := by
    apply (div_le_iff₀ hhz).mpr
    calc
      _ ≤ C*Real.exp (r*Real.sqrt r) := hb
      _ = ((C/‖flow t 0‖)*Real.exp (r*Real.sqrt r))*‖flow t 0‖ := by field_simp
      _ ≤ ((C/‖flow t 0‖)*Real.exp (r*Real.sqrt r))*‖h 0‖ :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
  have hgRe : (g z).re ≤ Real.log (C/‖flow t 0‖)+r*Real.sqrt r := by
    apply Real.exp_le_exp.mp
    have hex := congrArg norm (he z hzr)
    rw [Complex.norm_exp,norm_div] at hex
    rw [hex,Real.exp_add,Real.exp_log hCp]
    exact hnorm
  have hr3 : r ≤ 3*R := by linarith
  have hsq : Real.sqrt r ≤ 2*Real.sqrt R := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hRp.le]
  have hscale : r*Real.sqrt r ≤ 6*(R*Real.sqrt R) := by
    have hm := mul_le_mul hr3 hsq (Real.sqrt_nonneg r) (by positivity : 0 ≤ 3*R)
    nlinarith
  linarith [le_abs_self (Real.log (C/‖flow t 0‖))]

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalBounds
