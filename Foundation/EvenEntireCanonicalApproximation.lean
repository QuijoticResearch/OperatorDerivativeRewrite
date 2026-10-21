import Foundation.EvenEntireCanonicalDerivative
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Field.Lemmas

/-! Canonical remainder bounds for actual entire functions nonzero at the origin.
Boundary and origin bounds are proved before normalized logarithm growth. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.EvenEntireCanonicalApproximation
open EvenEntireCanonicalDerivative
variable (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f univ) (h0 : f 0 ≠ 0)
include ha h0

omit ha h0 in
theorem canonical_norm_at_origin (R : ℝ) (hR : 0 < R) (a : ℂ) (ha : a ≠ 0) :
    ‖canonicalFactor R a 0‖ = R/‖a‖ := by
  rw [canonicalFactor_apply]
  simp only [mul_zero,sub_zero,zero_sub,norm_div,norm_pow,norm_mul,norm_neg,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  field_simp

omit h0 in
theorem canonical_product_boundary_norm (R : ℝ) (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
    ‖∏ᶠ a : ℂ, canonicalFactor R a z ^ (divisor f (ball 0 R) a)‖ = 1 := by
  classical
  have hf := ha
  let d := divisor f (ball (0 : ℂ) R)
  have hs : (Function.support d).Finite :=
    ((ha).mono (subset_univ (closedBall (0 : ℂ) R))).meromorphicOn.divisor_ball_support_finite
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

theorem canonical_product_origin_norm_ge_one (R : ℝ) (hR : 0 < R) :
    1 ≤ ‖∏ᶠ a : ℂ, canonicalFactor R a 0 ^ (divisor f (ball 0 R) a)‖ := by
  classical
  have hf := ha
  let d := divisor f (ball (0 : ℂ) R)
  have hs : (Function.support d).Finite :=
    ((ha).mono (subset_univ (closedBall (0 : ℂ) R))).meromorphicOn.divisor_ball_support_finite
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
    exact hd (ball_divisor_zero_at_origin f hf h0 R)
  have hnorm : ‖a‖ < R := mem_ball_zero_iff.mp (d.supportWithinDomain hd)
  rw [norm_zpow,canonical_norm_at_origin R hR a ha0]
  exact one_le_zpow₀ ((le_div_iff₀ (norm_pos_iff.mpr ha0)).mpr (by linarith))
    (((hf).mono (subset_univ (ball (0 : ℂ) R))).divisor_nonneg a)

omit h0 in
theorem remainder_boundary_norm (R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp f h R)
    (hne : ∀ z ∈ sphere (0 : ℂ) R, f z ≠ 0) :
    ∀ z ∈ sphere (0 : ℂ) R, ‖h z‖ = ‖f z‖ := by
  intro z hz
  rw [canonical_remainder_eq_at_ne_zero f ha R hR h D
    (EntireDiskDecomposition.boundary_divisor_eq_zero f ha R hne)
    z (sphere_subset_closedBall hz) (hne z hz),norm_mul,canonical_product_boundary_norm f ha R z hz,one_mul]

theorem remainder_origin_norm_lower (R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp f h R)
    (hboundary : divisor f (sphere 0 R) = 0) : ‖f 0‖ ≤ ‖h 0‖ := by
  have hn : f 0 ≠ 0 := h0
  rw [canonical_remainder_eq_at_ne_zero f ha R hR h D hboundary 0 (mem_closedBall_self hR.le) hn,
    norm_mul]
  nlinarith [canonical_product_origin_norm_ge_one f ha h0 R hR,norm_nonneg (f 0)]

omit h0 in
theorem remainder_norm_bound (C : ℝ)
    (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖))
    (R : ℝ) (hR : 0 < R) (h : ℂ → ℂ) (D : ECanonicalDecomp f h R)
    (hne : ∀ z ∈ sphere (0 : ℂ) R, f z ≠ 0) :
    ∀ z ∈ closedBall (0 : ℂ) R, ‖h z‖ ≤ C*Real.exp (R*Real.sqrt R) := by
  have hd : DiffContOnCl ℂ h (ball (0 : ℂ) R) :=
    D.analyticOnNhd.differentiableOn.diffContOnCl_ball subset_rfl
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_
    (by simpa only [closure_ball (0 : ℂ) (ne_of_gt hR)] using hz)
  intro w hw
  have hs : w ∈ sphere (0 : ℂ) R := by
    simpa only [frontier_ball (0 : ℂ) (ne_of_gt hR)] using hw
  rw [remainder_boundary_norm f ha R hR h D hne w hs]
  have hn : ‖w‖ = R := mem_sphere_zero_iff_norm.mp hs
  simpa only [hn] using hgrowth w

theorem sphere_zero_free_of_boundary_divisor_zero (R : ℝ)
    (hboundary : divisor f (sphere 0 R) = 0) :
    ∀ z ∈ sphere (0 : ℂ) R, f z ≠ 0 := by
  have he := ((ha).mono (subset_univ (sphere (0 : ℂ) R))).meromorphicNFOn
    |>.zero_set_eq_divisor_support (fun z => EntireSubquadraticZeroCounting.zero_order_finite f ha h0 z)
  intro z hz hzero
  have hm : z ∈ sphere (0 : ℂ) R ∩ f ⁻¹' {0} := ⟨hz,hzero⟩
  rw [he] at hm
  simp only [Function.mem_support,hboundary,Function.locallyFinsuppWithin.coe_zero,
    Pi.zero_apply,ne_eq,not_true_eq_false] at hm

theorem exists_normalized_remainder_real_part_bound
    (hgrowth : ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, ‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 1 ≤ R → ∀ r : ℝ, 2*R < r → r < 2*R+1 →
      ∀ h g : ℂ → ℂ, ECanonicalDecomp f h r →
        divisor f (sphere 0 r) = 0 →
        (∀ z ∈ ball (0 : ℂ) r, Complex.exp (g z) = h z/h 0) →
        ∀ z ∈ ball (0 : ℂ) (2*R), (g z).re ≤ A+6*(R*Real.sqrt R) := by
  obtain ⟨C,hC,hgrowth⟩ := hgrowth
  have hp : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hCp : 0 < C/‖f 0‖ := div_pos hC hp
  refine ⟨|Real.log (C/‖f 0‖)|+1,by positivity,?_⟩
  intro R hR r hr hr1 h g D hboundary he z hz
  have hRp : 0 < R := by linarith
  have hrp : 0 < r := by linarith
  have hzr : z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr
    ((mem_ball_zero_iff.mp hz).trans hr)
  have hlower := remainder_origin_norm_lower f ha h0 r hrp h D hboundary
  have hhz : 0 < ‖h 0‖ := lt_of_lt_of_le hp hlower
  have hb := remainder_norm_bound f ha C hgrowth r hrp h D
    (sphere_zero_free_of_boundary_divisor_zero f ha h0 r hboundary) z (ball_subset_closedBall hzr)
  have hnorm : ‖h z‖/‖h 0‖ ≤ (C/‖f 0‖)*Real.exp (r*Real.sqrt r) := by
    apply (div_le_iff₀ hhz).mpr
    calc
      _ ≤ C*Real.exp (r*Real.sqrt r) := hb
      _ = ((C/‖f 0‖)*Real.exp (r*Real.sqrt r))*‖f 0‖ := by field_simp
      _ ≤ ((C/‖f 0‖)*Real.exp (r*Real.sqrt r))*‖h 0‖ :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
  have hgRe : (g z).re ≤ Real.log (C/‖f 0‖)+r*Real.sqrt r := by
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
  linarith [le_abs_self (Real.log (C/‖f 0‖))]

end OperatorDerivativeRewrite.Foundation.EvenEntireCanonicalApproximation

noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.EvenEntireCanonicalApproximation
variable (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f univ) (h0 : f 0 ≠ 0)
  (heven : ∀ z : ℂ, f (-z)=f z)
include ha h0 heven

theorem exists_locally_uniform_remainders
    (hgrowth : ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, ‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ r : ℝ → ℝ, ∃ h g : ℝ → ℂ → ℂ,
      (∀ R : ℝ, 1 ≤ R → 2*R < r R ∧ r R < 2*R+1 ∧
        divisor f (sphere 0 (r R)) = 0 ∧
        ECanonicalDecomp f (h R) (r R) ∧
        DifferentiableOn ℂ (g R) (ball 0 (r R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
        (∀ z ∈ ball (0 : ℂ) (r R), HasDerivAt (g R) (deriv (h R) z / h R z) z) ∧
        (∀ z ∈ ball (0 : ℂ) (r R), Complex.exp (g R z) = h R z / h R 0) ∧
        ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+6*(R*Real.sqrt R)) ∧
      TendstoLocallyUniformly g (fun _ => 0) atTop ∧
      TendstoLocallyUniformly (fun R z => Complex.exp (g R z)) (fun _ => 1) atTop ∧
      TendstoLocallyUniformly (fun R z => h R z / h R 0) (fun _ => 1) atTop := by
  classical
  obtain ⟨A,hA,hreal⟩ := exists_normalized_remainder_real_part_bound f ha h0 hgrowth
  have hex (R : ℝ) := EvenEntireCanonicalDerivative.exists_zero_derivative_log_remainder f ha h0 heven (2*max R 1)
    (by positivity : 0 ≤ 2*max R 1)
  choose r hr hr1 hboundary h g D hg h0 hd0 hd he using hex
  have hspec (R : ℝ) (hR : 1 ≤ R) : 2*R < r R ∧ r R < 2*R+1 ∧
      divisor f (sphere 0 (r R)) = 0 ∧
      ECanonicalDecomp f (h R) (r R) ∧
      DifferentiableOn ℂ (g R) (ball 0 (r R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) (r R), HasDerivAt (g R) (deriv (h R) z / h R z) z) ∧
      (∀ z ∈ ball (0 : ℂ) (r R), Complex.exp (g R z) = h R z / h R 0) ∧
      ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+6*(R*Real.sqrt R) := by
    have hrl : 2*R < r R := by simpa only [max_eq_left hR] using hr R
    have hru : r R < 2*R+1 := by simpa only [max_eq_left hR] using hr1 R
    exact ⟨hrl,hru,hboundary R,D R,hg R,h0 R,hd0 R,hd R,he R,
      hreal R hR (r R) hrl hru (h R) (g R) (D R) (hboundary R) (he R)⟩
  have hdata : ∀ᶠ R : ℝ in atTop,
      DifferentiableOn ℂ (g R) (ball 0 (2*R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
        ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+6*(R*Real.sqrt R) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    obtain ⟨hrl,hru,hbd,hD,hgR,hg0,hgd,hder,hexp,hre⟩ := hspec R hR
    exact ⟨hgR.mono (ball_subset_ball hrl.le),hg0,hgd,hre⟩
  have hlog := EvenDiskLogLimit.locally_uniform_zero g A 6 hA (by norm_num) hdata
  have hexp := EvenDiskLogLimit.locally_uniform_exp_one g A 6 hA (by norm_num) hdata
  have hquot : TendstoLocallyUniformly (fun R z => h R z / h R 0) (fun _ => 1) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨ρ,hρ,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    apply (tendstoLocallyUniformly_iff_forall_isCompact.mp hexp K hK).congr
    filter_upwards [eventually_ge_atTop (max 1 (ρ+1))] with R hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    have hrl : 2*R < r R := (hspec R hR1).1
    intro z hz
    apply he R z
    apply mem_ball_zero_iff.mpr
    have hzρ : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.mp (hsub hz)
    linarith [(le_max_right 1 (ρ+1)).trans hR]
  exact ⟨A,hA,r,h,g,hspec,hlog,hexp,hquot⟩

end OperatorDerivativeRewrite.Foundation.EvenEntireCanonicalApproximation

noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.EvenEntireCanonicalApproximation
variable (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f univ) (h0 : f 0 ≠ 0)
include ha h0

def inverseZeroProduct (R : ℝ) : ℂ → ℂ :=
  ∏ᶠ a : ℂ, (canonicalFactor R a) ^ (-divisor f (ball 0 R) a)

omit ha h0 in
theorem canonical_reciprocal_eq (R : ℝ) (a z : ℂ) :
    (canonicalFactor R a z)⁻¹ = (R : ℂ)*(z-a)/((R : ℂ)^2-conj a*z) := by
  rw [canonicalFactor_apply,inv_div]

omit ha h0 in
theorem canonical_numerator_ne_zero (R : ℝ) (a z : ℂ)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ closedBall (0 : ℂ) R) :
    (R : ℂ)^2-conj a*z ≠ 0 := by
  have har : ‖a‖ < R := mem_ball_zero_iff.mp ha
  have hzr : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg a) har
  have hn : ‖conj a*z‖ < ‖(R : ℂ)^2‖ := by
    calc
      _ = ‖a‖*‖z‖ := by rw [norm_mul,norm_conj]
      _ ≤ ‖a‖*R := mul_le_mul_of_nonneg_left hzr (norm_nonneg a)
      _ < R*R := mul_lt_mul_of_pos_right har hR
      _ = _ := by simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,pow_two]
  exact sub_ne_zero.mpr fun he => (ne_of_lt hn) (congrArg norm he.symm)

omit ha h0 in
theorem canonical_reciprocal_analytic (R : ℝ) (a : ℂ) (ha : a ∈ ball (0 : ℂ) R) :
    AnalyticOnNhd ℂ (fun z => (canonicalFactor R a z)⁻¹) (closedBall 0 R) := by
  have he : (fun z => (canonicalFactor R a z)⁻¹) =
      fun z => (R : ℂ)*(z-a)/((R : ℂ)^2-conj a*z) := funext (canonical_reciprocal_eq R a)
  rw [he]
  intro z hz
  exact (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (canonical_numerator_ne_zero R a z ha hz)

omit h0 in
theorem inverseZeroProduct_apply (R : ℝ) (z : ℂ) :
    inverseZeroProduct f R z =
      ∏ᶠ a : ℂ, canonicalFactor R a z ^ (-divisor f (ball 0 R) a) := by
  let d := divisor f (ball (0 : ℂ) R)
  have hs : (Function.support d).Finite :=
    ((ha).mono (subset_univ (closedBall (0 : ℂ) R))).meromorphicOn.divisor_ball_support_finite
  have hf : Function.HasFiniteMulSupport (fun a : ℂ => (canonicalFactor R a)^(-d a)) := by
    apply hs.subset
    intro a ha
    by_contra h
    have he : d a = 0 := by simpa only [Function.mem_support,not_not] using h
    simp only [Function.mem_mulSupport,he,neg_zero,zpow_zero,ne_eq,not_true_eq_false] at ha
  exact finprod_apply hf z

omit h0 in
theorem inverseZeroProduct_analytic (R : ℝ) :
    AnalyticOnNhd ℂ (inverseZeroProduct f R) (closedBall 0 R) := by
  have hf := ha
  intro z hz
  apply analyticAt_finprod
  intro a
  let d := divisor f (ball (0 : ℂ) R)
  by_cases hd : d a = 0
  · simp only [show divisor f (ball 0 R) a = 0 from hd,neg_zero,zpow_zero]
    exact analyticAt_const
  · have ha := d.supportWithinDomain hd
    have hn : 0 ≤ d a := ((hf).mono (subset_univ (ball (0 : ℂ) R))).divisor_nonneg a
    have he : (canonicalFactor R a)^(-d a) = (fun w => (canonicalFactor R a w)⁻¹)^(d a) := by
      funext w
      simp only [Pi.pow_apply,Pi.inv_apply,zpow_neg,inv_zpow]
    rw [he]
    exact (canonical_reciprocal_analytic R a ha z hz).zpow_nonneg hn

omit h0 in
theorem reconstruction (R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp f h R)
    (hboundary : divisor f (sphere 0 R) = 0) :
    ∀ z ∈ closedBall (0 : ℂ) R, f z = inverseZeroProduct f R z * h z := by
  have hF := (ha).mono (subset_univ (closedBall (0 : ℂ) R))
  have hG := (inverseZeroProduct_analytic f ha R).mul D.analyticOnNhd
  have he : f =ᶠ[codiscreteWithin (closedBall (0 : ℂ) R)] inverseZeroProduct f R * h := by
    have hd := D.eventuallyEq
    rw [hboundary] at hd
    simpa only [Function.locallyFinsuppWithin.coe_zero,Pi.zero_apply,neg_zero,zpow_zero,
      finprod_one,mul_one,smul_eq_mul,inverseZeroProduct] using hd
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hl := (hF 0 (ball_subset_closedBall h0)).meromorphicAt
    |>.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (hG 0 (ball_subset_closedBall h0)).meromorphicAt h0 isOpen_ball.preperfect
      (he.filter_mono (codiscreteWithin_mono ball_subset_closedBall))
  have hball : EqOn f (inverseZeroProduct f R * h) (ball (0 : ℂ) R) :=
    (hF.mono ball_subset_closedBall).eqOn_of_preconnected_of_frequently_eq
      (hG.mono ball_subset_closedBall) (convex_ball (0 : ℂ) R).isPreconnected h0 hl.frequently
  have hall := hball.of_subset_closure hF.continuousOn hG.continuousOn ball_subset_closedBall
    (by rw [closure_ball (0 : ℂ) hR.ne'])
  exact hall

theorem inverseZeroProduct_origin_ne_zero (R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp f h R)
    (hboundary : divisor f (sphere 0 R) = 0) : inverseZeroProduct f R 0 ≠ 0 := by
  have hn : f 0 ≠ 0 := h0
  have he := reconstruction f ha R hR h D hboundary 0 (mem_closedBall_self hR.le)
  exact (mul_ne_zero_iff.mp (he ▸ hn)).1

omit h0 in
theorem normalized_reconstruction (R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp f h R)
    (hboundary : divisor f (sphere 0 R) = 0) :
    ∀ z ∈ closedBall (0 : ℂ) R, f z / f 0 =
      (inverseZeroProduct f R z / inverseZeroProduct f R 0) * (h z/h 0) := by
  intro z hz
  rw [reconstruction f ha R hR h D hboundary z hz,
    reconstruction f ha R hR h D hboundary 0 (mem_closedBall_self hR.le)]
  ring

end OperatorDerivativeRewrite.Foundation.EvenEntireCanonicalApproximation

noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.EvenEntireCanonicalApproximation
variable (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f univ) (h0 : f 0 ≠ 0)
  (heven : ∀ z : ℂ, f (-z)=f z)
include ha h0 heven

theorem exists_product_approximation
    (hgrowth : ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, ‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖)) :
    ∃ r : ℝ → ℝ, ∃ h : ℝ → ℂ → ℂ,
      (∀ R : ℝ, 1 ≤ R → 2*R < r R ∧ r R < 2*R+1 ∧
        ECanonicalDecomp f (h R) (r R) ∧
        divisor f (sphere 0 (r R)) = 0 ∧
        inverseZeroProduct f (r R) 0 ≠ 0 ∧
        ∀ z ∈ closedBall (0 : ℂ) (r R),
          f z = inverseZeroProduct f (r R) z * h R z) ∧
      TendstoLocallyUniformly
        (fun R z => inverseZeroProduct f (r R) z / inverseZeroProduct f (r R) 0)
        (fun z => f z / f 0) atTop ∧
      TendstoLocallyUniformly
        (fun R z => f 0 * (inverseZeroProduct f (r R) z / inverseZeroProduct f (r R) 0))
        f atTop := by
  obtain ⟨A,hA,r,h,g,hs,hlog,hexp,hquot⟩ :=
    exists_locally_uniform_remainders f ha h0 heven hgrowth
  have hdata (R : ℝ) (hR : 1 ≤ R) : 2*R < r R ∧ r R < 2*R+1 ∧
      ECanonicalDecomp f (h R) (r R) ∧
      divisor f (sphere 0 (r R)) = 0 ∧
      inverseZeroProduct f (r R) 0 ≠ 0 ∧
      ∀ z ∈ closedBall (0 : ℂ) (r R), f z = inverseZeroProduct f (r R) z * h R z := by
    obtain ⟨hrl,hru,hbd,D,hg,hg0,hd0,hd,he,hre⟩ := hs R hR
    have hrp : 0 < r R := by linarith
    exact ⟨hrl,hru,D,hbd,inverseZeroProduct_origin_ne_zero f ha h0 (r R) hrp (h R) D hbd,
      reconstruction f ha (r R) hrp (h R) D hbd⟩
  let F : ℂ → ℂ := fun z => f z / f 0
  have hFc : Continuous F := (differentiableOn_univ.mp ha.differentiableOn).continuous.div_const _
  have hconst : TendstoLocallyUniformly (fun _ : ℝ => F) F atTop := by
    apply TendstoUniformly.tendstoLocallyUniformly
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    exact Eventually.of_forall fun R z => by simpa using hε
  have hdiv : TendstoLocallyUniformly (fun R z => F z / (h R z/h R 0)) F atTop := by
    have hh := hconst.div₀ hquot hFc continuous_const (by intro z; norm_num)
    have he : F / (fun _ : ℂ => (1 : ℂ)) = F := by funext z; simp
    rw [he] at hh
    exact hh
  have hprod : TendstoLocallyUniformly
      (fun R z => inverseZeroProduct f (r R) z / inverseZeroProduct f (r R) 0) F atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨ρ,hρ,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    apply (tendstoLocallyUniformly_iff_forall_isCompact.mp hdiv K hK).congr
    filter_upwards [eventually_ge_atTop (max 1 (ρ+1))] with R hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    obtain ⟨hrl,hru,D,hbd,hB0,hrec⟩ := hdata R hR1
    have hrp : 0 < r R := by linarith
    intro z hz
    have hzr : z ∈ closedBall (0 : ℂ) (r R) := mem_closedBall_zero_iff.mpr (by
      have hn := mem_closedBall_zero_iff.mp (hsub hz)
      linarith [(le_max_right 1 (ρ+1)).trans hR])
    have hn : h R z/h R 0 ≠ 0 := div_ne_zero (D.ne_zero z hzr)
      (D.ne_zero 0 (mem_closedBall_self hrp.le))
    have he := normalized_reconstruction f ha (r R) hrp (h R) D hbd z hzr
    exact ((eq_div_iff hn).mpr he.symm).symm
  have hscale : TendstoLocallyUniformly
      (fun R z => f 0 * (inverseZeroProduct f (r R) z / inverseZeroProduct f (r R) 0))
      f atTop := by
    have hc : TendstoLocallyUniformly (fun _ : ℝ => fun _ : ℂ => f 0)
        (fun _ => f 0) atTop := by
      apply TendstoUniformly.tendstoLocallyUniformly
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      exact Eventually.of_forall fun R z => by simpa using hε
    have hh := hc.mul₀ hprod continuous_const hFc
    have hn : f 0 ≠ 0 := h0
    have he : (fun _ : ℂ => f 0) * F = f := by
      funext z
      dsimp [F]
      field_simp
    rw [he] at hh
    exact hh
  exact ⟨r,h,hdata,hprod,hscale⟩

end OperatorDerivativeRewrite.Foundation.EvenEntireCanonicalApproximation
