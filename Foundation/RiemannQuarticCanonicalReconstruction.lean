import Foundation.RiemannQuarticCanonicalLimit
import Mathlib.Analysis.Analytic.Uniqueness

/-! The actual finite reciprocal canonical product is analytic on the
closed disk, including its original zero locations. Reconstruction is
proved there as an identity of functions, rather than only off a discrete set. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalReconstruction
open RiemannQuarticFlow RiemannQuarticReality RiemannQuarticZeroCounting

def inverseZeroProduct (t R : ℝ) : ℂ → ℂ :=
  ∏ᶠ a : ℂ, (canonicalFactor R a) ^ (-divisor (flow t) (ball 0 R) a)

theorem canonical_reciprocal_eq (R : ℝ) (a z : ℂ) :
    (canonicalFactor R a z)⁻¹ = (R : ℂ)*(z-a)/((R : ℂ)^2-conj a*z) := by
  rw [canonicalFactor_apply,inv_div]

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

theorem canonical_reciprocal_analytic (R : ℝ) (a : ℂ) (ha : a ∈ ball (0 : ℂ) R) :
    AnalyticOnNhd ℂ (fun z => (canonicalFactor R a z)⁻¹) (closedBall 0 R) := by
  have he : (fun z => (canonicalFactor R a z)⁻¹) =
      fun z => (R : ℂ)*(z-a)/((R : ℂ)^2-conj a*z) := funext (canonical_reciprocal_eq R a)
  rw [he]
  intro z hz
  exact (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (canonical_numerator_ne_zero R a z ha hz)

theorem inverseZeroProduct_apply (t R : ℝ) (z : ℂ) :
    inverseZeroProduct t R z =
      ∏ᶠ a : ℂ, canonicalFactor R a z ^ (-divisor (flow t) (ball 0 R) a) := by
  let d := divisor (flow t) (ball (0 : ℂ) R)
  have hs : (Function.support d).Finite :=
    ((flow_analytic t).mono (subset_univ (closedBall (0 : ℂ) R))).meromorphicOn.divisor_ball_support_finite
  have hf : Function.HasFiniteMulSupport (fun a : ℂ => (canonicalFactor R a)^(-d a)) := by
    apply hs.subset
    intro a ha
    by_contra h
    have he : d a = 0 := by simpa only [Function.mem_support,not_not] using h
    simp only [Function.mem_mulSupport,he,neg_zero,zpow_zero,ne_eq,not_true_eq_false] at ha
  exact finprod_apply hf z

theorem inverseZeroProduct_analytic (t R : ℝ) :
    AnalyticOnNhd ℂ (inverseZeroProduct t R) (closedBall 0 R) := by
  intro z hz
  apply analyticAt_finprod
  intro a
  let d := divisor (flow t) (ball (0 : ℂ) R)
  by_cases hd : d a = 0
  · simp only [show divisor (flow t) (ball 0 R) a = 0 from hd,neg_zero,zpow_zero]
    exact analyticAt_const
  · have ha := d.supportWithinDomain hd
    have hn : 0 ≤ d a := ((flow_analytic t).mono (subset_univ (ball (0 : ℂ) R))).divisor_nonneg a
    have he : (canonicalFactor R a)^(-d a) = (fun w => (canonicalFactor R a w)⁻¹)^(d a) := by
      funext w
      simp only [Pi.pow_apply,Pi.inv_apply,zpow_neg,inv_zpow]
    rw [he]
    exact (canonical_reciprocal_analytic R a ha z hz).zpow_nonneg hn

theorem actual_reconstruction (t R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) :
    ∀ z ∈ closedBall (0 : ℂ) R, flow t z = inverseZeroProduct t R z * h z := by
  have hF := (flow_analytic t).mono (subset_univ (closedBall (0 : ℂ) R))
  have hG := (inverseZeroProduct_analytic t R).mul D.analyticOnNhd
  have he : flow t =ᶠ[codiscreteWithin (closedBall (0 : ℂ) R)] inverseZeroProduct t R * h := by
    have hd := D.eventuallyEq
    rw [hboundary] at hd
    simpa only [Function.locallyFinsuppWithin.coe_zero,Pi.zero_apply,neg_zero,zpow_zero,
      finprod_one,mul_one,smul_eq_mul,inverseZeroProduct] using hd
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hl := (hF 0 (ball_subset_closedBall h0)).meromorphicAt
    |>.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (hG 0 (ball_subset_closedBall h0)).meromorphicAt h0 isOpen_ball.preperfect
      (he.filter_mono (codiscreteWithin_mono ball_subset_closedBall))
  have hball : EqOn (flow t) (inverseZeroProduct t R * h) (ball (0 : ℂ) R) :=
    (hF.mono ball_subset_closedBall).eqOn_of_preconnected_of_frequently_eq
      (hG.mono ball_subset_closedBall) (convex_ball (0 : ℂ) R).isPreconnected h0 hl.frequently
  have hall := hball.of_subset_closure hF.continuousOn hG.continuousOn ball_subset_closedBall
    (by rw [closure_ball (0 : ℂ) hR.ne'])
  exact hall

theorem inverseZeroProduct_origin_ne_zero (t R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) : inverseZeroProduct t R 0 ≠ 0 := by
  have hn : flow t 0 ≠ 0 := by simpa using flow_ne_zero_on_imaginary_axis t 0
  have he := actual_reconstruction t R hR h D hboundary 0 (mem_closedBall_self hR.le)
  exact (mul_ne_zero_iff.mp (he ▸ hn)).1

theorem normalized_reconstruction (t R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) :
    ∀ z ∈ closedBall (0 : ℂ) R, flow t z / flow t 0 =
      (inverseZeroProduct t R z / inverseZeroProduct t R 0) * (h z/h 0) := by
  intro z hz
  rw [actual_reconstruction t R hR h D hboundary z hz,
    actual_reconstruction t R hR h D hboundary 0 (mem_closedBall_self hR.le)]
  ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalReconstruction
