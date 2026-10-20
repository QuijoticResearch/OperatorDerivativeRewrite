import Foundation.RiemannQuarticDiskDecomposition
import Foundation.RiemannQuarticGlobalSimpleZeros
import Mathlib.Analysis.Calculus.LogDeriv

/-! Actual opposite-zero multiplicities and canonical logarithmic
derivatives. No real-zero assumption or simple-zero assumption is used. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalDerivative
open RiemannQuarticFlow RiemannQuarticEvolution RiemannQuarticReality
open RiemannQuarticZeroCounting

theorem flow_order_neg (t : ℝ) (z : ℂ) :
    meromorphicOrderAt (flow t) (-z) = meromorphicOrderAt (flow t) z := by
  have hc := meromorphicOrderAt_comp_of_deriv_ne_zero (f := flow t)
    (g := fun w : ℂ => -w) (x := z) (by fun_prop) (by simp)
  have he : flow t ∘ (fun w : ℂ => -w) = flow t := funext (flow_even t)
  rw [he] at hc
  exact hc.symm

theorem ball_divisor_neg (t R : ℝ) (z : ℂ) :
    divisor (flow t) (ball 0 R) (-z) = divisor (flow t) (ball 0 R) z := by
  have ha := (flow_analytic t).mono (subset_univ (ball (0 : ℂ) R))
  by_cases hz : z ∈ ball (0 : ℂ) R
  · have hn : -z ∈ ball (0 : ℂ) R := by simpa using hz
    rw [ha.meromorphicOn.divisor_apply hn,ha.meromorphicOn.divisor_apply hz,flow_order_neg]
  · have hn : -z ∉ ball (0 : ℂ) R := by simpa using hz
    rw [(divisor (flow t) (ball 0 R)).apply_eq_zero_of_notMem hz,
      (divisor (flow t) (ball 0 R)).apply_eq_zero_of_notMem hn]

theorem ball_divisor_zero_at_origin (t R : ℝ) :
    divisor (flow t) (ball 0 R) 0 = 0 := by
  by_cases hz : (0 : ℂ) ∈ ball 0 R
  · have ha := flow_analytic t
    have hn : flow t 0 ≠ 0 := by simpa using flow_ne_zero_on_imaginary_axis t 0
    rw [((ha.mono (subset_univ (ball (0 : ℂ) R))).meromorphicOn).divisor_apply hz,
      (ha 0 (mem_univ _)).meromorphicOrderAt_eq,
      (ha 0 (mem_univ _)).analyticOrderAt_eq_zero.mpr hn]
    simp
  · exact (divisor (flow t) (ball 0 R)).apply_eq_zero_of_notMem hz

theorem canonical_logDeriv_zero (R : ℝ) (hR : 0 < R) (a : ℂ) (ha : a ≠ 0) :
    logDeriv (canonicalFactor R a) 0 = 1/a - conj a/(R : ℂ)^2 := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hN := (hasDerivAt_const (0 : ℂ) ((R : ℂ)^2)).sub
    ((hasDerivAt_id (0 : ℂ)).const_mul (conj a))
  have hD := ((hasDerivAt_id (0 : ℂ)).sub_const a).const_mul (R : ℂ)
  have hd := hN.div hD (by simpa using mul_ne_zero hRc (neg_ne_zero.mpr ha))
  change HasDerivAt (canonicalFactor R a) _ 0 at hd
  rw [logDeriv_apply,hd.deriv,canonicalFactor_apply]
  simp only [Pi.sub_apply,id_eq,mul_zero,sub_zero,zero_sub,zero_mul]
  field_simp
  ring

theorem canonical_logDeriv_sum_zero (t R : ℝ) :
    (∑ᶠ a : ℂ, (divisor (flow t) (ball 0 R) a : ℂ) *
      (1/a-conj a/(R : ℂ)^2)) = 0 := by
  let F : ℂ → ℂ := fun a => (divisor (flow t) (ball 0 R) a : ℂ) *
    (1/a-conj a/(R : ℂ)^2)
  have hodd (a : ℂ) : F (-a) = -F a := by
    dsimp [F]
    rw [ball_divisor_neg]
    simp only [one_div,inv_neg,map_neg,neg_div]
    ring
  have he := finsum_comp (fun a : ℂ => -a) (Equiv.neg ℂ).bijective (g := F)
  simp_rw [hodd] at he
  rw [finsum_neg_distrib] at he
  change (∑ᶠ a, F a) = 0
  linear_combination -he / 2

theorem canonical_remainder_eq_at_ne_zero (t R : ℝ) (hR : 0 < R)
    (h : ℂ → ℂ) (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) (hne : flow t z ≠ 0) :
    h z = (∏ᶠ a : ℂ, canonicalFactor R a z ^ (divisor (flow t) (ball 0 R) a)) * flow t z := by
  have ha := flow_analytic t
  have ho : meromorphicOrderAt (flow t) z = 0 := by
    rw [(ha z (mem_univ _)).meromorphicOrderAt_eq,
      (ha z (mem_univ _)).analyticOrderAt_eq_zero.mpr hne]
    simp
  have he := D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt hz ho hR
  rw [hboundary] at he
  simpa only [Function.locallyFinsuppWithin.coe_zero,Pi.zero_apply,neg_zero,zpow_zero,
    finprod_one,mul_one,smul_eq_mul,
    (ha z (mem_univ _)).meromorphicTrailingCoeffAt_of_ne_zero hne] using he

theorem canonical_remainder_deriv_zero (t R : ℝ) (hR : 0 < R)
    (h : ℂ → ℂ) (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) : deriv h 0 = 0 := by
  classical
  let d := divisor (flow t) (ball (0 : ℂ) R)
  have hs : (Function.support d).Finite := D.meromorphicOn.divisor_ball_support_finite
  let S : Finset ℂ := hs.toFinset
  have hmem (a : ℂ) : a ∈ S ↔ d a ≠ 0 := by simp [S,Function.mem_support]
  have ha0 (a : ℂ) (ha : a ∈ S) : a ≠ 0 := by
    intro he
    subst a
    exact (hmem 0).mp ha (ball_divisor_zero_at_origin t R)
  have haB (a : ℂ) (ha : a ∈ S) : a ∈ ball (0 : ℂ) R :=
    d.supportWithinDomain ((hmem a).mp ha)
  have hCFne (a : ℂ) (ha : a ∈ S) : canonicalFactor R a 0 ≠ 0 :=
    canonicalFactor_ne_zero (haB a ha) (mem_closedBall_self hR.le) (Ne.symm (ha0 a ha))
  have hCFdiff (a : ℂ) (ha : a ∈ S) : DifferentiableAt ℂ (canonicalFactor R a) 0 :=
    (analyticOnNhd_canonicalFactor R a 0 (Ne.symm (ha0 a ha))).differentiableAt
  let P : ℂ → ℂ := fun z => ∏ a ∈ S, canonicalFactor R a z ^ d a
  have hPne : P 0 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a ha => zpow_ne_zero _ (hCFne a ha)
  have hPdiff : DifferentiableAt ℂ P 0 := by
    apply DifferentiableAt.fun_finsetProd
    intro a ha
    exact (hCFdiff a ha).zpow (Or.inl (hCFne a ha))
  have hPlog : logDeriv P 0 = 0 := by
    have he := logDeriv_prod
      (f := fun a z => canonicalFactor R a z ^ d a) (s := S) (x := (0 : ℂ))
      (fun a ha => zpow_ne_zero _ (hCFne a ha))
      (fun a ha => (hCFdiff a ha).zpow (Or.inl (hCFne a ha)))
    have hPeq : (∏ a ∈ S, fun z : ℂ => canonicalFactor R a z ^ d a) = P := by
      funext z
      simp [P]
    rw [hPeq] at he
    rw [he]
    have hsum : (∑ᶠ a : ℂ, (d a : ℂ)*(1/a-conj a/(R : ℂ)^2)) =
        ∑ a ∈ S, (d a : ℂ)*(1/a-conj a/(R : ℂ)^2) := by
      apply finsum_eq_sum_of_support_subset
      intro a ha
      apply (hmem a).mpr
      intro hzero
      simp only [Function.mem_support,hzero,Int.cast_zero,zero_mul,ne_eq,not_true_eq_false] at ha
    calc
      _ = ∑ a ∈ S, (d a : ℂ)*(1/a-conj a/(R : ℂ)^2) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [logDeriv_fun_zpow (hCFdiff a ha),canonical_logDeriv_zero R hR a (ha0 a ha)]
      _ = ∑ᶠ a : ℂ, (d a : ℂ)*(1/a-conj a/(R : ℂ)^2) := hsum.symm
      _ = 0 := canonical_logDeriv_sum_zero t R
  have hprod (z : ℂ) : (∏ᶠ a : ℂ, canonicalFactor R a z ^ d a) = P z := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro a ha
    apply (hmem a).mpr
    intro hzero
    simp only [Function.mem_mulSupport,hzero,zpow_zero,ne_eq,not_true_eq_false] at ha
  have hn : flow t 0 ≠ 0 := by simpa using flow_ne_zero_on_imaginary_axis t 0
  have hlocal : h =ᶠ[𝓝 (0 : ℂ)] fun z => P z * flow t z := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR),
      (flow_differentiable t 0).continuousAt.eventually_ne hn] with z hz hne
    rw [canonical_remainder_eq_at_ne_zero t R hR h D hboundary z (ball_subset_closedBall hz) hne]
    rw [hprod]
  have hf0 : deriv (flow t) 0 = 0 := by
    have hd := RiemannQuarticGlobalSimpleZeros.deriv_flow_neg t 0
    simp only [neg_zero] at hd
    linear_combination hd / 2
  have hhlog : logDeriv h 0 = 0 := by
    have he := (logDeriv_congr_nhds hlocal).eq_of_nhds
    rw [he,logDeriv_fun_mul 0 hPne hn hPdiff (flow_differentiable t 0),hPlog]
    simp only [logDeriv_apply,hf0,zero_div,add_zero]
  have hhne : h 0 ≠ 0 := D.ne_zero 0 (mem_closedBall_self hR.le)
  exact (div_eq_zero_iff.mp hhlog).resolve_right hhne

theorem exists_actual_zero_derivative_log_remainder (t R : ℝ) (hR : 0 ≤ R) :
    ∃ r : ℝ, R < r ∧ r < R+1 ∧
      divisor (flow t) (sphere 0 r) = 0 ∧
      ∃ h g : ℂ → ℂ, ECanonicalDecomp (flow t) h r ∧
        DifferentiableOn ℂ g (ball 0 r) ∧ g 0 = 0 ∧ deriv g 0 = 0 ∧
        (∀ z ∈ ball (0 : ℂ) r, HasDerivAt g (deriv h z / h z) z) ∧
        ∀ z ∈ ball (0 : ℂ) r, Complex.exp (g z) = h z / h 0 := by
  obtain ⟨r,hr,hr1,hboundary,h,g,D,hg,h0,hd,he⟩ :=
    RiemannQuarticDiskDecomposition.exists_actual_disk_log_remainder t R hR
  have hrp : 0 < r := lt_of_le_of_lt hR hr
  have hd0 : deriv g 0 = 0 := by
    rw [(hd 0 (mem_ball_self hrp)).deriv,
      canonical_remainder_deriv_zero t r hrp h D hboundary,zero_div]
  exact ⟨r,hr,hr1,hboundary,h,g,D,hg,h0,hd0,hd,he⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalDerivative
