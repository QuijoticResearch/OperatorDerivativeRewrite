import Foundation.EntireDiskDecomposition
import Mathlib.Analysis.Calculus.LogDeriv

/-! Even entire-function canonical logarithms with zero derivative at the origin.
The established quartic proof is generalized to explicit analytic, nonvanishing
and evenness hypotheses; no real-zero or simple-zero assumption is used. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.EvenEntireCanonicalDerivative
variable (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f univ)
  (h0 : f 0 ≠ 0) (heven : ∀ z : ℂ, f (-z)=f z)
include ha h0 heven

omit ha h0 in
theorem order_neg  (z : ℂ) :
    meromorphicOrderAt f (-z) = meromorphicOrderAt f z := by
  have hc := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f)
    (g := fun w : ℂ => -w) (x := z) (by fun_prop) (by simp)
  have he : f ∘ (fun w : ℂ => -w) = f := funext heven
  rw [he] at hc
  exact hc.symm

omit h0 in
theorem ball_divisor_neg (R : ℝ) (z : ℂ) :
    divisor f (ball 0 R) (-z) = divisor f (ball 0 R) z := by
  have ha := (ha).mono (subset_univ (ball (0 : ℂ) R))
  by_cases hz : z ∈ ball (0 : ℂ) R
  · have hn : -z ∈ ball (0 : ℂ) R := by simpa using hz
    rw [ha.meromorphicOn.divisor_apply hn,ha.meromorphicOn.divisor_apply hz,order_neg f heven]
  · have hn : -z ∉ ball (0 : ℂ) R := by simpa using hz
    rw [(divisor f (ball 0 R)).apply_eq_zero_of_notMem hz,
      (divisor f (ball 0 R)).apply_eq_zero_of_notMem hn]

omit heven in
theorem ball_divisor_zero_at_origin (R : ℝ) :
    divisor f (ball 0 R) 0 = 0 := by
  by_cases hz : (0 : ℂ) ∈ ball 0 R
  · have ha := ha
    have hn : f 0 ≠ 0 := h0
    rw [((ha.mono (subset_univ (ball (0 : ℂ) R))).meromorphicOn).divisor_apply hz,
      (ha 0 (mem_univ _)).meromorphicOrderAt_eq,
      (ha 0 (mem_univ _)).analyticOrderAt_eq_zero.mpr hn]
    simp
  · exact (divisor f (ball 0 R)).apply_eq_zero_of_notMem hz

omit ha h0 heven in
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

omit h0 in
theorem canonical_logDeriv_sum_zero (R : ℝ) :
    (∑ᶠ a : ℂ, (divisor f (ball 0 R) a : ℂ) *
      (1/a-conj a/(R : ℂ)^2)) = 0 := by
  let F : ℂ → ℂ := fun a => (divisor f (ball 0 R) a : ℂ) *
    (1/a-conj a/(R : ℂ)^2)
  have hodd (a : ℂ) : F (-a) = -F a := by
    dsimp [F]
    rw [ball_divisor_neg f ha heven]
    simp only [one_div,inv_neg,map_neg,neg_div]
    ring
  have he := finsum_comp (fun a : ℂ => -a) (Equiv.neg ℂ).bijective (g := F)
  simp_rw [hodd] at he
  rw [finsum_neg_distrib] at he
  change (∑ᶠ a, F a) = 0
  linear_combination -he / 2

omit h0 heven in
theorem canonical_remainder_eq_at_ne_zero (R : ℝ) (hR : 0 < R)
    (h : ℂ → ℂ) (D : ECanonicalDecomp f h R)
    (hboundary : divisor f (sphere 0 R) = 0)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) (hne : f z ≠ 0) :
    h z = (∏ᶠ a : ℂ, canonicalFactor R a z ^ (divisor f (ball 0 R) a)) * f z := by
  have ho : meromorphicOrderAt f z = 0 := by
    rw [(ha z (mem_univ _)).meromorphicOrderAt_eq,
      (ha z (mem_univ _)).analyticOrderAt_eq_zero.mpr hne]
    simp
  have he := D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt hz ho hR
  rw [hboundary] at he
  simpa only [Function.locallyFinsuppWithin.coe_zero,Pi.zero_apply,neg_zero,zpow_zero,
    finprod_one,mul_one,smul_eq_mul,
    (ha z (mem_univ _)).meromorphicTrailingCoeffAt_of_ne_zero hne] using he

theorem canonical_remainder_deriv_zero (R : ℝ) (hR : 0 < R)
    (h : ℂ → ℂ) (D : ECanonicalDecomp f h R)
    (hboundary : divisor f (sphere 0 R) = 0) : deriv h 0 = 0 := by
  classical
  have hf := ha
  let d := divisor f (ball (0 : ℂ) R)
  have hs : (Function.support d).Finite := D.meromorphicOn.divisor_ball_support_finite
  let S : Finset ℂ := hs.toFinset
  have hmem (a : ℂ) : a ∈ S ↔ d a ≠ 0 := by simp [S,Function.mem_support]
  have ha0 (a : ℂ) (ha : a ∈ S) : a ≠ 0 := by
    intro he
    subst a
    exact (hmem 0).mp ha (ball_divisor_zero_at_origin f hf h0 R)
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
      _ = 0 := canonical_logDeriv_sum_zero f ha heven R
  have hprod (z : ℂ) : (∏ᶠ a : ℂ, canonicalFactor R a z ^ d a) = P z := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro a ha
    apply (hmem a).mpr
    intro hzero
    simp only [Function.mem_mulSupport,hzero,zpow_zero,ne_eq,not_true_eq_false] at ha
  have hn : f 0 ≠ 0 := h0
  have hlocal : h =ᶠ[𝓝 (0 : ℂ)] fun z => P z * f z := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR),
      (ha 0 (mem_univ _)).differentiableAt.continuousAt.eventually_ne hn] with z hz hne
    rw [canonical_remainder_eq_at_ne_zero f ha R hR h D hboundary z (ball_subset_closedBall hz) hne]
    rw [hprod]
  have hf0 : deriv f 0 = 0 := by
    have hd := (((ha (-(0:ℂ)) (mem_univ _)).differentiableAt.hasDerivAt).comp (0:ℂ)
      (hasDerivAt_neg (0:ℂ))).deriv
    simp only [neg_zero] at hd
    have hfe : (fun z : ℂ => f (-z))=f := funext heven
    change deriv (fun z : ℂ => f (-z)) 0=deriv f 0 * -1 at hd
    rw [hfe] at hd
    linear_combination hd / 2
  have hhlog : logDeriv h 0 = 0 := by
    have he := (logDeriv_congr_nhds hlocal).eq_of_nhds
    rw [he,logDeriv_fun_mul 0 hPne hn hPdiff (ha 0 (mem_univ _)).differentiableAt,hPlog]
    simp only [logDeriv_apply,hf0,zero_div,add_zero]
  have hhne : h 0 ≠ 0 := D.ne_zero 0 (mem_closedBall_self hR.le)
  exact (div_eq_zero_iff.mp hhlog).resolve_right hhne

theorem exists_zero_derivative_log_remainder (R : ℝ) (hR : 0 ≤ R) :
    ∃ r : ℝ, R < r ∧ r < R+1 ∧
      divisor f (sphere 0 r) = 0 ∧
      ∃ h g : ℂ → ℂ, ECanonicalDecomp f h r ∧
        DifferentiableOn ℂ g (ball 0 r) ∧ g 0 = 0 ∧ deriv g 0 = 0 ∧
        (∀ z ∈ ball (0 : ℂ) r, HasDerivAt g (deriv h z / h z) z) ∧
        ∀ z ∈ ball (0 : ℂ) r, Complex.exp (g z) = h z / h 0 := by
  obtain ⟨r,hr,hr1,hboundary,h,g,D,hg,hg0,hd,he⟩ :=
    EntireDiskDecomposition.exists_disk_log_remainder f ha h0 R hR
  have hrp : 0 < r := lt_of_le_of_lt hR hr
  have hd0 : deriv g 0 = 0 := by
    rw [(hd 0 (mem_ball_self hrp)).deriv,
      canonical_remainder_deriv_zero f ha h0 heven r hrp h D hboundary,zero_div]
  exact ⟨r,hr,hr1,hboundary,h,g,D,hg,hg0,hd0,hd,he⟩

end OperatorDerivativeRewrite.Foundation.EvenEntireCanonicalDerivative
