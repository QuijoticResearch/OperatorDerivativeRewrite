import Foundation.EvenEntireZeroFreeRigidity
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.Algebra.Polynomial

/-! Focused finite-zero factorization for the actual Fourier-flow audit.
The codiscrete meromorphic extraction is upgraded to a pointwise entire identity. -/
noncomputable section
open Set Filter Complex Polynomial MeasureTheory MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.SubquadraticFiniteZeroFactorization
open EvenEntireZeroFreeRigidity

private theorem radius_linear_bound (r : ℝ) (hr : 0 ≤ r) :
    r ≤ 1+r*Real.sqrt r := by
  by_cases h : r ≤ 1
  · nlinarith [Real.sqrt_nonneg r]
  · have hs : 1 ≤ Real.sqrt r := (Real.le_sqrt (by norm_num) hr).mpr (by nlinarith)
    nlinarith

theorem zero_free_exponential_affine (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) (C : ℝ) (hC : 0 < C)
    (hb : ∀ z, ‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖)) :
    ∃ a : ℂ, ∀ z : ℂ, f z = f 0*Complex.exp (a*z) := by
  obtain ⟨h,hh,hexp⟩ := exists_entire_log f hf hne
  let g : ℂ → ℂ := fun z => h z-h 0
  have hg : Differentiable ℂ g := hh.sub_const _
  have h0 : g 0 = 0 := sub_self _
  have he (z : ℂ) : Complex.exp (g z) = f z/f 0 := by
    simp only [g,Complex.exp_sub,hexp]
  let A : ℝ := |Real.log C|+|Real.log ‖f 0‖|+1
  have hgrowth (z : ℂ) : (g z).re ≤ A+‖z‖*Real.sqrt ‖z‖ := by
    have hn : 0 < ‖f 0‖ := norm_pos_iff.mpr (hne 0)
    have hz : 0 < ‖f z‖ := norm_pos_iff.mpr (hne z)
    have hnorm := congrArg norm (he z)
    rw [Complex.norm_exp,norm_div] at hnorm
    have hl := Real.log_le_log hz (hb z)
    rw [Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _),Real.log_exp] at hl
    have heq := congrArg Real.log hnorm
    rw [Real.log_exp,Real.log_div (ne_of_gt hz) (ne_of_gt hn)] at heq
    dsimp [A]
    linarith [le_abs_self (Real.log C),neg_le_abs (Real.log ‖f 0‖)]
  let a := deriv g 0
  let q : ℂ → ℂ := fun z => g z-a*z
  have hq : Differentiable ℂ q := hg.sub ((differentiable_const a).mul differentiable_id)
  have hq0 : q 0 = 0 := by simp [q,h0]
  have hd0 : deriv q 0 = 0 := by
    have hd := (hg 0).hasDerivAt.sub ((hasDerivAt_id (0 : ℂ)).const_mul a)
    change HasDerivAt q (deriv g 0-a*1) 0 at hd
    simpa only [mul_one,a,sub_self] using hd.deriv
  have hqgrowth (z : ℂ) : (q z).re ≤ (A+‖a‖)+(1+‖a‖)*(‖z‖*Real.sqrt ‖z‖) := by
    have hn := Complex.re_le_norm (-(a*z))
    simp only [Complex.neg_re,norm_neg,norm_mul] at hn
    have hlin := mul_le_mul_of_nonneg_left (radius_linear_bound ‖z‖ (norm_nonneg z))
      (norm_nonneg a)
    change (g z).re-(a*z).re ≤ _
    nlinarith [hgrowth z]
  have hz := zero_of_zero_derivative_and_subquadratic_real_part q hq hq0 hd0
    (A+‖a‖) (1+‖a‖) (by dsimp [A]; positivity) (by positivity) hqgrowth
  refine ⟨a,fun z => ?_⟩
  have hgz : g z = a*z := sub_eq_zero.mp (hz z)
  have h := he z
  rw [hgz] at h
  exact (div_eq_iff (hne 0)).mp h.symm |>.trans (by ring)

theorem finite_zero_polynomial_factor (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (hfinite : {z : ℂ | f z = 0}.Finite) :
    ∃ (P : ℂ[X]) (g : ℂ → ℂ), P ≠ 0 ∧ Differentiable ℂ g ∧
      (∀ z, g z ≠ 0) ∧ ∀ z, f z = P.eval z*g z := by
  classical
  have ha : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hm0 : meromorphicOrderAt f 0 ≠ ⊤ := by
    rw [(ha 0 (mem_univ _)).meromorphicOrderAt_eq,
      (ha 0 (mem_univ _)).analyticOrderAt_eq_zero.mpr h0]
    simp
  have horder : ∀ z : (univ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ :=
    (ha.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).mp
      ⟨⟨0,mem_univ _⟩,hm0⟩
  let d := MeromorphicOn.divisor f univ
  have hd : (Function.support d).Finite := by
    rw [← ha.meromorphicNFOn.zero_set_eq_divisor_support horder]
    simpa only [univ_inter,Set.preimage,Set.mem_singleton_iff] using hfinite
  have hdpos (z : ℂ) : 0 ≤ d z := ha.divisor_nonneg z
  let P : ℂ[X] := ∏ u ∈ hd.toFinset, (X-C u)^(d u).toNat
  have hP : P ≠ 0 := by
    dsimp [P]
    exact Finset.prod_ne_zero_iff.mpr fun u _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero u)
  have hpoly : (∏ᶠ u : ℂ, (·-u)^(d u)) = fun z => P.eval z := by
    rw [Function.FactorizedRational.finprod_eq_fun hd]
    funext z
    rw [finprod_eq_prod_of_mulSupport_subset (s := hd.toFinset)]
    · simp only [P,Polynomial.eval_prod,Polynomial.eval_pow,Polynomial.eval_sub,
        Polynomial.eval_X,Polynomial.eval_C]
      apply Finset.prod_congr rfl
      intro u _
      have hint : ((d u).toNat : ℤ) = d u := Int.toNat_of_nonneg (hdpos u)
      have hp : (z-u)^((d u).toNat : ℤ) = (z-u)^(d u).toNat := by rw [zpow_natCast]
      rwa [hint] at hp
    · intro u hu
      have hs : u ∈ Function.support d := by
        change d u ≠ 0
        intro hz
        apply hu
        change (z-u)^(d u) = 1
        rw [hz,zpow_zero]
      exact (Finite.mem_toFinset hd).mpr hs
  obtain ⟨g,hg,hgn,hfg⟩ := ha.meromorphicOn.extract_zeros_poles horder hd
  have he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => P.eval z*g z) := by
    change f =ᶠ[codiscreteWithin (univ : Set ℂ)] (∏ᶠ u : ℂ, (·-u)^(d u))*g at hfg
    rw [hpoly] at hfg
    filter_upwards [hfg] with z hz
    exact hz
  have hgdiff : Differentiable ℂ g := fun z => (hg z (mem_univ _)).differentiableAt
  refine ⟨P,g,hP,hgdiff,fun z => hgn ⟨z,mem_univ _⟩,fun z => ?_⟩
  have hne : f =ᶠ[𝓝[≠] z] (fun w => P.eval w*g w) := by
    have h := (eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp he) z (mem_univ _)
    filter_upwards [h] with w hw
    exact hw (mem_univ _)
  have hleft : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
    hf.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hright : Tendsto f (𝓝[≠] z) (𝓝 (P.eval z*g z)) := by
    apply (tendsto_congr' hne).mpr
    exact (P.continuous.mul hgdiff.continuous).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hleft hright

private theorem polynomial_norm_lower (P : ℂ[X]) (hP : P ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ z : ℂ in cocompact ℂ, δ ≤ ‖P.eval z‖ := by
  by_cases hd : 0 < P.degree
  · have hn : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := by
      simpa only [dist_zero_right] using tendsto_dist_right_cocompact_atTop (0 : ℂ)
    exact ⟨1,by norm_num,(P.tendsto_norm_atTop hd hn).eventually (eventually_ge_atTop 1)⟩
  · have he := Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hd)
    have hc : P.coeff 0 ≠ 0 := by
      intro h
      apply hP
      rw [he,h]
      simp
    refine ⟨‖P.coeff 0‖,norm_pos_iff.mpr hc,Eventually.of_forall ?_⟩
    intro z
    have hconst : P.eval z = P.coeff 0 := by
      nth_rw 1 [he]
      exact eval_C
    rw [hconst]

theorem polynomial_factor_growth (f g : ℂ → ℂ) (P : ℂ[X]) (hP : P ≠ 0)
    (hg : Continuous g) (he : ∀ z, f z = P.eval z*g z)
    (C : ℝ) (hC : 0 < C) (hb : ∀ z, ‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖)) :
    ∃ D : ℝ, 0 < D ∧ ∀ z, ‖g z‖ ≤ D*Real.exp (‖z‖*Real.sqrt ‖z‖) := by
  obtain ⟨δ,hδ,hlower⟩ := polynomial_norm_lower P hP
  obtain ⟨K,hK,houtside⟩ := mem_cocompact.mp hlower
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  let D := |M|+C/δ+1
  have hdiv : 0 < C/δ := div_pos hC hδ
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,fun z => ?_⟩
  by_cases hz : z ∈ K
  · have hgM := hM z hz
    have he1 : 1 ≤ Real.exp (‖z‖*Real.sqrt ‖z‖) := Real.one_le_exp (by positivity)
    have hMD : M ≤ D := by dsimp [D]; linarith [le_abs_self M]
    exact hgM.trans (hMD.trans (le_mul_of_one_le_right hD.le he1))
  · have hnorm := hb z
    rw [he z,norm_mul] at hnorm
    have hl := houtside hz
    have hmul := mul_le_mul_of_nonneg_right hl (norm_nonneg (g z))
    have hbound : ‖g z‖ ≤ (C/δ)*Real.exp (‖z‖*Real.sqrt ‖z‖) := by
      calc
        _ ≤ (C*Real.exp (‖z‖*Real.sqrt ‖z‖))/δ :=
          (le_div_iff₀ hδ).mpr (by nlinarith)
        _ = _ := by ring
    exact hbound.trans (mul_le_mul_of_nonneg_right
      (by dsimp [D]; linarith [abs_nonneg M]) (Real.exp_pos _).le)

theorem finite_zero_exponential_polynomial (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (hfinite : {z : ℂ | f z = 0}.Finite)
    (C : ℝ) (hC : 0 < C) (hb : ∀ z, ‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖)) :
    ∃ (P : ℂ[X]) (a : ℂ), P ≠ 0 ∧ ∀ z, f z = P.eval z*Complex.exp (a*z) := by
  obtain ⟨P,g,hP,hg,hgn,he⟩ := finite_zero_polynomial_factor f hf h0 hfinite
  obtain ⟨D,hD,hgrowth⟩ := polynomial_factor_growth f g P hP hg.continuous he C hC hb
  obtain ⟨a,ha⟩ := zero_free_exponential_affine g hg hgn D hD hgrowth
  refine ⟨Polynomial.C (g 0)*P,a,mul_ne_zero (by simpa using hgn 0) hP,fun z => ?_⟩
  rw [he z,ha z,Polynomial.eval_mul,Polynomial.eval_C]
  ring

theorem exponential_polynomial_not_real_decay (P : ℂ[X]) (hP : P ≠ 0) (a : ℂ) :
    ¬ Tendsto (fun x : ℝ => P.eval (x : ℂ)*Complex.exp (a*(x : ℂ)))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨δ,hδ,hlower⟩ := polynomial_norm_lower P hP
  let s : ℝ := if 0 ≤ a.re then 1 else -1
  have hs : |s| = 1 := by dsimp [s]; split <;> norm_num
  have hsign : 0 ≤ a.re*s := by dsimp [s]; split <;> rename_i h <;> simp <;> linarith
  have haxis : Tendsto (fun x : ℝ => ((s*x : ℝ) : ℂ)) atTop (cocompact ℂ) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ)
    simpa only [dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_mul,hs,one_mul]
      using tendsto_abs_atTop_atTop
  have hreal : Tendsto (fun x : ℝ => s*x) atTop (cocompact ℝ) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℝ)
    simpa only [Real.dist_eq,sub_zero,abs_mul,hs,one_mul] using tendsto_abs_atTop_atTop
  intro hdecay
  have hsmall : Tendsto (fun x : ℝ => ‖P.eval ((s*x : ℝ) : ℂ)*
      Complex.exp (a*((s*x : ℝ) : ℂ))‖) atTop (𝓝 0) := by
    have h := (hdecay.comp hreal).norm
    change Tendsto (fun x : ℝ => ‖P.eval ((s*x : ℝ) : ℂ)*
      Complex.exp (a*((s*x : ℝ) : ℂ))‖) atTop (𝓝 ‖(0 : ℂ)‖) at h
    simpa only [norm_zero] using h
  obtain ⟨x,hx,hu,hl⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    ((hsmall.eventually (gt_mem_nhds hδ)).and (haxis.eventually hlower))).exists
  have he : 1 ≤ ‖Complex.exp (a*((s*x : ℝ) : ℂ))‖ := by
    rw [Complex.norm_exp,Real.one_le_exp_iff]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    nlinarith [mul_nonneg hsign hx]
  have hlarge : δ ≤ ‖P.eval ((s*x : ℝ) : ℂ)*Complex.exp (a*((s*x : ℝ) : ℂ))‖ := by
    rw [norm_mul]
    exact hl.trans (le_mul_of_one_le_right (norm_nonneg _) he)
  exact (not_lt_of_ge hlarge) hu

theorem infinite_zeros_of_subquadratic_real_decay (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ z, ‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖))
    (hdecay : Tendsto (fun x : ℝ => f (x : ℂ)) (cocompact ℝ) (𝓝 0)) :
    {z : ℂ | f z = 0}.Infinite := by
  change ¬ {z : ℂ | f z = 0}.Finite
  intro hfinite
  obtain ⟨P,a,hP,he⟩ := finite_zero_exponential_polynomial f hf h0 hfinite C hC hb
  exact exponential_polynomial_not_real_decay P hP a (by simpa only [he] using hdecay)

end OperatorDerivativeRewrite.Foundation.SubquadraticFiniteZeroFactorization
