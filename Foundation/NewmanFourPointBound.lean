import Foundation.RiemannEvenRealityClosed
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A four-point lower bound for positive log factors, complete polynomial root products and actual all-real Xi flows. Arithmetic reality remains an explicit hypothesis. -/
noncomputable section
open Real Polynomial Filter Set
namespace OperatorDerivativeRewrite.Foundation.NewmanFourPointBound

theorem log_quadratic_lower (w : ℝ) (hw : 0 ≤ w) :
    w-w^2/2 ≤ log (1+w) := by
  have hp : 0 < w+2 := by linarith
  have he : w-w^2/2 ≤ 2*w/(w+2) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [mul_nonneg (sq_nonneg w) hw]
  exact he.trans (Real.le_log_one_add_of_nonneg hw)

theorem log_gap_bound (c : ℝ) (hc : 0 ≤ c) :
    (c/(1+c))^2 ≤ 4*(2*log (1+c/2)-log (1+c)) := by
  have h1 : 0 < 1+c := by linarith
  have h2 : 0 < c+2 := by linarith
  have hh : 0 < 1+c/2 := by linarith
  have hr : 0 < (1+c/2)^2/(1+c) := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos hr
  have he : 1-((1+c/2)^2/(1+c))⁻¹ = (c/(c+2))^2 := by
    field_simp
    <;> ring
  rw [he,Real.log_div (by positivity) (ne_of_gt h1),Real.log_pow] at hl
  have hu : c/(1+c) ≤ 2*(c/(c+2)) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ h1 h2).mpr
    nlinarith [sq_nonneg c]
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ c/(1+c)) (by positivity)).mpr hu
  nlinarith

theorem log_factor_four_point (c y : ℝ) (hc : 0 ≤ c) (hy : 1 ≤ y) :
    log (1+c) + (y-1)*(log (1+2*c)-log (1+c)) -
      2*(y-1)^2*(2*log (1+c/2)-log (1+c)) ≤ log (1+c*y) := by
  let u : ℝ := c/(1+c)
  let v : ℝ := y-1
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := sub_nonneg.mpr hy
  have hc1 : 1+c ≠ 0 := ne_of_gt (by linarith : 0 < 1+c)
  have hfact : 1+c*y = (1+c)*(1+u*v) := by dsimp [u,v]; field_simp; ring
  have hstep : 1+2*c = (1+c)*(1+u) := by dsimp [u]; field_simp; ring
  have hlog : log (1+2*c)-log (1+c) = log (1+u) := by
    rw [hstep, Real.log_mul hc1 (by positivity)]
    ring
  have hsmall : log (1+u) ≤ u := by
    simpa only [add_sub_cancel_left] using Real.log_le_sub_one_of_pos (by positivity : 0 < 1+u)
  have hlower := log_quadratic_lower (u*v) (mul_nonneg hu hv)
  have hgap := log_gap_bound c hc
  change u^2 ≤ 4*(2*log (1+c/2)-log (1+c)) at hgap
  have hslope := mul_le_mul_of_nonneg_left hsmall hv
  have hcurve := mul_le_mul_of_nonneg_right hgap (sq_nonneg v)
  rw [hfact, Real.log_mul hc1 (by positivity), hlog]
  change log (1+c)+v*log (1+u)-2*v^2*(2*log (1+c/2)-log (1+c)) ≤ _
  rw [mul_pow] at hlower
  nlinarith

theorem finite_log_profile_four_point (L : Multiset ℝ)
    (hL : ∀ c ∈ L, 0 ≤ c) (A B alpha y : ℝ) (ha : 0 ≤ alpha) (hy : 1 ≤ y) :
    let q : ℝ → ℝ := fun v => A-B*v+alpha*(L.map (fun c => log (1+c*v))).sum
    q 1+(y-1)*(q 2-q 1)-2*(y-1)^2*(2*q (1/2)-q 0-q 1) ≤ q y := by
  induction L using Multiset.induction_on with
  | empty => simp only [Multiset.map_zero,Multiset.sum_zero,mul_zero,add_zero]; nlinarith
  | cons c L ih =>
    have hc := hL c (Multiset.mem_cons_self c L)
    have htail : ∀ d ∈ L, 0 ≤ d := fun d hd => hL d (Multiset.mem_cons_of_mem hd)
    have hi := ih htail
    have hf := mul_le_mul_of_nonneg_left (log_factor_four_point c y hc hy) ha
    simp only [Multiset.map_cons,Multiset.sum_cons]
    dsimp only at hi ⊢
    simp only [mul_one,mul_zero,add_zero,log_one,sub_zero] at hi hf ⊢
    rw [show 2*c=c*2 by ring, show c/2=c*(1/2) by ring] at hf
    linear_combination hi + hf

theorem imaginary_linear_log (a C y : ℝ) (ha : a ≠ 0) (hy : 0 ≤ y) :
    log ‖Complex.I*((C*sqrt y : ℝ):ℂ)-(a:ℂ)‖ =
      log |a| + log (1+(C/a)^2*y)/2 := by
  have hp : 0 < 1+(C/a)^2*y := by nlinarith [mul_nonneg (sq_nonneg (C/a)) hy]
  have he : a^2+(C*sqrt y)^2 = a^2*(1+(C/a)^2*y) := by
    rw [mul_pow,Real.sq_sqrt hy]
    field_simp
    <;> ring
  have hn : ‖Complex.I*((C*sqrt y : ℝ):ℂ)-(a:ℂ)‖ =
      |a| * sqrt (1+(C/a)^2*y) := by
    rw [Complex.norm_def]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,sub_zero,
      Complex.sub_im,Complex.mul_im,mul_zero,zero_sub]
    simp only [zero_add,← pow_two,neg_sq]
    rw [he,Real.sqrt_mul (sq_nonneg a),Real.sqrt_sq_eq_abs]
  rw [hn,Real.log_mul (abs_ne_zero.mpr ha) (ne_of_gt (Real.sqrt_pos.mpr hp)),
    Real.log_sqrt hp.le]

theorem imaginary_factor_ne_zero (r : ℂ) (hr : r.re ≠ 0) (x : ℝ) :
    Complex.I*(x:ℂ)-r ≠ 0 := by
  intro he
  have hh := congrArg Complex.re he
  have hz : r.re = 0 := by
    simpa only [Complex.sub_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,sub_zero,
      Complex.zero_re,zero_sub,neg_eq_zero] using hh
  exact hr hz

theorem imaginary_rootProduct_ne_zero (L : Multiset ℂ)
    (hL : ∀ r ∈ L, r.re ≠ 0) (x : ℝ) :
    SymmetricPolynomialStrip.rootProduct L (Complex.I*(x:ℂ)) ≠ 0 := by
  induction L using Multiset.induction_on with
  | empty => simp [SymmetricPolynomialStrip.rootProduct]
  | cons r L ih =>
    simp only [SymmetricPolynomialStrip.rootProduct,Multiset.map_cons,Multiset.prod_cons]
    exact mul_ne_zero (imaginary_factor_ne_zero r (hL r (Multiset.mem_cons_self r L)) x)
      (ih (fun a ha => hL a (Multiset.mem_cons_of_mem ha)))

theorem rootProduct_log_profile (L : Multiset ℂ)
    (hL : ∀ r ∈ L, r.im = 0 ∧ r.re ≠ 0) (C y : ℝ) (hy : 0 ≤ y) :
    log ‖SymmetricPolynomialStrip.rootProduct L (Complex.I*((C*sqrt y:ℝ):ℂ))‖ =
      (L.map (fun r => log |r.re|)).sum +
        (1/2:ℝ)*(L.map (fun r => log (1+(C/r.re)^2*y))).sum := by
  induction L using Multiset.induction_on with
  | empty => simp [SymmetricPolynomialStrip.rootProduct]
  | cons r L ih =>
    have hr := hL r (Multiset.mem_cons_self r L)
    have htail : ∀ a ∈ L, a.im = 0 ∧ a.re ≠ 0 :=
      fun a ha => hL a (Multiset.mem_cons_of_mem ha)
    have he : r = (r.re:ℂ) := Complex.ext rfl (by simpa using hr.1)
    have hn := imaginary_factor_ne_zero r hr.2 (C*sqrt y)
    have ht := imaginary_rootProduct_ne_zero L (fun a ha => (htail a ha).2) (C*sqrt y)
    have hf : log ‖Complex.I*((C*sqrt y:ℝ):ℂ)-r‖ =
        log |r.re|+log (1+(C/r.re)^2*y)/2 := by
      nth_rw 1 [he]
      exact imaginary_linear_log r.re C y hr.2 hy
    rw [show SymmetricPolynomialStrip.rootProduct (r ::ₘ L) (Complex.I*((C*sqrt y:ℝ):ℂ)) =
      (Complex.I*((C*sqrt y:ℝ):ℂ)-r)*SymmetricPolynomialStrip.rootProduct L
        (Complex.I*((C*sqrt y:ℝ):ℂ)) by simp [SymmetricPolynomialStrip.rootProduct],
      norm_mul,Real.log_mul (norm_ne_zero_iff.mpr hn) (norm_ne_zero_iff.mpr ht),hf,ih htail]
    simp only [Multiset.map_cons,Multiset.sum_cons]
    ring

theorem polynomial_log_profile (P : ℂ[X]) (h0 : P.eval 0 ≠ 0)
    (hreal : ∀ r : ℂ, P.eval r = 0 → r.im = 0) (C : ℝ) :
    ∃ A : ℝ, ∃ L : Multiset ℝ, (∀ c ∈ L, 0 ≤ c) ∧
      ∀ y : ℝ, 0 ≤ y → log ‖P.eval (Complex.I*((C*sqrt y:ℝ):ℂ))‖ =
        A+(1/2:ℝ)*(L.map (fun c => log (1+c*y))).sum := by
  have hp : P ≠ 0 := by intro h; apply h0; simp [h]
  have hr (r : ℂ) (hh : r ∈ P.roots) : r.im = 0 ∧ r.re ≠ 0 := by
    have hz : P.eval r = 0 := Polynomial.isRoot_of_mem_roots hh
    have hi := hreal r hz
    refine ⟨hi,?_⟩
    intro he
    have heq : r = 0 := Complex.ext (by simpa using he) (by simpa using hi)
    exact h0 (by simpa only [heq] using hz)
  refine ⟨log ‖P.leadingCoeff‖+(P.roots.map (fun r => log |r.re|)).sum,
    P.roots.map (fun r => (C/r.re)^2), ?_, ?_⟩
  · intro c hc
    obtain ⟨r,hr,he⟩ := Multiset.mem_map.mp hc
    rw [← he]
    exact sq_nonneg _
  · intro y hy
    rw [SymmetricPolynomialStrip.polynomial_root_product,norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))
        (norm_ne_zero_iff.mpr (imaginary_rootProduct_ne_zero P.roots
          (fun r hh => (hr r hh).2) (C*sqrt y))),
      rootProduct_log_profile P.roots hr C y hy]
    simp only [Multiset.map_map,Function.comp_def]
    ring

theorem polynomial_four_point (P : ℂ[X]) (h0 : P.eval 0 ≠ 0)
    (hreal : ∀ r : ℂ, P.eval r = 0 → r.im = 0) (A B C y : ℝ) (hy : 1 ≤ y) :
    let q : ℝ → ℝ := fun v => A-B*v+log ‖P.eval (Complex.I*((C*sqrt v:ℝ):ℂ))‖
    q 1+(y-1)*(q 2-q 1)-2*(y-1)^2*(2*q (1/2)-q 0-q 1) ≤ q y := by
  obtain ⟨D,L,hL,hprofile⟩ := polynomial_log_profile P h0 hreal C
  have he := finite_log_profile_four_point L hL (A+D) B (1/2) y (by norm_num) hy
  dsimp only at he ⊢
  rw [hprofile 1 (by norm_num),hprofile 2 (by norm_num),hprofile (1/2) (by norm_num),
    hprofile 0 le_rfl,hprofile y (by linarith)]
  linear_combination he

theorem actual_flow_four_point (m : ℕ) (t : ℝ)
    (hreal : ∀ z : ℂ, RiemannEvenFlow.flow m t z = 0 → z.im = 0)
    (A B C y : ℝ) (hy : 1 ≤ y) :
    let q : ℝ → ℝ := fun v => A-B*v+
      log ‖RiemannEvenFlow.flow m t (Complex.I*((C*sqrt v:ℝ):ℂ))‖
    q 1+(y-1)*(q 2-q 1)-2*(y-1)^2*(2*q (1/2)-q 0-q 1) ≤ q y := by
  let f : ℂ → ℂ := RiemannEvenFlow.flow m t
  have h0 : f 0 ≠ 0 :=
    ne_of_apply_ne Complex.re (ne_of_gt (RiemannEvenNormalizedCompact.actual_flow_zero_pos m t))
  obtain ⟨r,P,hr,hrb,hzeros,hP0,heven,hlim⟩ :=
    EvenEntirePolynomialApproximation.exists_real_polynomial_approximation f
      ((RiemannEvenFlow.flow_differentiable m t).differentiableOn.analyticOnNhd isOpen_univ)
      h0 (RiemannEvenEvolution.flow_even m t)
      (RiemannEvenEntireGrowth.exists_subquadratic_growth m t) (RiemannEvenWindowZeros.flow_conj m t)
  let Q : ℕ → ℂ[X] := fun n => (P n).map (algebraMap ℝ ℂ)
  have hQ0 (n : ℕ) : (Q n).eval 0 ≠ 0 := by rw [show (Q n).eval 0=f 0 from hP0 n]; exact h0
  have hQreal (n : ℕ) (z : ℂ) (hz : (Q n).eval z = 0) : z.im = 0 :=
    hreal z ((hzeros n z).mp hz).2
  have hfn (x : ℝ) : f (Complex.I*(x:ℂ)) ≠ 0 := by
    intro hz
    have hi := hreal (Complex.I*(x:ℂ)) hz
    have hx : x = 0 := by simpa only [Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add] using hi
    apply h0
    simpa only [hx,Complex.ofReal_zero,mul_zero] using hz
  let qn : ℕ → ℝ → ℝ := fun n v => A-B*v+log ‖(Q n).eval (Complex.I*((C*sqrt v:ℝ):ℂ))‖
  let q : ℝ → ℝ := fun v => A-B*v+log ‖f (Complex.I*((C*sqrt v:ℝ):ℂ))‖
  have hq (v : ℝ) : Tendsto (fun n => qn n v) atTop (nhds (q v)) := by
    have hp := (tendstoLocallyUniformlyOn_univ.mpr hlim).tendsto_at
      (mem_univ (Complex.I*((C*sqrt v:ℝ):ℂ)))
    have hl := (Real.continuousAt_log (norm_ne_zero_iff.mpr (hfn (C*sqrt v)))).tendsto.comp hp.norm
    exact tendsto_const_nhds.add hl
  have hleft := ((hq 1).add (((hq 2).sub (hq 1)).const_mul (y-1))).sub
    (((((hq (1/2)).const_mul 2).sub (hq 0)).sub (hq 1)).const_mul (2*(y-1)^2))
  apply le_of_tendsto_of_tendsto hleft (hq y)
  exact Eventually.of_forall (fun n => polynomial_four_point (Q n) (hQ0 n) (hQreal n) A B C y hy)

end OperatorDerivativeRewrite.Foundation.NewmanFourPointBound
