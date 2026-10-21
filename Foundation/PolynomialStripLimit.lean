import Foundation.SymmetricPolynomialHeatLimit
import Foundation.RealRootedVerticalLimit

/-! Root-strip closure for nonzero entire polynomial limits and actual heat.
Full complex root multisets give one-sided vertical modulus bounds. An existing
analytic identity theorem excludes a zero beyond the strip for a nonzero entire
pointwise limit. The verified symmetric-shift limit then gives global finite
polynomial heat strip contraction, including repeated roots and collisions. -/
noncomputable section
open Polynomial Complex Multiset Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PolynomialStripLimit

theorem linear_factor_upper_bound (x a b : ℝ) (r : ℂ)
    (hr : r.im≤a) (hab : a≤b) :
    ‖((x:ℂ)+I*a)-r‖≤‖((x:ℂ)+I*b)-r‖ := by
  have hs : (a-r.im)^2≤(b-r.im)^2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hr) (by linarith)).mpr (by linarith)
  apply Real.sqrt_le_sqrt
  simpa [Complex.normSq_apply,pow_two] using hs

theorem rootProduct_upper_bound (L : Multiset ℂ) (β x a b : ℝ)
    (hL : ∀ r∈L,r.im≤β) (hβ : β≤a) (hab : a≤b) :
    ‖SymmetricPolynomialStrip.rootProduct L ((x:ℂ)+I*a)‖≤
      ‖SymmetricPolynomialStrip.rootProduct L ((x:ℂ)+I*b)‖ := by
  induction L using Multiset.induction_on with
  | empty => simp [SymmetricPolynomialStrip.rootProduct]
  | cons r L ih =>
    simp only [SymmetricPolynomialStrip.rootProduct,Multiset.map_cons,Multiset.prod_cons,norm_mul]
    apply mul_le_mul (linear_factor_upper_bound x a b r
      ((hL r (Multiset.mem_cons_self r L)).trans hβ) hab)
      (ih (fun v hv => hL v (Multiset.mem_cons_of_mem hv))) (norm_nonneg _) (norm_nonneg _)

theorem polynomial_upper_bound (P : ℂ[X]) (β x a b : ℝ)
    (hP : ∀ r : ℂ,P.eval r=0 → r.im≤β) (hβ : β≤a) (hab : a≤b) :
    ‖P.eval ((x:ℂ)+I*a)‖≤‖P.eval ((x:ℂ)+I*b)‖ := by
  rw [SymmetricPolynomialStrip.polynomial_root_product,SymmetricPolynomialStrip.polynomial_root_product,
    norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_left
    (rootProduct_upper_bound P.roots β x a b (fun r hr => hP r (Polynomial.isRoot_of_mem_roots hr)) hβ hab)
    (norm_nonneg _)

theorem limit_upper_bound (P : ℕ → ℂ[X]) (f : ℂ → ℂ) (β x a b : ℝ)
    (hP : ∀ n : ℕ,∀ r : ℂ,(P n).eval r=0 → r.im≤β)
    (hlim : ∀ z : ℂ,Tendsto (fun n => (P n).eval z) atTop (𝓝 (f z)))
    (hβ : β≤a) (hab : a≤b) : ‖f ((x:ℂ)+I*a)‖≤‖f ((x:ℂ)+I*b)‖ := by
  apply le_of_tendsto_of_tendsto ((hlim _).norm) ((hlim _).norm)
  exact Eventually.of_forall (fun n => polynomial_upper_bound (P n) β x a b (hP n) hβ hab)

theorem zero_im_le_of_vertical_bound (f : ℂ → ℂ) (β : ℝ)
    (hf : Differentiable ℂ f) (hne : ∃ w : ℂ,f w≠0)
    (hvert : ∀ x a b : ℝ,β≤a → a≤b → ‖f ((x:ℂ)+I*a)‖≤‖f ((x:ℂ)+I*b)‖)
    (z : ℂ) (hz : f z=0) : z.im≤β := by
  by_contra hn
  have hgap : 0<z.im-β := by linarith
  let s : ℕ → ℂ := fun n => (z.re:ℂ)+I*Complex.ofReal (β+(z.im-β)/((n:ℝ)+1))
  let w : ℂ := (z.re:ℂ)+I*β
  have hs : Tendsto s atTop (𝓝 w) := by
    have h : Tendsto (fun n : ℕ => β+(z.im-β)/((n:ℝ)+1)) atTop (𝓝 β) := by
      have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (z.im-β)
      simpa only [mul_zero,add_zero,div_eq_mul_inv,one_mul] using ht.const_add β
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul hc)
  have hm : ∀ n : ℕ,s n∈{v : ℂ | f v=0} \ {w} := by
    intro n
    have hd : (1:ℝ)≤(n:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hlow : β≤β+(z.im-β)/((n:ℝ)+1) := by
      have hq := div_nonneg hgap.le (by linarith : (0:ℝ)≤(n:ℝ)+1)
      linarith
    have hupp : β+(z.im-β)/((n:ℝ)+1)≤z.im := by
      have hq := div_le_self hgap.le hd
      linarith
    have he : (z.re:ℂ)+I*z.im=z := by apply Complex.ext <;> simp
    have hv := hvert z.re (β+(z.im-β)/((n:ℝ)+1)) z.im hlow hupp
    rw [he,hz,norm_zero] at hv
    refine ⟨norm_eq_zero.mp (le_antisymm hv (norm_nonneg _)),?_⟩
    intro hmem
    have hh : s n=w := Set.mem_singleton_iff.mp hmem
    have him := congrArg Complex.im hh
    have hden : (n:ℝ)+1≠0 := by positivity
    have hq : (z.im-β)/((n:ℝ)+1)=0 := by
      have heq : β+(z.im-β)/((n:ℝ)+1)=β := by
        simpa only [s,w,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
          Complex.I_re,Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add] using him
      linarith
    exact (ne_of_gt hgap) ((div_eq_zero_iff.mp hq).resolve_right hden)
  have hclosure := mem_closure_of_tendsto hs (Eventually.of_forall hm)
  have ha : AnalyticOnNhd ℂ f univ := fun v _ => hf.analyticAt v
  have heq := ha.eqOn_zero_of_preconnected_of_mem_closure isPreconnected_univ (mem_univ w) hclosure
  obtain ⟨v,hv⟩ := hne
  exact hv (heq (mem_univ v))

theorem upper_zero_limit (P : ℕ → ℂ[X]) (f : ℂ → ℂ) (β : ℝ)
    (hf : Differentiable ℂ f) (hne : ∃ w : ℂ,f w≠0)
    (hP : ∀ n : ℕ,∀ r : ℂ,(P n).eval r=0 → r.im≤β)
    (hlim : ∀ z : ℂ,Tendsto (fun n => (P n).eval z) atTop (𝓝 (f z))) :
    ∀ z : ℂ,f z=0 → z.im≤β :=
  zero_im_le_of_vertical_bound f β hf hne (limit_upper_bound P f β · · · hP hlim)

theorem strip_zero_limit (P : ℕ → ℂ[X]) (f : ℂ → ℂ) (b : ℝ)
    (hf : Differentiable ℂ f) (hne : ∃ w : ℂ,f w≠0)
    (hP : ∀ n : ℕ,∀ r : ℂ,(P n).eval r=0 → |r.im|≤b)
    (hlim : ∀ z : ℂ,Tendsto (fun n => (P n).eval z) atTop (𝓝 (f z))) :
    ∀ z : ℂ,f z=0 → |z.im|≤b := by
  have hu := upper_zero_limit P f b hf hne
    (fun n r hr => (le_abs_self r.im).trans (hP n r hr)) hlim
  have hg : Differentiable ℂ (fun z : ℂ => f (-z)) := hf.comp (differentiable_id.neg)
  have hgn : ∃ w : ℂ,f (-w)≠0 := by
    obtain ⟨w,hw⟩ := hne
    exact ⟨-w,by simpa only [neg_neg] using hw⟩
  have hl := upper_zero_limit (fun n => (P n).comp (-X)) (fun z : ℂ => f (-z)) b hg hgn
    (by
      intro n a ha
      have ha0 : (P n).eval (-a)=0 := by simpa only [eval_comp,eval_neg,eval_X] using ha
      have hb : |a.im|≤b := by simpa only [Complex.neg_im,abs_neg] using hP n (-a) ha0
      exact (le_abs_self _).trans hb)
    (by
      intro a
      simpa only [eval_comp,eval_neg,eval_X] using hlim (-a))
  intro z hz
  have htop := hu z hz
  have hbot : -z.im≤b := by
    have he := hl (-z) (by simpa only [neg_neg] using hz)
    simpa only [Complex.neg_im] using he
  exact abs_le.mpr ⟨by linarith,htop⟩

open PureOrderPolynomialTransport in
theorem quadratic_transport_ne_zero (a : ℝ) (P : ℝ[X]) (hP : P≠0) :
    transport 2 a P≠0 := by
  have he := LinearMap.congr_fun (transport_add 2 (by norm_num) (-a) a) P
  change transport 2 (-a) (transport 2 a P)=transport 2 (-a+a) P at he
  rw [neg_add_cancel,transport_zero,LinearMap.id_apply] at he
  intro hz
  rw [hz,(transport 2 (-a)).map_zero] at he
  exact hP he.symm

open PureOrderPolynomialTransport in
theorem quadratic_heat_strip (P : ℝ[X]) (hP : P≠0) (s b : ℝ) (hs : 0≤s)
    (hstrip : ∀ a : ℂ,(P.map (algebraMap ℝ ℂ)).eval a=0 → a.im^2≤b^2)
    (z : ℂ) (hz : ((transport 2 (-s) P).map (algebraMap ℝ ℂ)).eval z=0) :
    z.im^2≤max (b^2-2*s) 0 := by
  rcases eq_or_lt_of_le hs with hzero|hpos
  · subst s
    have he : (P.map (algebraMap ℝ ℂ)).eval z=0 := by
      simpa only [neg_zero,transport_zero,LinearMap.id_apply] using hz
    simpa only [mul_zero,sub_zero,max_eq_left (sq_nonneg b)] using hstrip z he
  · let B : ℝ := max (b^2-2*s) 0
    have hB : 0≤B := le_max_right _ _
    let Q : ℂ[X] := (transport 2 (-s) P).map (algebraMap ℝ ℂ)
    have hQ : Q≠0 := (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr
      (quadratic_transport_ne_zero (-s) P hP)
    have hne : ∃ w : ℂ,Q.eval w≠0 := by
      by_contra hn
      push Not at hn
      apply hQ
      apply Polynomial.funext
      intro w
      simpa using hn w
    have hpmap : P.map (algebraMap ℝ ℂ)≠0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hP
    have hdata (n : ℕ) := SymmetricPolynomialStrip.scaledShift_properties
      (P.map (algebraMap ℝ ℂ)) hpmap (SymmetricPolynomialStrip.real_map_conj P) s b hpos hstrip n
    have hlim := SymmetricPolynomialHeatLimit.scaledShift_locally_uniform s hs P
    have he := strip_zero_limit
      (fun n => SymmetricPolynomialStrip.scaledShift s n (P.map (algebraMap ℝ ℂ)))
      (fun w => Q.eval w) (Real.sqrt B) Q.differentiable hne
      (fun n a ha => Real.abs_le_sqrt ((hdata n).2.2 a ha))
      (fun w => (tendstoLocallyUniformlyOn_univ.mpr hlim).tendsto_at (mem_univ w)) z hz
    have hsq := (sq_le_sq₀ (abs_nonneg z.im) (Real.sqrt_nonneg B)).mpr he
    simpa only [sq_abs,Real.sq_sqrt hB] using hsq

open PureOrderPolynomialTransport in
theorem quadratic_heat_real_roots (P : ℝ[X]) (hP : P≠0) (s b : ℝ) (hs : 0≤s)
    (hstrip : ∀ a : ℂ,(P.map (algebraMap ℝ ℂ)).eval a=0 → a.im^2≤b^2)
    (ht : b^2≤2*s) (z : ℂ)
    (hz : ((transport 2 (-s) P).map (algebraMap ℝ ℂ)).eval z=0) : z.im=0 := by
  have he := quadratic_heat_strip P hP s b hs hstrip z hz
  rw [max_eq_right (sub_nonpos.mpr ht)] at he
  nlinarith [sq_nonneg z.im]

end OperatorDerivativeRewrite.Foundation.PolynomialStripLimit
