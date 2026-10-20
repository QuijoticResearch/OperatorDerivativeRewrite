import Foundation.RiemannQuarticTransitionCosinePhase
import Foundation.RiemannQuarticLocalCosineZeros
/-! Exact reality and simplicity from buffered actual cosine disks.
Local holomorphy, conjugacy and quantitative phase control are all explicit. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionSimpleZeros

private theorem exp_two_le_nine : Real.exp (2 : ℝ) ≤ 9 := by
  calc
    _ = Real.exp (1 : ℝ)^2 := by simpa using Real.exp_nat_mul (1 : ℝ) 2
    _ ≤ 3^2 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 2
    _ = _ := by norm_num

private theorem cosh_le_nine (y : ℝ) (hy : |y| ≤ 2) : Real.cosh y ≤ 9 := by
  have h1 := (Real.exp_le_exp.mpr (abs_le.mp hy).2).trans exp_two_le_nine
  have h2 := (Real.exp_le_exp.mpr (by linarith [(abs_le.mp hy).1] : -y ≤ 2)).trans exp_two_le_nine
  rw [Real.cosh_eq]
  linarith

private theorem cos_lipschitz_two (a : ℝ) (u v : ℂ)
    (hu : u ∈ closedBall (a : ℂ) 2) (hv : v ∈ closedBall (a : ℂ) 2) :
    ‖Complex.cos v-Complex.cos u‖ ≤ 9*‖v-u‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le (fun y _ => Complex.differentiableAt_cos) ?_
    (convex_closedBall (a : ℂ) 2) hu hv
  intro y hy
  have hn : ‖y-(a : ℂ)‖ ≤ 2 := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have him := (Complex.abs_im_le_norm (y-(a : ℂ))).trans hn
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at him
  rw [Complex.deriv_cos,norm_neg]
  exact (RiemannQuarticCosineLocalZeros.norm_sin_le_exp_abs_im y).trans
    ((Real.exp_le_exp.mpr him).trans exp_two_le_nine)

theorem phase_im_lower_bound (x r s D : ℝ) (Φ : ℂ → ℂ)
    (hs : 0 < s) (hhalf : D ≤ s/2)
    (hconj : ∀ z : ℂ, Φ (conj z)=conj (Φ z))
    (ha : ∀ z : ℂ, ‖z-(x : ℂ)‖ < r → AnalyticAt ℂ Φ z)
    (hderiv : ∀ z : ℂ, ‖z-(x : ℂ)‖ < r → ‖deriv Φ z-(s : ℂ)‖ ≤ D)
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) : s*|z.im| ≤ 2*|(Φ z).im| := by
  let ρ := (r+‖z-(x : ℂ)‖)/2
  have hρ : ρ < r := by dsimp [ρ]; linarith
  have hzρ : ‖z-(x : ℂ)‖ ≤ ρ := by dsimp [ρ]; linarith
  have hnear (y : ℂ) (hy : y ∈ closedBall (x : ℂ) ρ) : ‖y-(x : ℂ)‖ < r :=
    (show ‖y-(x : ℂ)‖ ≤ ρ by simpa only [mem_closedBall,dist_eq_norm] using hy).trans_lt hρ
  have hd : ∀ y ∈ closedBall (x : ℂ) ρ, DifferentiableAt ℂ Φ y :=
    fun y hy => (ha y (hnear y hy)).differentiableAt
  have hb : ∀ y ∈ closedBall (x : ℂ) ρ, ‖deriv Φ y-(s : ℂ)‖ ≤ ‖(s : ℂ)‖/2 := by
    intro y hy
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
    exact (hderiv y (hnear y hy)).trans hhalf
  have hzc : ‖conj z-(x : ℂ)‖=‖z-(x : ℂ)‖ := by
    have he : conj z-(x : ℂ)=conj (z-(x : ℂ)) := by simp
    rw [he,norm_conj]
  have h := RiemannQuarticFrequencyBranch.scalar_ball_lower_bound Φ (x : ℂ) (s : ℂ) ρ hd hb z (conj z)
    (by simpa only [mem_closedBall,dist_eq_norm] using hzρ)
    (by simpa only [mem_closedBall,dist_eq_norm,hzc] using hzρ)
  have hn (q : ℂ) : ‖q-conj q‖=2*|q.im| := by
    have he : q-conj q=(2*(q.im : ℂ))*Complex.I := by
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
    rw [he,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  rw [hconj,hn,hn,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs] at h
  nlinarith

theorem local_real_simple_zero_of_differentiable (g : ℂ → ℂ)
    (hg : Differentiable ℂ g) (hgconj : ∀ z : ℂ, g (conj z)=conj (g z))
    (x r s D : ℝ) (E Φ : ℂ → ℂ)
    (hs : 0 < s) (hr : 0 < r) (hD : 0 ≤ D)
    (hscaled : D/s ≤ 1/1000000) (hbuffer : 1/s ≤ r/2)
    (hglobal : ∀ z : ℂ, E z ≠ 0 ∧ E (conj z)=conj (E z) ∧ Φ (conj z)=conj (Φ z))
    (hlocal : ∀ z : ℂ, ‖z-(x : ℂ)‖ < r → AnalyticAt ℂ E z ∧ AnalyticAt ℂ Φ z ∧
      ‖deriv Φ z-(s : ℂ)‖ ≤ D ∧
      ‖g z/E z-Complex.cos (Φ z)‖ ≤ (1/1000000)*Real.cosh (Φ z).im)
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r/2) (hzero : g z=0) :
    z.im=0 ∧ deriv (g) z ≠ 0 := by
  have herror := fun y hy => (hlocal y hy).2.2.2
  have hEa := fun y hy => (hlocal y hy).1
  have hΦa := fun y hy => (hlocal y hy).2.1
  have hΦd := fun y hy => (hlocal y hy).2.2.1
  have hhalf : D ≤ s/2 := by
    have hh := (div_le_iff₀ hs).mp hscaled
    nlinarith
  let p := z.re
  let a := (Φ (p : ℂ)).re
  let L := fun q : ℂ => (p : ℂ)+(q-(a : ℂ))/(s : ℂ)
  let F := fun y : ℂ => g y/E y
  let f := fun q : ℂ => F (L q)
  let q₀ := (a : ℂ)+(s : ℂ)*(z-(p : ℂ))
  have hspos : 0 < s := hs
  have hsn : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspos.ne'
  have hpcenter : ‖(p : ℂ)-(x : ℂ)‖ < r/2 := by
    have h := (Complex.abs_re_le_norm (z-(x : ℂ))).trans_lt hz
    simpa only [Complex.sub_re,Complex.ofReal_re,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h
  have hinside (y : ℂ) (hy : y ∈ closedBall (p : ℂ) (1/s)) : ‖y-(x : ℂ)‖ < r := by
    have hy' : ‖y-(p : ℂ)‖ ≤ 1/s := by simpa only [mem_closedBall,dist_eq_norm] using hy
    have h := norm_add_le (y-(p : ℂ)) ((p : ℂ)-(x : ℂ))
    rw [sub_add_sub_cancel] at h
    linarith
  have hLmem (q : ℂ) (hq : q ∈ closedBall (a : ℂ) 1) : L q ∈ closedBall (p : ℂ) (1/s) := by
    have hq' : ‖q-(a : ℂ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hq
    rw [mem_closedBall,dist_eq_norm]
    dsimp [L]
    rw [add_sub_cancel_left,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hspos]
    exact div_le_div_of_nonneg_right hq' hspos.le
  have hphasep : Φ (p : ℂ)=(a : ℂ) := by
    apply Complex.ext
    · rfl
    · have hc := (hglobal (p : ℂ)).2.2
      simp only [Complex.conj_ofReal] at hc
      have hh := congrArg Complex.im hc
      simp only [Complex.conj_im] at hh
      dsimp [a]
      linarith
  have hlinear (q : ℂ) (hq : q ∈ closedBall (a : ℂ) 1) : ‖Φ (L q)-q‖ ≤ 1/1000000 := by
    have hd : ∀ y ∈ closedBall (p : ℂ) (1/s),
        DifferentiableAt ℂ (fun y => Φ y-(s : ℂ)*y) y := by
      intro y hy
      exact (hΦa y (hinside y hy)).differentiableAt.sub
        ((hasDerivAt_id y).const_mul (s : ℂ)).differentiableAt
    have hb : ∀ y ∈ closedBall (p : ℂ) (1/s),
        ‖deriv (fun y => Φ y-(s : ℂ)*y) y‖ ≤ D := by
      intro y hy
      have hd' : HasDerivAt (fun u => Φ u-(s : ℂ)*u) (deriv Φ y-(s : ℂ)) y := by
        convert ((hΦa y
          (hinside y hy)).differentiableAt.hasDerivAt).sub ((hasDerivAt_id y).const_mul (s : ℂ)) using 1
        · funext u; rfl
        · simp only [mul_one]
      rw [hd'.deriv]
      exact hΦd y (hinside y hy)
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_closedBall (p : ℂ) (1/s))
      (mem_closedBall_self (by positivity)) (hLmem q hq)
    have hid : Φ (L q)-(s : ℂ)*L q-(Φ (p : ℂ)-(s : ℂ)*(p : ℂ))=Φ (L q)-q := by
      rw [hphasep]
      dsimp [L]
      field_simp [hsn] <;> ring
    rw [hid] at h
    have hm := mul_le_mul_of_nonneg_left (show ‖L q-(p : ℂ)‖ ≤ 1/s by
      simpa only [mem_closedBall,dist_eq_norm] using hLmem q hq) (by positivity : 0 ≤ D)
    have hbound : D*(1/s) ≤ 1/1000000 := by simpa only [mul_one_div] using hscaled
    exact h.trans (hm.trans hbound)
  have hf : ∀ q ∈ closedBall (a : ℂ) 1, DifferentiableAt ℂ f q := by
    intro q hq
    exact ((hg.analyticAt (L q)).div
      (hEa (L q) (hinside (L q) (hLmem q hq))) (hglobal (L q)).1).differentiableAt.comp q (by dsimp [L]; fun_prop)
  have hconj : ∀ q, f (conj q)=conj (f q) := by
    intro q
    have hLc : L (conj q)=conj (L q) := by
      simp only [L,map_add,map_div₀,map_sub,Complex.conj_ofReal]
    dsimp only [f]
    rw [hLc]
    dsimp [F]
    rw [hgconj,(hglobal (L q)).2.1,map_div₀]
  have hclose : ∀ q ∈ closedBall (a : ℂ) 1, ‖f q-Complex.cos q‖ ≤ 1/1000 := by
    intro q hq
    have hlin := hlinear q hq
    have hqnorm : ‖q-(a : ℂ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hq
    have hphi : Φ (L q) ∈ closedBall (a : ℂ) 2 := by
      have ht := norm_add_le (Φ (L q)-q) (q-(a : ℂ))
      rw [sub_add_sub_cancel] at ht
      rw [mem_closedBall,dist_eq_norm]
      linarith
    have him : |(Φ (L q)).im| ≤ 2 := by
      have h := (Complex.abs_im_le_norm (Φ (L q)-(a : ℂ))).trans
        (show ‖Φ (L q)-(a : ℂ)‖ ≤ 2 by simpa only [mem_closedBall,dist_eq_norm] using hphi)
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using h
    have hcos := cos_lipschitz_two a q (Φ (L q))
      (closedBall_subset_closedBall (by norm_num) hq) hphi
    have he := herror (L q) (hinside (L q) (hLmem q hq))
    have hcosh := cosh_le_nine (Φ (L q)).im him
    have htri := norm_add_le (F (L q)-Complex.cos (Φ (L q))) (Complex.cos (Φ (L q))-Complex.cos q)
    rw [sub_add_sub_cancel] at htri
    change ‖F (L q)-Complex.cos (Φ (L q))‖ ≤ _ at he
    change ‖F (L q)-Complex.cos q‖ ≤ _
    nlinarith
  have hLq : L q₀=z := by dsimp [L,q₀]; field_simp [hsn] <;> ring
  have hzeroF : f q₀=0 := by dsimp [f,F]; rw [hLq,hzero,zero_div]
  have hphasezero : |(Φ z).im| ≤ 2*(1/1000000) := by
    have he := herror z (by linarith)
    rw [hzero,zero_div,zero_sub,norm_neg] at he
    exact RiemannQuarticZeroStrip.small_cos_im (Φ z) (1/1000000) (by norm_num) (by norm_num) he
  have hgeom := phase_im_lower_bound x r s D Φ hs hhalf (fun q => (hglobal q).2.2) hΦa hΦd z (by linarith)
  have hqsmall : q₀ ∈ closedBall (a : ℂ) (1/1000) := by
    have hzre : z-(p : ℂ)=(z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [p]
    have hqn : ‖q₀-(a : ℂ)‖=s*|z.im| := by
      dsimp [q₀]
      rw [add_sub_cancel_left,norm_mul,hzre,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hspos,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    rw [mem_closedBall,dist_eq_norm]
    rw [hqn]
    change s*|z.im| ≤ _ at hgeom
    nlinarith
  have hlocal := RiemannQuarticLocalCosineZeros.real_simple_zero f a hf hconj hclose q₀ hqsmall hzeroF
  have himq : q₀.im=s*z.im := by simp [q₀,Complex.mul_im]
  have hzreal : z.im=0 := by
    rw [himq] at hlocal
    exact (mul_eq_zero.mp hlocal.1).resolve_left hspos.ne'
  refine ⟨hzreal,?_⟩
  intro hbad
  have hFn : HasDerivAt (g) 0 z := by
    simpa only [hbad] using (hg z).hasDerivAt
  have hEn : E z ≠ 0 := (hglobal z).1
  have hEd := (hEa z (by linarith)).differentiableAt.hasDerivAt
  have hF0 : HasDerivAt F 0 z := by
    convert hFn.div hEd hEn using 1 <;>
      simp only [hzero,zero_mul,mul_zero,sub_zero,zero_div]
  have hLd : HasDerivAt L (1/(s : ℂ)) q₀ := by
    exact (((hasDerivAt_id q₀).sub_const (a : ℂ)).div_const (s : ℂ)).const_add (p : ℂ)
  rw [← hLq] at hF0
  have hcomp := hF0.comp q₀ hLd
  have hfc : HasDerivAt f 0 q₀ := by
    convert hcomp using 1
    · funext y; rfl
    · simp only [zero_mul]
  exact hlocal.2 hfc.deriv

theorem local_real_simple_zero (t x r s D : ℝ) (E Φ : ℂ → ℂ)
    (hs : 0 < s) (hr : 0 < r) (hD : 0 ≤ D)
    (hscaled : D/s ≤ 1/1000000) (hbuffer : 1/s ≤ r/2)
    (hglobal : ∀ z : ℂ, E z ≠ 0 ∧ E (conj z)=conj (E z) ∧ Φ (conj z)=conj (Φ z))
    (hlocal : ∀ z : ℂ, ‖z-(x : ℂ)‖ < r → AnalyticAt ℂ E z ∧ AnalyticAt ℂ Φ z ∧
      ‖deriv Φ z-(s : ℂ)‖ ≤ D ∧
      ‖RiemannQuarticFlow.flow t z/E z-Complex.cos (Φ z)‖ ≤ (1/1000000)*Real.cosh (Φ z).im)
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r/2) (hzero : RiemannQuarticFlow.flow t z=0) :
    z.im=0 ∧ deriv (RiemannQuarticFlow.flow t) z ≠ 0 := by
  exact local_real_simple_zero_of_differentiable (RiemannQuarticFlow.flow t)
    (RiemannQuarticFlow.flow_differentiable t) (RiemannQuarticNormalizedAnalytic.flow_conj t)
    x r s D E Φ hs hr hD hscaled hbuffer hglobal hlocal z hz hzero

theorem bounded_ratio_real_simple_zeros (M : ℝ) (hM : 0 ≤ M) :
    ∀ R : ℝ, 0 ≤ R → ∀ᶠ t : ℝ in atTop, ∃ u : ℝ,
      R ≤ u ∧ 65536*(M+7) ≤ u ∧ RiemannQuarticSaddleTimes.phaseSlope t u=0 ∧
      ∀ z : ℂ, ‖z‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u →
        RiemannQuarticFlow.flow t z=0 → z.im=0 ∧ deriv (RiemannQuarticFlow.flow t) z ≠ 0 := by
  let A := 2*RiemannQuarticTransitionReflection.reflectionCutoff (128*(M+8))
  let r := 1/(128*(M+8))
  have hA : 0 < A := by
    have h := RiemannQuarticTransitionReflection.reflectionCutoff_pos (128*(M+8)) (by positivity)
    dsimp [A]
    linarith
  have hr : 0 < r := by dsimp [r]; positivity
  intro R hR
  let L := max R (max (65536*(M+7)) (max (1000000*(M+8)) (max (4*A/r) (2/r))))
  have hL : 0 < L := by dsimp [L]; positivity
  filter_upwards [RiemannQuarticTransitionCosinePhase.eventually_actual_cosine_disks M (1/1000000) hM (by norm_num),
    RiemannQuarticTransitionReflection.eventually_actual_nonzero_lower M hM,
    RiemannQuarticRealSaddle.maxima_escape L hL.le] with t hcos hlow hescape
  obtain ⟨u,hu,hm⟩ := RiemannQuarticRealSaddle.exists_global_max t
  have hlarge : L ≤ u := (hescape u hu hm).le
  have hRu : R ≤ u := (le_max_left _ _).trans hlarge
  have huM : 65536*(M+7) ≤ u := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have huD : 1000000*(M+8) ≤ u :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have huTail : max (4*A/r) (2/r) ≤ u :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have huA : 4*A/r ≤ u := (le_max_left _ _).trans huTail
  have huB : 2/r ≤ u := (le_max_right _ _).trans huTail
  have hu0 : 0 < u := by linarith
  have hs := RiemannQuarticRealSaddle.max_real_stationary t u hu0 hm
  rw [← (RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv] at hs
  refine ⟨u,hRu,huM,hs,?_⟩
  intro z hz hzero
  have hlo : -A/u < z.im := lt_of_not_ge (fun h => hlow u huM hs z hz h hzero)
  have hconjzero : RiemannQuarticFlow.flow t (conj z)=0 := by
    rw [RiemannQuarticNormalizedAnalytic.flow_conj,hzero]
    simp
  have hhi : -A/u < (conj z).im := lt_of_not_ge (fun h =>
    hlow u huM hs (conj z) (by simpa using hz) h hconjzero)
  simp only [Complex.conj_im] at hhi
  rw [neg_div] at hlo hhi
  have hstrip : |z.im| < A/u := abs_lt.mpr ⟨hlo,by linarith⟩
  have hAr : A/u ≤ r/4 := by
    have hh := (div_le_iff₀ hr).mp huA
    apply (div_le_iff₀ hu0).mpr
    nlinarith
  have hinside : ‖z-(z.re : ℂ)‖ < r/2 := by
    have he : z-(z.re : ℂ)=(z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    exact hstrip.trans (lt_of_le_of_lt hAr (by linarith))
  have hx : |z.re| ≤ M*RiemannQuarticTransitionSaddle.realScale u := (Complex.abs_re_le_norm z).trans hz
  obtain ⟨E,Φ,hglobal,hlocal⟩ := hcos u huM hs z.re hx
  have hscaled : (M+8)/u ≤ 1/1000000 := (div_le_iff₀ hu0).mpr (by linarith)
  have hbuffer : 1/u ≤ r/2 := by
    have hh := (div_le_iff₀ hr).mp huB
    apply (div_le_iff₀ hu0).mpr
    nlinarith
  exact local_real_simple_zero t z.re r u (M+8) E Φ hu0 hr (by linarith)
    hscaled hbuffer hglobal hlocal z hinside hzero

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionSimpleZeros
