import Foundation.RiemannQuarticCosineLocalZeros
import Foundation.RiemannQuarticZeroStrip
/-! Real and simple actual quartic-flow zeros in growing complex windows.
A conjugation/local-injectivity argument replaces general Rouche machinery.
No claim about the unrestricted frequency far field is made. -/
noncomputable section
open Set Metric Complex Filter
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticWindowZeros
open RiemannQuarticNormalizedAnalytic RiemannQuarticCosineNormalization RiemannQuarticCosineLocalZeros
open RiemannQuarticZeroStrip RiemannQuarticSaddleTimes RiemannQuarticSaddleBranch RiemannQuarticDomain

theorem power_window_margin (γ ν : ℝ) (hγν : γ < ν) (hν : 0 < ν) :
    ∀ᶠ Q : ℝ in atTop, Q^γ+1 ≤ Q^ν := by
  have hA : Tendsto (fun Q : ℝ => Q^(γ-ν)) atTop (nhds 0) := by
    rw [show γ-ν= -(ν-γ) by ring]
    exact tendsto_rpow_neg_atTop (sub_pos.mpr hγν)
  have hB := tendsto_rpow_neg_atTop hν
  filter_upwards [eventually_gt_atTop (0 : ℝ),hA.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2)),
    hB.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with Q hQ hA hB
  have he : Q^γ+1=Q^ν*(Q^(γ-ν)+Q^(-ν)) := by
    rw [mul_add,← Real.rpow_add hQ,← Real.rpow_add hQ]
    simp only [add_sub_cancel,add_neg_cancel,Real.rpow_zero]
  rw [he]
  have hpos : 0 < Q^ν := Real.rpow_pos_of_pos hQ ν
  nlinarith

theorem uniform_real_simple_window (γ : ℝ) (hγpos : 0 < γ) (hγ : γ < 2/3) :
    ∀ᶠ t : ℝ in atTop, ∀ (ht : 0 < t) (u : ℝ) (hu : 2 ≤ u),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → ∀ (hs : phaseSlope t u=0) (z : ℂ),
      ‖z‖ ≤ (t*u^3+1)^γ → RiemannQuarticFlow.flow t z=0 →
      z.im=0 ∧ deriv (RiemannQuarticFlow.flow t) z ≠ 0 := by
  let ν := (γ+2/3)/2
  have hν : 0 < ν := by dsimp [ν]; linarith
  have hγν : γ < ν := by dsimp [ν]; linarith
  have hνupper : ν < 2/3 := by dsimp [ν]; linarith
  let ε := 1/(1000*Real.cosh 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨U,hU⟩ := eventually_atTop.1 (power_window_margin γ ν hγν hν)
  filter_upwards [uniform_normalized_cosine ν hνupper ε hε,
    uniform_zero_strip γ hγ (1/1000) (by norm_num),eventually_ge_atTop U] with t hmodel hstrip htU
  intro ht u hu hm hs z hz hzero
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hun : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  have hu3 : 1 ≤ u^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sq_nonneg u)]
  have hQt : t ≤ t*u^3+1 := by nlinarith
  have hmargin := hU (t*u^3+1) (le_trans htU hQt)
  let y := (u : ℂ)*z
  let a := y.re
  let f := fun w : ℂ => normalizedFlow t u (w/(u : ℂ))
  have hscale : Differentiable ℂ (fun w : ℂ => w/(u : ℂ)) := differentiable_id.div_const _
  have hf : Differentiable ℂ f := (normalized_differentiable t u ht.le hu1 hs).comp hscale
  have hconj : ∀ w, f (conj w)=conj (f w) := by
    intro w
    dsimp [f]
    have he : conj w/(u : ℂ)=conj (w/(u : ℂ)) := by simp only [map_div₀,Complex.conj_ofReal]
    rw [he,normalized_conj t u ht.le hu1 hs]
  have hstripz := hstrip ht u hu hm hs z hz hzero
  have hyim : |y.im| ≤ (1/1000 : ℝ) := by
    dsimp [y]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,abs_mul,abs_of_pos hu0]
    exact hstripz
  have hydist : ‖y-(a : ℂ)‖=|y.im| := by
    have he : y-(a : ℂ)=(y.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [a,Complex.mul_re,Complex.mul_im]
    rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hy : y ∈ closedBall (a : ℂ) (1/1000) := by simpa only [mem_closedBall,dist_eq_norm,hydist] using hyim
  have hscalezero : y/(u : ℂ)=z := by dsimp [y]; field_simp
  have hfzero : f y=0 := by dsimp [f]; rw [hscalezero]; simp only [normalizedFlow,hzero,zero_div]
  have hclose : ∀ w ∈ closedBall (a : ℂ) 1, ‖f w-Complex.cos w‖ ≤ 1/1000 := by
    intro w hw
    have hwDist : ‖w-(a : ℂ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have hwy : ‖w-y‖ ≤ 1+1/1000 := by
      have h := norm_sub_le (w-(a : ℂ)) (y-(a : ℂ))
      rw [sub_sub_sub_cancel_right] at h
      linarith
    have hquot : ‖w/(u : ℂ)-z‖ ≤ 1 := by
      have he : w/(u : ℂ)-z=(w-y)/(u : ℂ) := by dsimp [y]; field_simp
      rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu0]
      apply (div_le_iff₀ hu0).mpr
      linarith
    have hnorm : ‖w/(u : ℂ)‖ ≤ (t*u^3+1)^ν := by
      have hn := norm_sub_le (w/(u : ℂ)-z) (-z)
      simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at hn
      linarith
    have h := hmodel ht u hu hm hs (w/(u : ℂ)) hnorm
    have hmul : (u : ℂ)*(w/(u : ℂ))=w := by field_simp
    have him : u*(w/(u : ℂ)).im=w.im := by
      have hh := congrArg Complex.im hmul
      simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using hh
    rw [hmul,him] at h
    have hi := (Complex.abs_im_le_norm (w-(a : ℂ))).trans hwDist
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hi
    have hcosh : Real.cosh w.im ≤ Real.cosh 1 := Real.cosh_le_cosh.mpr (by simpa using hi)
    have hb := mul_le_mul_of_nonneg_left hcosh hε.le
    have he : ε*Real.cosh 1=1/1000 := by dsimp [ε]; field_simp
    change ‖f w-Complex.cos w‖ ≤ _ at h
    exact h.trans (by rw [← he]; exact hb)
  have hlocal := real_simple_zero f hf hconj a hclose y hy hfzero
  have him : y.im=u*z.im := by simp [y,Complex.mul_im]
  refine ⟨?_,?_⟩
  · rw [him] at hlocal
    exact (mul_eq_zero.mp hlocal.1).resolve_left hu0.ne'
  · intro hder
    have hn := envelope_ne_zero t u ht.le hu1 hs z
    have hN : HasDerivAt (normalizedFlow t u) 0 z := by
      have h := (RiemannQuarticFlow.flow_differentiable t z).hasDerivAt.div
        ((envelope_differentiable t u z).hasDerivAt) hn
      rw [hder,hzero] at h
      simp only [zero_mul,mul_zero,sub_zero,zero_div] at h
      convert h using 1
      rfl
    have hN' : HasDerivAt (normalizedFlow t u) 0 (y/(u : ℂ)) := by rw [hscalezero]; exact hN
    have hcomp := hN'.comp y ((hasDerivAt_id y).div_const (u : ℂ))
    have hfd : deriv f y=0 := by
      have hh := hcomp.deriv
      simp only [zero_mul] at hh
      convert hh using 1
      rfl
    exact hlocal.2 hfd

theorem eventually_real_simple_zeros (γ : ℝ) (hγpos : 0 < γ) (hγ : γ < 2/3) :
    ∀ᶠ t : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ t^γ → RiemannQuarticFlow.flow t z=0 →
      z.im=0 ∧ deriv (RiemannQuarticFlow.flow t) z ≠ 0 := by
  filter_upwards [uniform_real_simple_window γ hγpos hγ,
    RiemannQuarticRealSaddle.maxima_escape 2 (by norm_num),eventually_gt_atTop (0 : ℝ)] with t hwindow hescape ht
  intro z hz hzero
  obtain ⟨u,hu,hm⟩ := RiemannQuarticRealSaddle.exists_global_max t
  have hu2 : 2 ≤ u := (hescape u hu hm).le
  have hu0 : 0 < u := by linarith
  have hs : phaseSlope t u=0 := by
    have h := RiemannQuarticRealSaddle.max_real_stationary t u hu0 hm
    rw [← (RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv] at h
    exact h
  have hu1 : 1 ≤ u := by linarith
  have hu3 : 1 ≤ u^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sq_nonneg u)]
  have hQt : t ≤ t*u^3+1 := by nlinarith
  have hzQ := hz.trans (Real.rpow_le_rpow ht.le hQt hγpos.le)
  exact hwindow ht u hu2 hm hs z hzQ hzero

end OperatorDerivativeRewrite.Foundation.RiemannQuarticWindowZeros
