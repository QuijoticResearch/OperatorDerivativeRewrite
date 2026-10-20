import Foundation.RiemannSixthTransitionSaddle
import Foundation.RiemannQuarticComplexCorrection
/-! Actual sixth-order logarithmic correction on an exponential saddle scale.
All theta domains and actual derivative estimates remain explicit. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionCorrection
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenRealSaddle
open RiemannSixthTransitionSaddle RiemannThetaComplexKernel
open RiemannQuarticQuantitativeSaddle RiemannQuarticFarCorrection
open RiemannQuarticTransitionSaddle (realScale realScale_pos movingAnchor)

theorem scaled_neighbor_domain (t K : ℝ) (z w v : ℂ)
    (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 10000 ≤ w.re)
    (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
    (hy : z.im ≤ 1) (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hE : ‖Complex.exp (4*w)‖ ≤ K) (hv : ‖v-w‖ ≤ 2/K) :
    0 ≤ v.re ∧ 1 ≤ (Complex.exp (4*v)).re ∧
      t*w.re^5/32 ≤ (Complex.exp (4*v)).re := by
  have hn := neighbor_real_margin K hK w v hE hv
  have hm := hmargin
  have hQ : 1024 ≤ t*w.re^5 := by
    have hp : 1024 ≤ w.re^5 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) (by linarith : 4 ≤ w.re) 5
      norm_num at h
      exact h
    nlinarith
  have hR0 : 0 ≤ (Complex.exp (4*w)).re := by nlinarith [Real.pi_pos]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hR0
  have hd : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ (by linarith : 0 < K)).mpr (by linarith))
  have hc := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hc
  refine ⟨by linarith [(abs_le.mp hc).1], by nlinarith, by nlinarith⟩

theorem scaled_neighbor_error (t K : ℝ) (z w v : ℂ)
    (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 10000 ≤ w.re)
    (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
    (hy : z.im ≤ 1) (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hE : ‖Complex.exp (4*w)‖ ≤ K) (hv : ‖v-w‖ ≤ 2/K) :
    ‖complexSlope 3 t v-modelDerivative 3 t v‖ ≤ 30005*Real.exp (-w.re) := by
  have hdom := scaled_neighbor_domain t K z w v ht hK hr hmargin hi hy hs hE hv
  have hd : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ (by linarith : 0 < K)).mpr (by linarith))
  have hc := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hc
  have hlo := (abs_le.mp hc).1
  have hhi := (abs_le.mp hc).2
  have heq : complexSlope 3 t v-modelDerivative 3 t v=
      kernelDerivative v/kernelComplex v-(9-4*(Real.pi : ℂ)*Complex.exp (4*v)) := by
    rw [arithmetic_error_eq_quartic]
    unfold RiemannQuarticSaddleBranch.complexSlope RiemannQuarticSaddleTheta.modelDerivative
    rw [(kernelComplex_hasDerivAt v (by linarith [hdom.2.1])).deriv]
    ring
  rw [heq]
  apply (RiemannQuarticSaddleNeighborhood.logDerivative_coarse_bound v hdom.1 hdom.2.1).trans
  have hcub : 1024*w.re ≤ w.re^5 := by
    have hsq : 1024 ≤ w.re^4 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) (by linarith : 6 ≤ w.re) 4
      norm_num at h
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)]
  have htcub : w.re^5 ≤ t*w.re^5 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith [hdom.2.1] :
    0 ≤ (Complex.exp (4*v)).re)
  have h1 : Real.exp (-4*v.re) ≤ Real.exp (-w.re) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (4*v.re)*Real.exp (-3*Real.pi*(Complex.exp (4*v)).re) ≤ Real.exp (-w.re) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hdom.2.2]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 5),
    mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 30000)]

theorem scaled_neighbor_analytic (t K : ℝ) (z w : ℂ)
    (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 10000 ≤ w.re)
    (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
    (hy : z.im ≤ 1) (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hE : ‖Complex.exp (4*w)‖ ≤ K) :
    AnalyticOnNhd ℂ (complexSlope 3 t) (closedBall w (2/K)) := by
  intro v hv
  have hdom := scaled_neighbor_domain t K z w v ht hK hr hmargin hi hy hs hE
    (by simpa only [mem_closedBall, dist_eq_norm] using hv)
  have ha := kernelComplex_analyticAt v (by linarith [hdom.2.1])
  have hn := kernel_ne_zero v hdom.1 hdom.2.1
  exact (analyticAt_const.mul (analyticAt_id.pow 5)).add (ha.deriv.div ha hn)

theorem scaled_neighbor_deriv_error (t K : ℝ) (z w v : ℂ)
    (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 10000 ≤ w.re)
    (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
    (hy : z.im ≤ 1) (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hE : ‖Complex.exp (4*w)‖ ≤ K) (hv : v ∈ closedBall w (1/K)) :
    ‖deriv (complexSlope 3 t) v-deriv (modelDerivative 3 t) v‖ ≤
      (30005*Real.exp (-w.re))*K := by
  have hK0 : 0 < K := by linarith
  have hsub : closedBall v (1/K) ⊆ closedBall w (2/K) := by
    intro u hu
    have h := dist_triangle u v w
    have hu' := mem_closedBall.mp hu
    have hv' := mem_closedBall.mp hv
    apply mem_closedBall.mpr
    have htwo : 1/K+1/K=2/K := by ring
    linarith
  have ha := scaled_neighbor_analytic t K z w ht hK hr hmargin hi hy hs hE
  have hm : AnalyticOnNhd ℂ (modelDerivative 3 t) (closedBall w (2/K)) := by
    intro q _
    unfold modelDerivative
    fun_prop
  have hd := ((ha.sub hm).mono hsub).differentiableOn.diffContOnCl_ball (Subset.refl _)
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : (0 : ℝ) < 1/K) hd (fun q hq => scaled_neighbor_error t K z w q
      ht hK hr hmargin hi hy hs hE (by simpa only [mem_closedBall, dist_eq_norm] using
        (hsub (sphere_subset_closedBall hq))))
  have hvin : v ∈ closedBall w (2/K) := hsub (mem_closedBall_self (by positivity))
  rw [deriv_sub (ha v hvin).differentiableAt (modelDerivative_hasDerivAt 3 t v).differentiableAt] at h
  simpa only [one_div, div_inv_eq_mul] using h

theorem scaled_curvature_lower (t : ℝ) (z w : ℂ)
    (ht : 1 ≤ t) (hr : 10000 ≤ w.re)
    (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
    (hy : z.im ≤ 1) (hs : modelDerivative 3 t w= -(Complex.I*z)) :
    4*t*w.re^5 ≤ ‖-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)‖ := by
  have hm := hmargin
  have hre := Complex.re_le_norm (Complex.exp (4*w))
  have hp := mul_le_mul_of_nonneg_left hre (show 0 ≤ 16*Real.pi by positivity)
  simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  nlinarith

theorem scaled_model_deriv_bound (t K : ℝ) (w v : ℂ)
    (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 10000 ≤ w.re) (hn : ‖w‖ ≤ 2*w.re)
    (hE : ‖Complex.exp (4*w)‖ ≤ K) (hv : ‖v-w‖ ≤ 1/K) :
    ‖deriv (modelDerivative 3 t) v-(-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w))‖ ≤ t*w.re^5 := by
  have hK0 : 0 < K := by linarith
  have hv1 : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hK0).mpr (by linarith))
  have hnV : ‖v‖ ≤ 3*w.re := by
    have h := norm_add_le (v-w) w
    rw [sub_add_cancel] at h
    linarith
  have he := exp4_difference_bound w v (by
    have hh : 1/K ≤ 1/4 := (div_le_iff₀ hK0).mpr (by linarith)
    linarith)
  have hmul := mul_le_mul hE hv (norm_nonneg _) hK0.le
  have hcancel : K*(1/K)=1 := by field_simp
  have he8 : ‖Complex.exp (4*v)-Complex.exp (4*w)‖ ≤ 8 := by
    rw [hcancel] at hmul
    nlinarith
  have hid : deriv (modelDerivative 3 t) v-(-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w))=
      30*(t : ℂ)*v^4-16*(Real.pi : ℂ)*(Complex.exp (4*v)-Complex.exp (4*w)) := by
    rw [(modelDerivative_hasDerivAt 3 t v).deriv]
    ring
  rw [hid]
  have h := norm_sub_le (30*(t : ℂ)*v^4) (16*(Real.pi : ℂ)*(Complex.exp (4*v)-Complex.exp (4*w)))
  simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ t), abs_of_pos Real.pi_pos] at h
  have hpoly := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hnV 4)
    (show 0 ≤ 30*t by positivity)
  have hp := mul_nonneg (show 0 ≤ w.re-4860 by linarith) (show 0 ≤ t*w.re^4 by positivity)
  have hQ : 1024 ≤ t*w.re^5 := by
    have hh : 1024 ≤ w.re^5 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) (by linarith : 4 ≤ w.re) 5
      norm_num at h
      exact h
    nlinarith
  have hpi := mul_le_mul Real.pi_lt_four.le he8 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
  nlinarith

theorem scaled_actual_deriv_bound (t K : ℝ) (z w v : ℂ)
    (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 10000 ≤ w.re)
    (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
    (hn : ‖w‖ ≤ 2*w.re) (hy : z.im ≤ 1) (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hE : ‖Complex.exp (4*w)‖ ≤ K)
    (hsmall : (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4)
    (hv : v ∈ closedBall w (1/K)) :
    ‖deriv (complexSlope 3 t) v-(-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w))‖ ≤
      ‖-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)‖/2 := by
  have h1 := scaled_neighbor_deriv_error t K z w v ht hK hr hmargin hi hy hs hE hv
  have h2 := scaled_model_deriv_bound t K w v ht hK hr hn hE
    (by simpa only [mem_closedBall, dist_eq_norm] using hv)
  have h3 := norm_add_le (deriv (complexSlope 3 t) v-deriv (modelDerivative 3 t) v)
    (deriv (modelDerivative 3 t) v-(-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)))
  rw [sub_add_sub_cancel] at h3
  have hA := scaled_curvature_lower t z w ht hr hmargin hi hy hs
  have hQ : 0 ≤ t*w.re^5 := by positivity
  nlinarith

theorem scaled_actual_deriv_lower (t K : ℝ) (z w v : ℂ)
    (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 10000 ≤ w.re)
    (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
    (hn : ‖w‖ ≤ 2*w.re) (hy : z.im ≤ 1) (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hE : ‖Complex.exp (4*w)‖ ≤ K)
    (hsmall : (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4)
    (hv : v ∈ closedBall w (1/K)) :
    2*t*w.re^5 ≤ ‖deriv (complexSlope 3 t) v‖ := by
  have hb := scaled_actual_deriv_bound t K z w v ht hK hr hmargin hi hn hy hs hE hsmall hv
  have hnA := norm_sub_le
    (deriv (complexSlope 3 t) v-(-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)))
    (deriv (complexSlope 3 t) v)
  have heq : (deriv (complexSlope 3 t) v-(-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)))-
      deriv (complexSlope 3 t) v= -(-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)) := by ring
  rw [heq, norm_neg] at hnA
  have hA := scaled_curvature_lower t z w ht hr hmargin hi hy hs
  nlinarith

theorem scaled_actual_real_curvature (t K : ℝ) (z w v : ℂ)
    (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 10000 ≤ w.re)
    (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
    (hn : ‖w‖ ≤ 2*w.re) (hy : z.im ≤ 1) (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hE : ‖Complex.exp (4*w)‖ ≤ K)
    (hsmall : (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4)
    (hv : v ∈ closedBall w (1/K)) :
    (deriv (complexSlope 3 t) v).re ≤ -2*t*w.re^5 := by
  have h1 := scaled_neighbor_deriv_error t K z w v ht hK hr hmargin hi hy hs hE hv
  have h2 := scaled_model_deriv_bound t K w v ht hK hr hn hE
    (by simpa only [mem_closedBall, dist_eq_norm] using hv)
  let A : ℂ := -(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)
  have h3 := norm_add_le (deriv (complexSlope 3 t) v-deriv (modelDerivative 3 t) v)
    (deriv (modelDerivative 3 t) v-A)
  rw [sub_add_sub_cancel] at h3
  have hAr : A.re= -16*Real.pi*(Complex.exp (4*w)).re := by simp [A, Complex.mul_re]
  have hre := Complex.re_le_norm (deriv (complexSlope 3 t) v-A)
  rw [Complex.sub_re, hAr] at hre
  have hm := hmargin
  have hQ : 0 ≤ t*w.re^5 := by positivity
  nlinarith

theorem actual_scaled_frequency_disk (t K : ℝ) (z w q : ℂ)
    (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 10000 ≤ w.re)
    (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
    (hn : ‖w‖ ≤ 2*w.re) (hy : z.im ≤ 1) (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hE : ‖Complex.exp (4*w)‖ ≤ K)
    (hsmall : (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4)
    (hq : ‖q-z‖ ≤ t*w.re^5/K) :
    ∃! v, v ∈ closedBall w (1/K) ∧ complexSlope 3 t v= -(Complex.I*q) := by
  have hK0 : 0 < K := by linarith
  have hQ : 0 < t*w.re^5 := by positivity
  let A : ℂ := -(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)
  have hA : 4*t*w.re^5 ≤ ‖A‖ := scaled_curvature_lower t z w ht hr hmargin hi hy hs
  have hAn : A ≠ 0 := norm_pos_iff.mp (by linarith)
  have ha := scaled_neighbor_analytic t K z w ht hK hr hmargin hi hy hs hE
  have hsub : closedBall w (1/K) ⊆ closedBall w (2/K) :=
    closedBall_subset_closedBall (by apply (div_le_div_iff_of_pos_right hK0).mpr; norm_num)
  have hd : ∀ v ∈ closedBall w (1/K), DifferentiableAt ℂ (complexSlope 3 t) v :=
    fun v hv => (ha v (hsub hv)).differentiableAt
  have hb : ∀ v ∈ closedBall w (1/K), ‖deriv (complexSlope 3 t) v-A‖ ≤ ‖A‖/2 :=
    fun v hv => scaled_actual_deriv_bound t K z w v ht hK hr hmargin hi hn hy hs hE hsmall hv
  have hres := scaled_neighbor_error t K z w w ht hK hr hmargin hi hy hs hE (by simp; positivity)
  have htarget : -(Complex.I*q) ∈ closedBall (complexSlope 3 t w) (‖A‖*(1/K)/2) := by
    rw [mem_closedBall, dist_eq_norm]
    have hid : -(Complex.I*q)-complexSlope 3 t w=
        -(Complex.I*(q-z))-(complexSlope 3 t w-modelDerivative 3 t w) := by rw [hs]; ring
    rw [hid]
    have htri := norm_sub_le (-(Complex.I*(q-z))) (complexSlope 3 t w-modelDerivative 3 t w)
    simp only [norm_neg, norm_mul, Complex.norm_I, one_mul] at htri
    have hmul := mul_le_mul_of_nonneg_right htri hK0.le
    have hqK := (le_div_iff₀ hK0).mp hq
    have hresK := mul_le_mul_of_nonneg_right hres hK0.le
    have heq : ‖A‖*(1/K)/2=‖A‖/(2*K) := by ring
    rw [heq]
    apply (le_div_iff₀ (show 0 < 2*K by positivity)).mpr
    nlinarith
  obtain ⟨v,hv,hroot⟩ := scalar_ball_surj (complexSlope 3 t) w A (1/K)
    (by positivity) hAn hd hb htarget
  refine ⟨v, ⟨hv,hroot⟩, ?_⟩
  intro p hp
  exact scalar_ball_injective (complexSlope 3 t) w A (1/K) hAn hd hb hp.1 hv
    (hp.2.trans hroot.symm)

theorem transition_error_small (a M : ℝ) (hM : 0 ≤ M)
    (_ha : 1000 ≤ a) (haM : 50000*(M+8) ≤ a) :
    (30005*Real.exp (-a))*(M+8) ≤ 1/4096 := by
  have hp := Real.pow_div_factorial_le_exp a (by linarith : 0 ≤ a) 2
  norm_num at hp
  have hsq := mul_nonneg (show 0 ≤ a-10000 by nlinarith) (show 0 ≤ a by linarith)
  have he : 122900480*(M+8) ≤ Real.exp a := by nlinarith
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-a)).le
  have hid : Real.exp a*Real.exp (-a)=1 := by rw [← Real.exp_add]; simp
  rw [hid] at hm
  nlinarith

theorem transition_scale_data (t u M : ℝ) (z w : ℂ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hu : 65536*(M+7) ≤ u)
    (hs : phaseSlope 3 t u=0) (hy : z.im ≤ 1) (hz : ‖z‖ ≤ M*realScale u)
    (hw : w ∈ closedBall (movingAnchor u z) (1/1024))
    (hr : modelDerivative 3 t w= -(Complex.I*z)) :
    8 ≤ (M+8)*realScale u ∧ 10000 ≤ w.re ∧ |w.im| ≤ 1/2 ∧ ‖w‖ ≤ 2*w.re ∧
      ‖Complex.exp (4*w)‖ ≤ (M+8)*realScale u ∧
      (30005*Real.exp (-w.re))*((M+8)*realScale u) ≤ t*w.re^5/4 ∧
      t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re := by
  have hg := transition_model_geometry t u M z w ht hM hu hs hy hz hw hr
  have hc := Complex.abs_re_le_norm (w-(u : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hc
  have haU := (abs_le.mp (hc.trans hg.1)).1
  have haM : 50000*(M+8) ≤ w.re := by linarith
  have ha : 10000 ≤ w.re := by linarith
  have hu1 : 1 ≤ u := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hB := real_saddle_scale_lower t u hu1 hs
  have hBu : realScale u ≤ 6*t*u^5+12 := by
    have hh := (RiemannEvenRealSaddle.stationary_scale_bounds 3 t u hu1 hs).1
    norm_num at hh
    unfold realScale
    linarith
  have htu : 1 ≤ t*u^5 := by
    have hh : 1 ≤ u^5 := one_le_pow₀ hu1
    nlinarith
  have hB18 : realScale u ≤ 18*t*u^5 := by linarith
  have huA : u ≤ 2*w.re := by linarith
  have hcube := pow_le_pow_left₀ (by linarith : 0 ≤ u) huA 5
  have hcubeT := mul_le_mul_of_nonneg_left hcube ht0
  have hBcomp : realScale u ≤ 576*t*w.re^5 := by nlinarith
  have hK : 8 ≤ (M+8)*realScale u := by nlinarith [realScale_pos u]
  have hn : ‖w‖ ≤ 2*w.re := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_nonneg (by linarith : 0 ≤ w.re)] at h
    linarith [hg.2.2.1]
  have hnU : ‖w‖ ≤ 2*u := by
    have h := norm_add_le (w-(u : ℂ)) (u : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ u)] at h
    linarith [hg.1]
  have hExp : ‖Complex.exp (4*w)‖ ≤ (M+8)*realScale u := by
    have heq : 4*(Real.pi : ℂ)*Complex.exp (4*w)=6*(t : ℂ)*w^5+9+Complex.I*z := by
      unfold modelDerivative at hr
      linear_combination -hr
    have heNorm := congrArg norm heq
    have h1 := norm_add_le (6*(t : ℂ)*w^5+9) (Complex.I*z)
    have h2 := norm_add_le (6*(t : ℂ)*w^5) (9 : ℂ)
    simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_pos Real.pi_pos,
      Complex.norm_I, one_mul] at heNorm h1 h2
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hnU 5)
      (show 0 ≤ 6*t by positivity)
    have hpi := mul_le_mul_of_nonneg_right
      (show 4 ≤ 4*Real.pi by linarith [Real.pi_gt_three]) (norm_nonneg (Complex.exp (4*w)))
    nlinarith [mul_nonneg hM (realScale_pos u).le]
  have herr := transition_error_small w.re M hM (by linarith) haM
  refine ⟨hK,ha,hg.2.2.1,hn,hExp,?_,hg.2.2.2.1⟩
  calc
    _ = ((30005*Real.exp (-w.re))*(M+8))*realScale u := by ring
    _ ≤ (1/4096)*realScale u := mul_le_mul_of_nonneg_right herr (realScale_pos u).le
    _ ≤ t*w.re^5/4 := by nlinarith

theorem actual_transition_saddle (t u M : ℝ) (z : ℂ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hu : 65536*(M+7) ≤ u)
    (hs : phaseSlope 3 t u=0) (hy : z.im ≤ 1) (hz : ‖z‖ ≤ M*realScale u) :
    ∃ v : ℂ, 0 ≤ v.re ∧ 1 ≤ (Complex.exp (4*v)).re ∧ kernelComplex v ≠ 0 ∧
      complexSlope 3 t v= -(Complex.I*z) ∧ deriv (complexSlope 3 t) v ≠ 0 ∧
      (deriv (complexSlope 3 t) v).re ≤ -(t*u^5/16) ∧ ‖v-(u : ℂ)‖ ≤ M+8 := by
  obtain ⟨w,hw,_⟩ := existsUnique_transition_model_saddle t u M z ht hM hu hs hy hz
  obtain ⟨hK,ha,hi,hn,hExp,hsmall,hmargin⟩ := transition_scale_data t u M z w ht hM hu hs hy hz hw.1 hw.2
  let K := (M+8)*realScale u
  have hK0 : 0 < K := by dsimp [K]; positivity [realScale_pos u]
  have hwpos : 0 < w.re := by linarith
  obtain ⟨v,hv,_⟩ := actual_scaled_frequency_disk t K z w z ht hK ha hmargin hi hn hy hw.2 hExp hsmall
    (by simp; positivity)
  have hder := scaled_actual_deriv_lower t K z w v ht hK ha hmargin hi hn hy hw.2 hExp hsmall hv.1
  have hne : deriv (complexSlope 3 t) v ≠ 0 := norm_pos_iff.mp (by
    have hpos : 0 < 2*t*w.re^5 := by positivity
    linarith)
  have hg := transition_model_geometry t u M z w ht hM hu hs hy hz hw.1 hw.2
  have hc := Complex.abs_re_le_norm (w-(u : ℂ))
  simp only [Complex.sub_re,Complex.ofReal_re] at hc
  have haU := (abs_le.mp (hc.trans hg.1)).1
  have hu0 : 0 ≤ u := by linarith
  have huA : u ≤ 2*w.re := by linarith
  have hpower := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0 huA 5)
    (show 0 ≤ t by linarith)
  have hRe := scaled_actual_real_curvature t K z w v ht hK ha hmargin hi hn hy hw.2 hExp hsmall hv.1
  have hcurv : (deriv (complexSlope 3 t) v).re ≤ -(t*u^5/16) := by nlinarith
  have hdist : ‖v-w‖ ≤ 1/K := by simpa only [mem_closedBall,dist_eq_norm] using hv.1
  have hdist2 : ‖v-w‖ ≤ 2/K := hdist.trans (by
    apply (div_le_div_iff_of_pos_right hK0).mpr
    norm_num)
  have hdom := scaled_neighbor_domain t K z w v ht hK ha hmargin hi hy hw.2 hExp hdist2
  have hker := kernel_ne_zero v hdom.1 hdom.2.1
  refine ⟨v,hdom.1,hdom.2.1,hker,hv.2,hne,hcurv,?_⟩
  have hsmallrad : 1/K ≤ 1 := (div_le_iff₀ hK0).mpr (by
    simp only [one_mul]
    change 1 ≤ (M+8)*realScale u
    linarith)
  have htri := norm_add_le (v-w) (w-(u : ℂ))
  rw [sub_add_sub_cancel] at htri
  linarith [hg.1]

theorem eventually_exists_actual_transition_family (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, 65536*(M+7) ≤ u ∧ phaseSlope 3 t u=0 ∧
      ∀ z : ℂ, z.im ≤ 1 → ‖z‖ ≤ M*realScale u →
        ∃ v : ℂ, 0 ≤ v.re ∧ 1 ≤ (Complex.exp (4*v)).re ∧ kernelComplex v ≠ 0 ∧
          complexSlope 3 t v= -(Complex.I*z) ∧ deriv (complexSlope 3 t) v ≠ 0 ∧
          (deriv (complexSlope 3 t) v).re ≤ -(t*u^5/16) ∧ ‖v-(u : ℂ)‖ ≤ M+8 := by
  filter_upwards [eventually_exists_transition_family M hM,eventually_ge_atTop (1 : ℝ)] with t hmod ht
  obtain ⟨u,hu,hs,_⟩ := hmod
  exact ⟨u,hu,hs,fun z hy hz => actual_transition_saddle t u M z ht hM hu hs hy hz⟩

theorem local_actual_saddle_branch (m : ℕ) (t : ℝ) (z v : ℂ)
    (hE : 0 < (Complex.exp (4*v)).re) (hk : kernelComplex v ≠ 0)
    (hr : complexSlope m t v= -(Complex.I*z)) (hn : deriv (complexSlope m t) v ≠ 0) :
    ∃ branch : ℂ → ℂ, branch z=v ∧ AnalyticAt ℂ branch z ∧
      HasStrictDerivAt branch (-Complex.I/deriv (complexSlope m t) v) z ∧
      ∀ᶠ q in nhds z, complexSlope m t (branch q)= -(Complex.I*q) ∧
        0 < (Complex.exp (4*branch q)).re ∧ kernelComplex (branch q) ≠ 0 := by
  have hak := kernelComplex_analyticAt v hE
  have ha : AnalyticAt ℂ (complexSlope m t) v :=
    (analyticAt_const.mul (analyticAt_id.pow (2*m-1))).add (hak.deriv.div hak hk)
  have hf := ha.hasStrictDerivAt
  let inv := hf.localInverse (complexSlope m t) (deriv (complexSlope m t) v) v hn
  have hleft : inv (complexSlope m t v)=v := (hf.eventually_left_inverse hn).self_of_nhds
  have hbase : inv (-(Complex.I*z))=v := by simpa only [hr] using hleft
  have hd : HasStrictDerivAt inv (deriv (complexSlope m t) v)⁻¹ (-(Complex.I*z)) := by
    simpa only [hr] using hf.to_localInverse hn
  have hright : ∀ᶠ y in nhds (-(Complex.I*z)), complexSlope m t (inv y)=y := by
    simpa only [hr] using hf.eventually_right_inverse hn
  have hainv : AnalyticAt ℂ inv (-(Complex.I*z)) := by
    simpa only [hr] using ha.analyticAt_localInverse hn
  have hab : AnalyticAt ℂ (fun q : ℂ => inv (-(Complex.I*q))) z :=
    AnalyticAt.comp (g := inv) (f := fun q : ℂ => -(Complex.I*q)) hainv (by fun_prop)
  refine ⟨(fun q => inv (-(Complex.I*q))), hbase, hab, ?_, ?_⟩
  · have hmul := (hasStrictDerivAt_id z).const_mul (-Complex.I)
    have hdf : HasStrictDerivAt inv (deriv (complexSlope m t) v)⁻¹ (-Complex.I*z) := by
      simpa only [neg_mul] using hd
    have hcomp := hdf.comp z hmul
    convert hcomp using 1
    · funext q
      congr 1
      ring
    · simp only [div_eq_mul_inv]
      ring
  · have hc : Tendsto (fun q : ℂ => -(Complex.I*q)) (nhds z) (nhds (-(Complex.I*z))) := by
      exact (show ContinuousAt (fun q : ℂ => -(Complex.I*q)) z from by fun_prop).tendsto
    have he : ∀ᶠ w in nhds v, 0 < (Complex.exp (4*w)).re :=
      (show ContinuousAt (fun w : ℂ => (Complex.exp (4*w)).re) v from by
        fun_prop).eventually (lt_mem_nhds hE)
    have hkn := hak.continuousAt.eventually_ne hk
    have hb : Tendsto (fun q : ℂ => inv (-(Complex.I*q))) (nhds z) (nhds v) := by
      simpa only [ContinuousAt, hbase] using hab.continuousAt
    filter_upwards [hc.eventually hright, hb.eventually he, hb.eventually hkn] with q hq he hkq
    exact ⟨hq,he,hkq⟩

theorem actual_transition_local_branch (t u M : ℝ) (z : ℂ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hu : 65536*(M+7) ≤ u)
    (hs : phaseSlope 3 t u=0) (hy : z.im ≤ 1) (hz : ‖z‖ ≤ M*realScale u) :
    ∃ branch : ℂ → ℂ, ‖branch z-(u : ℂ)‖ ≤ M+8 ∧ AnalyticAt ℂ branch z ∧
      deriv (complexSlope 3 t) (branch z) ≠ 0 ∧
      (deriv (complexSlope 3 t) (branch z)).re ≤ -(t*u^5/16) ∧
      HasStrictDerivAt branch (-Complex.I/deriv (complexSlope 3 t) (branch z)) z ∧
      ∀ᶠ q in nhds z, complexSlope 3 t (branch q)= -(Complex.I*q) ∧
        0 < (Complex.exp (4*branch q)).re ∧ kernelComplex (branch q) ≠ 0 := by
  obtain ⟨v,hvre,hvE,hvk,hvr,hvn,hvcurv,hvd⟩ := actual_transition_saddle t u M z ht hM hu hs hy hz
  obtain ⟨b,hb,ha,hd,he⟩ := local_actual_saddle_branch 3 t z v (by linarith) hvk hvr hvn
  exact ⟨b, by simpa only [hb] using hvd, ha, by simpa only [hb] using hvn,
    by simpa only [hb] using hvcurv, by simpa only [hb] using hd, he⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionCorrection
