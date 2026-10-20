import Foundation.RiemannSixthFarLeftAnnulus
import Foundation.RiemannEvenHorizontalDecomposition
/-! Complete actual A6 horizontal half-line Gaussian asymptotics.
One channel is controlled; the reflected flow pairing is kept distinct. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarHalfline
open RiemannSixthFarLeftAnnulus RiemannSixthFarLeftCompact RiemannSixthFarRightTail
open RiemannSixthFarGaussianLimit RiemannSixthFarGaussianFixed RiemannSixthFarCorrection
open RiemannSixthFarRemainder RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight
open RiemannEvenNaturalContour RiemannEvenHorizontalDecomposition

theorem eventually_uniform_horizontal_gaussian_error (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 10000*(t*(‖w‖+1)^5+1) ≤ x →
      modelDerivative 3 t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope 3 t v= -(Complex.I*z) → |z.im| ≤ 1 →
      IntegrableOn (fun s : ℝ => weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
      ‖(∫ s : ℝ in Ioi 0, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  let R : ℝ := 1/8192
  have hR : 0 < R := by norm_num [R]
  filter_upwards [eventually_uniform_relative_left_compact (η/8) (by positivity),
    eventually_uniform_relative_left_annulus R (η/8) hR (by norm_num [R]) (by positivity),
    eventually_uniform_fixed_gaussian_error R (η/8) hR (by norm_num [R]) (by positivity),
    eventually_uniform_relative_right_tail R (η/8) hR (by positivity),
    eventually_ge_atTop (10000 : ℝ),eventually_ge_atTop (100000000/R)]
    with x hcompact hleft hcenter hright hx hxR
  intro t ht w v hr hi hp hs hv z hz hzim
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 6*t*‖w‖^5+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 5]
  have hgeom := RiemannSixthFarAnalyticBranch.corrected_saddle_geometry t x ht hx w hr hi hp hs v
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have he := arithmetic_error_frequency_bound t x ht hx w hp hs
  have heR : 100000000/x ≤ R := by
    apply (div_le_iff₀ hx0).mpr
    have hm := (div_le_iff₀ hR).mp hxR
    nlinarith
  have hw3 : 16 ≤ w.re^5 := by
    have hw2 : 1 ≤ w.re^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hw2 (by linarith : 0 ≤ w.re)]
  have hwt : w.re^5 ≤ t*w.re^5 := by nlinarith
  have hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^5/16)*R := by
    have hm := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ t*w.re^5/16) hR.le
    linarith
  have htail := (actual_right_tail_bound t x ht (by linarith) w v (by linarith) hi hs hp0 hv z hz R hR hsmall).1
  refine ⟨shifted_weight_integrable 3 t z v.im hgeom.2.1,?_⟩
  have hsplit := horizontal_decomposition 3 t z v hgeom.2.1 R htail
  have hC := hcompact t ht w v hr hi hp hs hv z hz hzim
  have hL := hleft t ht w v hr hi hp hs hv z hz
  have hM := hcenter t ht w v (by linarith) hi hp hs hv z hz
  have hT := (hright t ht w v (by linarith) hi hp hs hv z hz).2
  let D := weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2))
  let C := ∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let L := ∫ s : ℝ in -1..-R, weight 3 t z (v+(s : ℂ))
  let M := ∫ s : ℝ in -R..R, weight 3 t z (v+(s : ℂ))
  let T := ∫ s : ℝ in Ioi R, weight 3 t z (v+(s : ℂ))
  change ‖C/D‖ ≤ η/8 at hC
  change ‖L/D‖ ≤ η/8 at hL
  change ‖M/D-1‖ ≤ η/8 at hM
  change ‖T/D‖ ≤ η/8 at hT
  rw [hsplit]
  change ‖(C+L+M+T)/D-1‖ ≤ η
  rw [show (C+L+M+T)/D-1=C/D+L/D+(M/D-1)+T/D by ring]
  have h1 := norm_add_le (C/D) (L/D)
  have h2 := norm_add_le (C/D+L/D) (M/D-1)
  have h3 := norm_add_le (C/D+L/D+(M/D-1)) (T/D)
  linarith

theorem horizontal_relative_limit_for_saddle_family (t : ℝ) (ht : 1 ≤ t) (w v z : ℝ → ℂ)
    (hdata : ∀ᶠ x : ℝ in atTop, 120020 ≤ (w x).re ∧ |(w x).im| ≤ 1/2 ∧
      10000*(t*(‖w x‖+1)^5+1) ≤ x ∧ modelDerivative 3 t (w x)= -(Complex.I*(x : ℂ)) ∧
      ‖v x-w x‖ ≤ 1/x ∧ complexSlope 3 t (v x)= -(Complex.I*z x) ∧ |(z x).im| ≤ 1) :
    Tendsto (fun x : ℝ =>
      (∫ s : ℝ in Ioi 0, weight 3 t (z x) ((s : ℂ)+((v x).im : ℂ)*Complex.I))/
        (weight 3 t (z x) (v x)*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) (v x)*(s : ℂ)^2/2))))
      atTop (nhds (1 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [eventually_uniform_horizontal_gaussian_error (η/2) (by positivity),hdata]
    with x herror hdatax
  obtain ⟨hr,hi,hp,hs,hv,hstat,hzim⟩ := hdatax
  have h := (herror t ht (w x) (v x) hr hi hp hs hv (z x) hstat hzim).2
  have hlt := lt_of_le_of_lt h (by linarith : η/2 < η)
  simpa only [dist_eq_norm] using hlt

theorem exists_uniform_actual_horizontal_gaussian :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ t u x : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x →
      ∃ w : ℂ, 10000 ≤ x ∧ 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
        10000*(t*(‖w‖+1)^5+1) ≤ x ∧ modelDerivative 3 t w = -(Complex.I*(x : ℂ)) ∧
        ∀ z : ℂ, ‖z-(x : ℂ)‖ ≤ 1 → ∃ v : ℂ,
          v ∈ closedBall w (1/x) ∧ complexSlope 3 t v = -(Complex.I*z) ∧
          1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ weight 3 t z v ≠ 0 ∧
          weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 ∧
          IntegrableOn (fun s : ℝ => weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
          RiemannEvenFlow.flow 3 t z =
            ((∫ s : ℝ in Ioi 0, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))+
              (∫ s : ℝ in Ioi 0, weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)))/2 ∧
          ‖(∫ s : ℝ in Ioi 0, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
            (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  obtain ⟨K,hK,hconstruct⟩ := RiemannSixthUniformFarSaddles.exists_uniform_actual_far_frequency_disks
  refine ⟨K,hK,?_⟩
  intro η hη
  obtain ⟨X,hX⟩ := eventually_atTop.mp (eventually_uniform_horizontal_gaussian_error η hη)
  refine ⟨X,?_⟩
  intro t u x ht hu hstat hx
  have hxK := (le_max_right X (K*RiemannQuarticTransitionSaddle.realScale u)).trans hx
  have hxX := (le_max_left X (K*RiemannQuarticTransitionSaddle.realScale u)).trans hx
  obtain ⟨w,hxlarge,hr,hi,hp,hs,hroots⟩ := hconstruct t u x ht hu hstat hxK
  refine ⟨w,hxlarge,hr,hi,hp,hs,?_⟩
  intro z hz
  obtain ⟨v,⟨hv,hvstat⟩,_⟩ := hroots z hz
  have hd := RiemannSixthFarAnalyticBranch.corrected_saddle_geometry
    t x ht hxlarge w hr hi hp hs v hv
  have hvdist : ‖v-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hn := gaussian_normalization_lower t x ht hxlarge w v (by linarith) hi hp hs hvdist
  have hG : (∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 := by
    intro h
    rw [h,norm_zero,mul_zero] at hn
    norm_num at hn
  have hW : weight 3 t z v ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hd.2.2
  have hzim : |z.im| ≤ 1 := by
    have h := (Complex.abs_im_le_norm (z-(x : ℂ))).trans hz
    simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using h
  have hwhole := hX x hxX t ht w v hr hi hp hs hvdist z hvstat hzim
  exact ⟨v,hv,hvstat,hd.1,hd.2.1,hW,mul_ne_zero hW hG,hwhole.1,
    flow_eq_paired_horizontal 3 t z v.im hd.2.1,hwhole.2⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarHalfline
