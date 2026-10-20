import Foundation.RiemannSixthComplexGaussian
/-! Uniform signed central Gaussian approximation for constructed actual A6
saddles at complex frequency centers. Complementary contours remain separate. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthComplexCentral
open RiemannSixthComplexGaussian RiemannSixthComplexCorrection
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight
open RiemannQuarticErrorLimits
open RiemannQuarticFarGaussianLimit (relativeBudget smallBudget
  relativeBudget_tendsto_zero smallBudget_tendsto_zero)

theorem uniform_local_gaussian_error (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ c : ℂ, c.im ≤ 0 → ‖c‖=N →
      ∀ w v : ℂ, 4096 ≤ w.re → |w.im| ≤ 1/2 →
      10000*(t*(‖w‖+1)^5+1) ≤ ‖c‖ → modelDerivative 3 t w= -(Complex.I*c) →
      ‖v-w‖ ≤ 1/‖c‖ → ∀ z : ℂ, complexSlope 3 t v= -(Complex.I*z) →
      ‖(∫ s : ℝ in -(centralRadius ‖c‖)..centralRadius ‖c‖, weight 3 t z (v+(s : ℂ)))/
        (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  filter_upwards [eventually_ge_atTop (10000 : ℝ),
    centralRadius_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/16)),
    smallBudget_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    relativeBudget_tendsto_zero.eventually (gt_mem_nhds hη)] with N hN hr hsmall hηN
  intro t ht c hcenter hn w v hrw hi hp hs hv z hstat
  have hc := central_relative_error_bound t c hcenter ht (by simpa only [hn] using hN)
    w v hrw hi hp hs hv z hstat (by simpa only [hn] using hr) (by simpa only [hn] using hsmall.le)
  exact hc.trans (by simpa only [hn] using hηN.le)

theorem exists_uniform_actual_complex_central_gaussian :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ t u : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      ∀ c : ℂ, c.im ≤ 0 → max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ ‖c‖ →
        ∃ w : ℂ, 10000 ≤ ‖c‖ ∧ 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
          10000*(t*(‖w‖+1)^5+1) ≤ ‖c‖ ∧ modelDerivative 3 t w = -(Complex.I*c) ∧
          ∀ z : ℂ, ‖z-c‖ ≤ 1 → ∃ v : ℂ,
            v ∈ closedBall w (1/‖c‖) ∧ complexSlope 3 t v = -(Complex.I*z) ∧
            1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ weight 3 t z v ≠ 0 ∧
            weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 ∧
            IntervalIntegrable (fun s : ℝ => weight 3 t z (v+(s : ℂ))) volume
              (-(centralRadius ‖c‖)) (centralRadius ‖c‖) ∧
            RiemannEvenFlow.flow 3 t z =
              ((∫ s : ℝ in Ioi 0, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))+
                (∫ s : ℝ in Ioi 0, weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)))/2 ∧
            ‖(∫ s : ℝ in -(centralRadius ‖c‖)..centralRadius ‖c‖, weight 3 t z (v+(s : ℂ)))/
              (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  obtain ⟨K,hK,hC⟩ := exists_uniform_actual_far_complex_disks
  refine ⟨K,hK,?_⟩
  intro η hη
  obtain ⟨X,hX⟩ := eventually_atTop.mp (uniform_local_gaussian_error η hη)
  refine ⟨X,?_⟩
  intro t u ht hu hstat c hcenter hcut
  obtain ⟨w,hN,hr,hi,hp,hs,hroots⟩ := hC t u ht hu hstat c hcenter ((le_max_right _ _).trans hcut)
  refine ⟨w,hN,hr,hi,hp,hs,?_⟩
  intro z hz
  obtain ⟨v,⟨hv,hvstat⟩,hunique⟩ := hroots z hz
  have hvd : ‖v-w‖ ≤ 1/‖c‖ := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hd := corrected_saddle_geometry t c hcenter ht hN w v hr hi hp hs hv
  have hW : weight 3 t z v ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hd.2.2
  have hG := gaussian_normalization_lower t c hcenter ht hN w v (by linarith) hi hp hs hvd
  have hGn : (∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 := by
    intro h
    norm_num [h] at hG
  have hf : Continuous (fun s : ℝ => weight 3 t z (v+(s : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have hw := weight_analyticAt 3 t z (v+(s : ℂ)) (by simpa [Complex.add_im] using hd.2.1)
    exact ContinuousAt.comp (g := weight 3 t z) (f := fun s : ℝ => v+(s : ℂ))
      hw.continuousAt (by fun_prop)
  exact ⟨v,hv,hvstat,hd.1,hd.2.1,hW,mul_ne_zero hW hGn,hf.intervalIntegrable _ _,
    RiemannEvenNaturalContour.flow_eq_paired_horizontal 3 t z v.im hd.2.1,
    hX ‖c‖ ((le_max_left _ _).trans hcut) t ht c hcenter rfl w v (by linarith) hi hp hs hvd z hvstat⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthComplexCentral
