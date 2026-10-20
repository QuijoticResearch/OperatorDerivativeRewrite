import Foundation.RiemannSixthComplexAnnulus
import Foundation.RiemannSixthComplexLeftAnnulus
import Foundation.RiemannEvenHorizontalDecomposition
/-! Complete signed actual sixth-order horizontal Gaussian asymptotics at
complex frequency centers. The opposite-frequency flow remains a separate pair. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthComplexHalfline
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight
open RiemannSixthComplexGaussian RiemannSixthComplexCorrection RiemannQuarticErrorLimits
open RiemannSixthComplexAnnulus RiemannEvenNaturalContour RiemannEvenHorizontalDecomposition

theorem uniform_fixed_gaussian_error (R η : ℝ) (hR0 : 0 < R)
    (hR : R ≤ 1/8192) (hη : 0 < η) :
    ∀ᶠ N : ℝ in atTop, ∀ c : ℂ, c.im ≤ 0 → ‖c‖=N → ∀ t : ℝ, 1 ≤ t →
      ∀ w v : ℂ, 120020 ≤ w.re → |w.im| ≤ 1/2 →
        10000*(t*(‖w‖+1)^5+1) ≤ ‖c‖ → modelDerivative 3 t w= -(Complex.I*c) →
        ‖v-w‖ ≤ 1/‖c‖ → ∀ z : ℂ, complexSlope 3 t v= -(Complex.I*z) →
        ‖(∫ s : ℝ in -R..R, weight 3 t z (v+(s : ℂ)))/
          (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  filter_upwards [RiemannSixthComplexCentral.uniform_local_gaussian_error (η/4) (by positivity),
    uniform_relative_annulus R (η/4) hR0 hR (by positivity),
    eventually_ge_atTop (10000 : ℝ),
    centralRadius_tendsto_zero.eventually (gt_mem_nhds hR0)] with N hlocal hann hN hradius
  intro c hc hn t ht w v hr hi hp hs hv z hz
  subst N
  have hgeom := corrected_saddle_geometry t c hc ht hN w v hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have hspl := neighborhood_decomposition 3 t z v hgeom.2.1
    (centralRadius ‖c‖) R (Real.rpow_pos_of_pos (by linarith : 0 < ‖c‖) _).le hradius.le
  have hC := hlocal t ht c hc rfl w v (by linarith) hi hp hs hv z hz
  have hL := hann c hc rfl t ht w v (by linarith) hi hp hs hv z hz (-1) (by norm_num)
  have hU := hann c hc rfl t ht w v (by linarith) hi hp hs hv z hz 1 (by norm_num)
  simp only [neg_one_mul,one_mul] at hL hU
  let D := weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2))
  let C := ∫ s : ℝ in -(centralRadius ‖c‖)..centralRadius ‖c‖, weight 3 t z (v+(s : ℂ))
  let L := ∫ s : ℝ in centralRadius ‖c‖..R, weight 3 t z (v+((-s : ℝ) : ℂ))
  let U := ∫ s : ℝ in centralRadius ‖c‖..R, weight 3 t z (v+(s : ℂ))
  change ‖C/D-1‖ ≤ η/4 at hC
  change ‖L/D‖ ≤ η/4 at hL
  change ‖U/D‖ ≤ η/4 at hU
  rw [hspl]
  change ‖(C+L+U)/D-1‖ ≤ η
  rw [show (C+L+U)/D-1=(C/D-1)+L/D+U/D by ring]
  have h1 := norm_add_le (C/D-1) (L/D)
  have h2 := norm_add_le ((C/D-1)+L/D) (U/D)
  linarith

theorem uniform_horizontal_gaussian_error (η : ℝ) (hη : 0 < η) :
    ∃ X : ℝ, ∀ c : ℂ, c.im ≤ 0 → X ≤ ‖c‖ → ∀ t : ℝ, 1 ≤ t →
      ∀ w v : ℂ, 120020 ≤ w.re → |w.im| ≤ 1/2 →
        10000*(t*(‖w‖+1)^5+1) ≤ ‖c‖ → modelDerivative 3 t w= -(Complex.I*c) →
        ‖v-w‖ ≤ 1/‖c‖ → ∀ z : ℂ, complexSlope 3 t v= -(Complex.I*z) → z.im ≤ 0 →
        IntegrableOn (fun s : ℝ => weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
        ‖(∫ s : ℝ in Ioi 0, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
          (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  let R : ℝ := 1/8192
  have hR : 0 < R := by norm_num [R]
  obtain ⟨XC,hXC⟩ := RiemannSixthComplexLeftCompact.uniform_relative_left_compact (η/8) (by positivity)
  obtain ⟨XL,hXL⟩ := eventually_atTop.mp
    (RiemannSixthComplexLeftAnnulus.uniform_relative_left_annulus R (η/8) hR (by norm_num [R]) (by positivity))
  obtain ⟨XM,hXM⟩ := eventually_atTop.mp
    (uniform_fixed_gaussian_error R (η/8) hR (by norm_num [R]) (by positivity))
  obtain ⟨XT,hXT⟩ := RiemannSixthComplexRightTail.uniform_relative_right_tail R (η/8) hR (by positivity)
  refine ⟨max 10000 (max XC (max XL (max XM XT))),?_⟩
  intro c hc hcut t ht w v hr hi hp hs hv z hz hzim
  have hN : 10000 ≤ ‖c‖ := (le_max_left _ _).trans hcut
  have hCuts : max XC (max XL (max XM XT)) ≤ ‖c‖ := (le_max_right _ _).trans hcut
  have hCcut : XC ≤ ‖c‖ := (le_max_left _ _).trans hCuts
  have hrest : max XL (max XM XT) ≤ ‖c‖ := (le_max_right _ _).trans hCuts
  have hLcut : XL ≤ ‖c‖ := (le_max_left _ _).trans hrest
  have hrest' : max XM XT ≤ ‖c‖ := (le_max_right _ _).trans hrest
  have hMcut : XM ≤ ‖c‖ := (le_max_left _ _).trans hrest'
  have hTcut : XT ≤ ‖c‖ := (le_max_right _ _).trans hrest'
  have hgeom := corrected_saddle_geometry t c hc ht hN w v hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have htail := hXT t ht c hc hTcut w v (by linarith) hi hp hs hv z hz
  refine ⟨shifted_weight_integrable 3 t z v.im hgeom.2.1,?_⟩
  have hsplit := horizontal_decomposition 3 t z v hgeom.2.1 R htail.1
  have hC := hXC c hc hCcut t ht w v hr hi hp hs hv z hz hzim
  have hL := hXL ‖c‖ hLcut c hc rfl t ht w v hr hi hp hs hv z hz
  have hM := hXM ‖c‖ hMcut c hc rfl t ht w v hr hi hp hs hv z hz
  have hT := htail.2
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

theorem horizontal_relative_limit_for_saddle_family (t : ℝ → ℝ) (c w v z : ℝ → ℂ)
    (hfreq : Tendsto (fun s => ‖c s‖) atTop atTop)
    (hdata : ∀ᶠ s : ℝ in atTop, 1 ≤ t s ∧ (c s).im ≤ 0 ∧
      120020 ≤ (w s).re ∧ |(w s).im| ≤ 1/2 ∧
      10000*(t s*(‖w s‖+1)^5+1) ≤ ‖c s‖ ∧ modelDerivative 3 (t s) (w s)= -(Complex.I*c s) ∧
      ‖v s-w s‖ ≤ 1/‖c s‖ ∧ complexSlope 3 (t s) (v s)= -(Complex.I*z s) ∧ (z s).im ≤ 0) :
    Tendsto (fun s =>
      (∫ a : ℝ in Ioi 0, weight 3 (t s) (z s) ((a : ℂ)+((v s).im : ℂ)*Complex.I))/
        (weight 3 (t s) (z s) (v s)*(∫ a : ℝ, Complex.exp (deriv (modelDerivative 3 (t s)) (v s)*(a : ℂ)^2/2))))
      atTop (nhds (1 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨X,hX⟩ := uniform_horizontal_gaussian_error (η/2) (by positivity)
  filter_upwards [hdata,hfreq.eventually (eventually_ge_atTop X)] with s hs hlarge
  obtain ⟨ht,hc,hr,hi,hp,hmodel,hv,hstat,hzim⟩ := hs
  have h := (hX (c s) hc hlarge (t s) ht (w s) (v s) hr hi hp hmodel hv (z s) hstat hzim).2
  have hlt := lt_of_le_of_lt h (by linarith : η/2 < η)
  simpa only [dist_eq_norm] using hlt

theorem exists_uniform_actual_horizontal_gaussian :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ t u : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      ∀ c : ℂ, c.im ≤ 0 → max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ ‖c‖ →
        ∃ w : ℂ, 10000 ≤ ‖c‖ ∧ 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
          10000*(t*(‖w‖+1)^5+1) ≤ ‖c‖ ∧ modelDerivative 3 t w = -(Complex.I*c) ∧
          ∀ z : ℂ, ‖z-c‖ ≤ 1 → z.im ≤ 0 → ∃ v : ℂ,
            v ∈ closedBall w (1/‖c‖) ∧ complexSlope 3 t v = -(Complex.I*z) ∧
            1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ weight 3 t z v ≠ 0 ∧
            weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 ∧
            IntegrableOn (fun s : ℝ => weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
            IntegrableOn (fun s : ℝ => weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
            RiemannEvenFlow.flow 3 t z =
              ((∫ s : ℝ in Ioi 0, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))+
                (∫ s : ℝ in Ioi 0, weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)))/2 ∧
            ‖(∫ s : ℝ in Ioi 0, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
              (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  obtain ⟨K,hK,hC⟩ := exists_uniform_actual_far_complex_disks
  refine ⟨K,hK,?_⟩
  intro η hη
  obtain ⟨X,hX⟩ := uniform_horizontal_gaussian_error η hη
  refine ⟨X,?_⟩
  intro t u ht hu hstat c hc hcut
  obtain ⟨w,hN,hr,hi,hp,hs,hroots⟩ := hC t u ht hu hstat c hc ((le_max_right _ _).trans hcut)
  refine ⟨w,hN,hr,hi,hp,hs,?_⟩
  intro z hz hzim
  obtain ⟨v,⟨hv,hvstat⟩,_⟩ := hroots z hz
  have hvdist : ‖v-w‖ ≤ 1/‖c‖ := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hd := corrected_saddle_geometry t c hc ht hN w v hr hi hp hs hv
  have hW : weight 3 t z v ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hd.2.2
  have hG := gaussian_normalization_lower t c hc ht hN w v (by linarith) hi hp hs hvdist
  have hGn : (∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 := by
    intro h
    norm_num [h] at hG
  have hmain := hX c hc ((le_max_left _ _).trans hcut) t ht w v hr hi hp hs hvdist z hvstat hzim
  have href := shifted_weight_integrable 3 t (-z) (-v.im) (by simpa only [abs_neg] using hd.2.1)
  simp only [Complex.ofReal_neg,neg_mul,← sub_eq_add_neg] at href
  exact ⟨v,hv,hvstat,hd.1,hd.2.1,hW,mul_ne_zero hW hGn,hmain.1,href,
    flow_eq_paired_horizontal 3 t z v.im hd.2.1,hmain.2⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthComplexHalfline
