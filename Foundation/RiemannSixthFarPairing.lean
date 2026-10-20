import Foundation.RiemannSixthFarHalfline
import Foundation.RiemannEvenHorizontalPairing
/-! Actual sixth-order real-axis cosine comparison after full horizontal
integration. The nonzero complex amplitude norm, never its real part,
normalizes the error; zero-phase localization is not a zero count. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarPairing
open RiemannEvenHorizontalPairing RiemannSixthFarHalfline RiemannSixthFarGaussianLimit
open RiemannEvenComplexWeight RiemannEvenModelPhase RiemannEvenSaddleBranch

def modelGaussianAmplitude (t : ℝ) (z v : ℂ) : ℂ :=
  weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2))

theorem modelGaussianAmplitude_ne_zero (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x) (z : ℂ) :
    modelGaussianAmplitude t z v ≠ 0 := by
  have hg := gaussian_normalization_lower t x ht hx w v (by linarith) hi hp hs hv
  have hG : (∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 := by
    intro h
    norm_num [h] at hg
  have hd := RiemannSixthFarAnalyticBranch.corrected_saddle_geometry t x ht hx w hr hi hp hs v
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hd.2.2) hG

theorem eventually_uniform_real_flow_error (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 10000*(t*(‖w‖+1)^5+1) ≤ x →
      modelDerivative 3 t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ y : ℝ, complexSlope 3 t v= -(Complex.I*(y : ℂ)) →
      modelGaussianAmplitude t (y : ℂ) v ≠ 0 ∧
      ‖RiemannEvenFlow.flow 3 t (y : ℂ)-((modelGaussianAmplitude t (y : ℂ) v).re : ℂ)‖ ≤
        η*‖modelGaussianAmplitude t (y : ℂ) v‖ ∧
      |(RiemannEvenFlow.flow 3 t (y : ℂ)).re/‖modelGaussianAmplitude t (y : ℂ) v‖-
        Real.cos (modelGaussianAmplitude t (y : ℂ) v).arg| ≤ η := by
  filter_upwards [eventually_uniform_horizontal_gaussian_error η hη,eventually_ge_atTop (10000 : ℝ)]
    with x he hx
  intro t ht w v hr hi hp hs hv y hz
  have hd := RiemannSixthFarAnalyticBranch.corrected_saddle_geometry t x ht hx w hr hi hp hs v
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have hA := modelGaussianAmplitude_ne_zero t x ht hx w v hr hi hp hs hv (y : ℂ)
  have he' := (he t ht w v hr hi hp hs hv (y : ℂ) hz (by simp)).2
  change ‖horizontalIntegral 3 t (y : ℂ) v.im/modelGaussianAmplitude t (y : ℂ) v-1‖ ≤ η at he'
  exact ⟨hA,real_pair_error 3 t y v.im hd.2.1 _ hA η he',
    real_pair_cosine_error 3 t y v.im hd.2.1 _ hA η he'⟩

theorem real_flow_cosine_limit_for_saddle_family (t : ℝ) (ht : 1 ≤ t) (w v : ℝ → ℂ)
    (hdata : ∀ᶠ x : ℝ in atTop, 120020 ≤ (w x).re ∧ |(w x).im| ≤ 1/2 ∧
      10000*(t*(‖w x‖+1)^5+1) ≤ x ∧ modelDerivative 3 t (w x)= -(Complex.I*(x : ℂ)) ∧
      ‖v x-w x‖ ≤ 1/x ∧ complexSlope 3 t (v x)= -(Complex.I*(x : ℂ))) :
    Tendsto (fun x : ℝ => (RiemannEvenFlow.flow 3 t (x : ℂ)).re/
      ‖modelGaussianAmplitude t (x : ℂ) (v x)‖-
      Real.cos (modelGaussianAmplitude t (x : ℂ) (v x)).arg) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [eventually_uniform_real_flow_error (η/2) (by positivity),hdata]
    with x he hd
  obtain ⟨hr,hi,hp,hs,hv,hz⟩ := hd
  have h := (he t ht (w x) (v x) hr hi hp hs hv x hz).2.2
  have hlt := lt_of_le_of_lt h (by linarith : η/2 < η)
  simpa only [Real.dist_eq,sub_zero] using hlt


theorem exists_uniform_actual_real_flow_cosine :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ t u x : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x →
      ∃ w : ℂ, 10000 ≤ x ∧ 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
        10000*(t*(‖w‖+1)^5+1) ≤ x ∧ modelDerivative 3 t w = -(Complex.I*(x : ℂ)) ∧
        ∀ y : ℝ, |y-x| ≤ 1 → ∃ v : ℂ,
          v ∈ closedBall w (1/x) ∧ complexSlope 3 t v = -(Complex.I*(y : ℂ)) ∧
          |v.im| < Real.pi/8 ∧ modelGaussianAmplitude t (y : ℂ) v ≠ 0 ∧
          ‖RiemannEvenFlow.flow 3 t (y : ℂ)-((modelGaussianAmplitude t (y : ℂ) v).re : ℂ)‖ ≤
            η*‖modelGaussianAmplitude t (y : ℂ) v‖ ∧
          |(RiemannEvenFlow.flow 3 t (y : ℂ)).re/‖modelGaussianAmplitude t (y : ℂ) v‖-
            Real.cos (modelGaussianAmplitude t (y : ℂ) v).arg| ≤ η := by
  obtain ⟨K,hK,hC⟩ := exists_uniform_actual_horizontal_gaussian
  refine ⟨K,hK,?_⟩
  intro η hη
  obtain ⟨X,hX⟩ := hC η hη
  refine ⟨X,?_⟩
  intro t u x ht hu hstat hx
  obtain ⟨w,hxlarge,hr,hi,hp,hs,hroots⟩ := hX t u x ht hu hstat hx
  refine ⟨w,hxlarge,hr,hi,hp,hs,?_⟩
  intro y hy
  have hy' : ‖(y : ℂ)-(x : ℂ)‖ ≤ 1 := by
    simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hy
  obtain ⟨v,hv,hvstat,hvre,hvim,hW,hD,hI,hflow,he⟩ := hroots (y : ℂ) hy'
  have hA : modelGaussianAmplitude t (y : ℂ) v ≠ 0 := hD
  change ‖horizontalIntegral 3 t (y : ℂ) v.im/modelGaussianAmplitude t (y : ℂ) v-1‖ ≤ η at he
  exact ⟨v,hv,hvstat,hvim,hA,real_pair_error 3 t y v.im hvim _ hA η he,
    real_pair_cosine_error 3 t y v.im hvim _ hA η he⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarPairing
