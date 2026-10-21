import Foundation.RiemannEvenRealityClosed

/-! Actual bounded positive even theta density and Gaussian smoothing: genuine integrals, distributional identification and a dominated pointwise approximate identity. -/
noncomputable section
open MeasureTheory Filter Set Real ProbabilityTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticDensitySmoothing
open RiemannQuarticKernel

def evenDensity (x : ℝ) : ℝ := kernel |x|

theorem evenDensity_continuous : Continuous evenDensity := by
  have hk : Continuous kernel := continuous_iff_continuousAt.mpr
    (fun x => (RiemannQuarticRealSaddle.kernel_hasDerivAt x).continuousAt)
  exact hk.comp continuous_abs

theorem evenDensity_pos (x : ℝ) : 0 < evenDensity x := kernel_pos |x| (abs_nonneg x)

theorem evenDensity_bounded : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |evenDensity x| ≤ C := by
  obtain ⟨u,hu,hmax⟩ := RiemannEvenRealSaddle.exists_global_max 1 0
  refine ⟨kernel u,kernel_pos u hu,?_⟩
  intro x
  have he := hmax (show |x| ∈ Ici (0 : ℝ) from abs_nonneg x)
  change RiemannEvenDomain.weighted 1 0 0 0 |x| ≤ RiemannEvenDomain.weighted 1 0 0 0 u at he
  simpa only [RiemannEvenDomain.weighted,pow_zero,one_mul,zero_mul,add_zero,
    exp_zero,evenDensity,abs_of_pos (kernel_pos |x| (abs_nonneg x))] using he

def smoothing (epsilon x : ℝ) : ℝ :=
  ∫ y : ℝ, evenDensity (x+epsilon*y) ∂RiemannQuadraticGaussian.law 1

theorem smoothing_integrable (epsilon x : ℝ) :
    Integrable (fun y : ℝ => evenDensity (x+epsilon*y)) (RiemannQuadraticGaussian.law 1) := by
  obtain ⟨C,hC,hbound⟩ := evenDensity_bounded
  have hc : Continuous (fun y : ℝ => evenDensity (x+epsilon*y)) :=
    evenDensity_continuous.comp (by fun_prop)
  exact (integrable_const C).mono' hc.aestronglyMeasurable
    (Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hbound (x+epsilon*y)))

theorem smoothing_limit (epsilon : ℕ → ℝ) (he : Tendsto epsilon atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => smoothing (epsilon n) x) atTop (𝓝 (evenDensity x)) := by
  obtain ⟨C,hC,hbound⟩ := evenDensity_bounded
  have hcont (n : ℕ) : Continuous (fun y : ℝ => evenDensity (x+epsilon n*y)) :=
    evenDensity_continuous.comp (by fun_prop)
  have hpt (y : ℝ) : Tendsto (fun n => evenDensity (x+epsilon n*y)) atTop (𝓝 (evenDensity x)) := by
    apply evenDensity_continuous.continuousAt.tendsto.comp
    simpa only [zero_mul,add_zero] using tendsto_const_nhds.add (he.mul_const y)
  have ht := tendsto_integral_of_dominated_convergence
    (μ := RiemannQuadraticGaussian.law 1) (fun _ : ℝ => C)
    (fun n => (hcont n).aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hbound (x+epsilon n*y)))
    (Eventually.of_forall hpt)
  simpa only [smoothing,integral_const,probReal_univ,one_smul] using ht

theorem smoothing_pos (epsilon x : ℝ) : 0 < smoothing epsilon x := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun y => (evenDensity_pos (x+epsilon*y)).le))
    (smoothing_integrable epsilon x)).mpr
  have hs : Function.support (fun y : ℝ => evenDensity (x+epsilon*y)) = univ := by
    ext y
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (evenDensity_pos _).ne'
  rw [hs]
  norm_num

theorem smoothing_distribution (epsilon x : ℝ) :
    smoothing epsilon x = ∫ u : ℝ, evenDensity u
      ∂gaussianReal x (⟨epsilon^2,sq_nonneg epsilon⟩*2) := by
  have hm : (RiemannQuadraticGaussian.law 1).map (fun y : ℝ => x+epsilon*y) =
      gaussianReal x (⟨epsilon^2,sq_nonneg epsilon⟩*2) := by
    simp only [RiemannQuadraticGaussian.law,mul_one]
    change (gaussianReal 0 2).map ((fun u : ℝ => x+u) ∘ (fun y : ℝ => epsilon*y)) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop),gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    simp only [mul_zero,zero_add]
    congr 1
  rw [← hm,integral_map (by fun_prop) evenDensity_continuous.aestronglyMeasurable]
  rfl

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticDensitySmoothing
