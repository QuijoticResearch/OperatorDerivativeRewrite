import Foundation.GaussianClosedChainRule
import Foundation.BrownianTanakaApproximation
import Foundation.IBMFourierClockMeanRegularity

/-! A nonsmooth reflected damping rule in the ORIGINAL closed Gaussian graph.
The zero-level cusp is handled by actual strong graph approximation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianReflectedDampingGraph
open InfiniteGaussian SmoothAbsoluteApproximation GaussianClosedChainRule

def value (c x : ℝ) : ℝ := Real.exp (-c*|x|)
def coefficient (c x : ℝ) : ℝ := -c*value c x*BrownianSignIntegral.signum x
def smoothValue (c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-c*radius (RealSteklovApprox.width n) x)
def smoothCoefficient (c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  -c*smoothValue c n x*slope (RealSteklovApprox.width n) x

theorem value_bound {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : ‖value c x‖ ≤ 1 := by
  rw [value,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (abs_nonneg _))

theorem smooth_bound {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : ℝ) : ‖smoothValue c n x‖ ≤ 1 := by
  rw [smoothValue,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc)
    (radius_pos (RealSteklovApprox.width_pos n) x).le

theorem smooth_hasDerivAt (c : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (smoothValue c n) (smoothCoefficient c n x) x := by
  have h := ((radius_hasDerivAt (RealSteklovApprox.width_pos n) x).const_mul (-c)).exp
  convert h using 1 <;> first | rfl | dsimp [smoothCoefficient,smoothValue]; ring

theorem smoothCoefficient_continuous (c : ℝ) (n : ℕ) : Continuous (smoothCoefficient c n) := by
  unfold smoothCoefficient smoothValue
  exact (continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul (radius_smooth (RealSteklovApprox.width_pos n) 0).continuous))).mul
      (slopeLip (RealSteklovApprox.width_pos n)).continuous

theorem smoothCoefficient_bound {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : ℝ) :
    ‖smoothCoefficient c n x‖ ≤ c := by
  rw [smoothCoefficient,norm_mul,norm_mul,norm_neg,Real.norm_of_nonneg hc]
  have hb := mul_le_mul (smooth_bound hc n x) (slope_bound (RealSteklovApprox.width_pos n) x)
    (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  nlinarith [mul_le_mul_of_nonneg_left hb hc]

theorem coefficient_bound {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : ‖coefficient c x‖ ≤ c := by
  rw [coefficient,norm_mul,norm_mul,norm_neg,Real.norm_of_nonneg hc]
  have hb := mul_le_mul (value_bound hc x) (BrownianSignIntegral.signum_bound x)
    (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  nlinarith [mul_le_mul_of_nonneg_left hb hc]

theorem smoothValue_tendsto (c x : ℝ) :
    Tendsto (fun n => smoothValue c n x) atTop (𝓝 (value c x)) := by
  have hr : Tendsto (fun n => radius (RealSteklovApprox.width n) x) atTop (𝓝 |x|) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => uniform_error (RealSteklovApprox.width_pos n) x)
      IBMIntrinsicChainApproximation.width_tendsto
  exact Real.continuous_exp.continuousAt.tendsto.comp (hr.const_mul (-c))

theorem smoothCoefficient_tendsto (c x : ℝ) :
    Tendsto (fun n => smoothCoefficient c n x) atTop (𝓝 (coefficient c x)) :=
  ((smoothValue_tendsto c x).const_mul (-c)).mul (BrownianTanakaApproximation.slope_tendsto_sign x)

theorem closed_graph {c : ℝ} (hc : 0 ≤ c) (f : GaussianL2) (g : GaussianVectorL2)
    (hfg : (f,g) ∈ closedCylindricalDerivative.graph) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F,G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun X => value c (f X)) ∧
      G =ᵐ[gaussianProduct] (fun X => coefficient c (f X) • g X) ∧ ‖G‖ ≤ c*‖g‖ := by
  choose Fn Gn hn hFn hGn using fun n => bounded_closed_chain_graph f g hfg
    (smoothValue c n) (smoothCoefficient c n) (smooth_hasDerivAt c n)
    (smoothCoefficient_continuous c n) 1 c (smooth_bound hc n) (smoothCoefficient_bound hc n)
  have hf : MemLp (fun X => value c (f X)) 2 gaussianProduct :=
    MemLp.of_bound (by unfold value; fun_prop) 1 (Eventually.of_forall (fun X => value_bound hc (f X)))
  let F : GaussianL2 := hf.toLp _
  have hF : F =ᵐ[gaussianProduct] fun X => value c (f X) := hf.coeFn_toLp
  have hFt : Tendsto Fn atTop (𝓝 F) := by
    apply BochnerL2Approximation.tendsto_of_dominated _ _ gaussianOne
    · intro n
      filter_upwards [hFn n,gaussianOne_coeFn] with X hn h1
      rw [hn,h1,norm_one]
      exact smooth_bound hc n _
    · filter_upwards [hF,gaussianOne_coeFn] with X hF h1
      rw [hF,h1,norm_one]
      exact value_bound hc _
    · filter_upwards [hF,ae_all_iff.mpr hFn] with X hF hn
      simpa only [hn,hF] using smoothValue_tendsto c (f X)
  let a : ℕ → SampleSpace → ℝ := fun n X => smoothCoefficient c n (f X)
  let b : SampleSpace → ℝ := fun X => coefficient c (f X)
  have ha : ∀ n, AEStronglyMeasurable (a n) gaussianProduct := fun n =>
    (smoothCoefficient_continuous c n).comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)
  have hb : AEStronglyMeasurable b gaussianProduct := by
    dsimp [b,coefficient,value]
    exact ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_abs))).comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).mul
        ((BrownianSignIntegral.signum_measurable.comp (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable)
  have hba : ∀ n, ∀ᵐ X ∂gaussianProduct, ‖a n X‖ ≤ c :=
    fun n => Eventually.of_forall fun X => smoothCoefficient_bound hc n (f X)
  have hbb : ∀ᵐ X ∂gaussianProduct, ‖b X‖ ≤ c :=
    Eventually.of_forall fun X => coefficient_bound hc (f X)
  let G := multiplier b hb c hbb g
  have hGt : Tendsto Gn atTop (𝓝 G) := by
    have he (n : ℕ) : Gn n = multiplier (a n) (ha n) c (hba n) g :=
      Lp.ext ((hGn n).trans (multiplier_ae (a n) (ha n) c (hba n) g).symm)
    rw [show Gn = (fun n => multiplier (a n) (ha n) c (hba n) g) from funext he]
    exact multiplier_tendsto_fixed a b ha hb c hc hba hbb
      (Eventually.of_forall fun X => smoothCoefficient_tendsto c (f X)) g
  refine ⟨F,G,closedCylindricalDerivative_isClosed.mem_of_tendsto
    (hFt.prodMk_nhds hGt) (Eventually.of_forall hn),hF,multiplier_ae b hb c hbb g,?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplier_ae b hb c hbb g,hbb] with X hG hbX
  rw [hG,norm_smul]
  exact mul_le_mul_of_nonneg_right hbX (norm_nonneg _)

end OperatorDerivativeRewrite.Foundation.GaussianReflectedDampingGraph
