import Foundation.GaussianReflectedDampingGraph
import Foundation.IBMIntrinsicChainApproximation

/-! Absolute value and minimum in the ORIGINAL closed Gaussian graph, including
zero and collision levels. Bounded sine/radius approximants are reused. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianAbsoluteMinimumGraph
open InfiniteGaussian SmoothAbsoluteApproximation GaussianClosedChainRule
open IBMIntrinsicChainApproximation

def approx (n : ℕ) : ℝ → ℝ := approximant (radius (width n)) n
def approxSlope (n : ℕ) : ℝ → ℝ := approximantDerivative (radius (width n)) (slope (width n)) n

theorem radius_limit (x : ℝ) : Tendsto (fun n => radius (width n) x) atTop (𝓝 |x|) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => uniform_error (RealSteklovApprox.width_pos n) x) width_tendsto

theorem approx_limit (x : ℝ) : Tendsto (fun n => approx n x) atTop (𝓝 |x|) := by
  have hm := width_tendsto.mul (radius_limit x)
  have hs := Real.continuous_sinc.continuousAt.tendsto.comp hm
  have h := (radius_limit x).mul hs
  simpa only [zero_mul,Real.sinc_zero,mul_one,approx,approximant,clip_sinc,Function.comp_def] using h

theorem approxSlope_limit (x : ℝ) :
    Tendsto (fun n => approxSlope n x) atTop (𝓝 (BrownianSignIntegral.signum x)) := by
  have h := (Real.continuous_cos.continuousAt.tendsto.comp
    (width_tendsto.mul (radius_limit x))).mul (BrownianTanakaApproximation.slope_tendsto_sign x)
  simpa only [approxSlope,approximantDerivative,zero_mul,Real.cos_zero,one_mul,Function.comp_def] using h

theorem approx_domination (n : ℕ) (x : ℝ) : ‖approx n x‖ ≤ |x|+1 := by
  have hw : width n ≤ 1 := by
    dsimp [width,RealSteklovApprox.width]
    apply (div_le_one (by positivity : (0:ℝ) < (n:ℝ)+1)).mpr
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hr := radius_le_abs_add (RealSteklovApprox.width_pos n) x
  have h := clip_domination n (radius (width n) x)
  rw [Real.norm_of_nonneg (radius_pos (RealSteklovApprox.width_pos n) x).le] at h
  exact h.trans (by linarith)

theorem absolute_graph (f : GaussianL2) (g : GaussianVectorL2)
    (hfg : (f,g) ∈ closedCylindricalDerivative.graph) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F,G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun X => |f X|) ∧
      G =ᵐ[gaussianProduct] (fun X => BrownianSignIntegral.signum (f X) • g X) ∧ ‖G‖ ≤ ‖g‖ := by
  choose Fn Gn hn hFn hGn using fun n => bounded_closed_chain_graph f g hfg
    (approx n) (approxSlope n)
    (approximant_hasDerivAt _ _ (radius_hasDerivAt (RealSteklovApprox.width_pos n)) n)
    (approximantDerivative_continuous _ _ (radius_smooth (RealSteklovApprox.width_pos n) 0).continuous
      (slopeLip (RealSteklovApprox.width_pos n)).continuous n)
    ((width n)⁻¹) 1 (fun x => clip_bound n (radius (width n) x)) (approximantDerivative_bound _ _ 1
      (slope_bound (RealSteklovApprox.width_pos n)) n)
  let F : GaussianL2 := (Lp.memLp f).norm.toLp _
  have hF : F =ᵐ[gaussianProduct] (fun X => |f X|) := by
    change (Lp.memLp f).norm.toLp (fun X => ‖f X‖) =ᵐ[gaussianProduct] _
    filter_upwards [(Lp.memLp f).norm.coeFn_toLp] with X hX
    exact hX.trans (Real.norm_eq_abs _)
  let m : GaussianL2 := F+gaussianOne
  have hm : m =ᵐ[gaussianProduct] (fun X => |f X|+1) := by
    filter_upwards [Lp.coeFn_add F gaussianOne,hF,gaussianOne_coeFn] with X hm hf h1
    change m X = _ at hm
    rw [hm,Pi.add_apply,hf,h1]
  have hFt : Tendsto Fn atTop (𝓝 F) := by
    apply BochnerL2Approximation.tendsto_of_dominated _ _ m
    · intro n
      filter_upwards [hFn n,hm] with X hn hm
      rw [hn,hm,Real.norm_of_nonneg (by positivity : 0 ≤ |f X|+1)]
      exact approx_domination n (f X)
    · filter_upwards [hF,hm] with X hf hm
      rw [hf,hm]
      simp only [Real.norm_eq_abs,abs_abs]
      rw [abs_of_nonneg (by positivity : 0 ≤ |f X|+1)]
      linarith
    · filter_upwards [hF,ae_all_iff.mpr hFn] with X hf hn
      simpa only [hn,hf] using approx_limit (f X)
  let a : ℕ → SampleSpace → ℝ := fun n X => approxSlope n (f X)
  let b : SampleSpace → ℝ := fun X => BrownianSignIntegral.signum (f X)
  have ha : ∀ n, AEStronglyMeasurable (a n) gaussianProduct := fun n =>
    (approximantDerivative_continuous _ _ (radius_smooth (RealSteklovApprox.width_pos n) 0).continuous
      (slopeLip (RealSteklovApprox.width_pos n)).continuous n).comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)
  have hb : AEStronglyMeasurable b gaussianProduct :=
    (BrownianSignIntegral.signum_measurable.comp (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable
  have hba : ∀ n, ∀ᵐ X ∂gaussianProduct, ‖a n X‖ ≤ (1:ℝ) := fun n =>
    Eventually.of_forall fun X => approximantDerivative_bound _ _ 1
      (slope_bound (RealSteklovApprox.width_pos n)) n (f X)
  have hbb : ∀ᵐ X ∂gaussianProduct, ‖b X‖ ≤ (1:ℝ) :=
    Eventually.of_forall fun X => BrownianSignIntegral.signum_bound (f X)
  let G := multiplier b hb 1 hbb g
  have hGt : Tendsto Gn atTop (𝓝 G) := by
    have he (n : ℕ) : Gn n = multiplier (a n) (ha n) 1 (hba n) g :=
      Lp.ext ((hGn n).trans (multiplier_ae (a n) (ha n) 1 (hba n) g).symm)
    rw [show Gn = (fun n => multiplier (a n) (ha n) 1 (hba n) g) from funext he]
    exact multiplier_tendsto_fixed a b ha hb 1 (by norm_num) hba hbb
      (Eventually.of_forall fun X => approxSlope_limit (f X)) g
  refine ⟨F,G,closedCylindricalDerivative_isClosed.mem_of_tendsto
    (hFt.prodMk_nhds hGt) (Eventually.of_forall hn),hF,multiplier_ae b hb 1 hbb g,?_⟩
  have hh : ‖G‖ ≤ 1*‖g‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [multiplier_ae b hb 1 hbb g,hbb] with X hG hbX
    rw [hG,norm_smul]
    exact mul_le_mul_of_nonneg_right hbX (norm_nonneg _)
  simpa only [one_mul] using hh

theorem minimum_graph (f h : GaussianL2) (g k : GaussianVectorL2)
    (hf : (f,g) ∈ closedCylindricalDerivative.graph)
    (hh : (h,k) ∈ closedCylindricalDerivative.graph) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F,G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun X => min (f X) (h X)) ∧
      G =ᵐ[gaussianProduct] (fun X => (1/2:ℝ) •
        (g X+k X-BrownianSignIntegral.signum (f X-h X) • (g X-k X))) ∧ ‖G‖ ≤ ‖g‖+‖k‖ := by
  obtain ⟨A,B,hab,ha,hb,hbn⟩ := absolute_graph (f-h) (g-k)
    (closedCylindricalDerivative.graph.sub_mem hf hh)
  let F := (1/2:ℝ) • (f+h-A)
  let G := (1/2:ℝ) • (g+k-B)
  refine ⟨F,G,closedCylindricalDerivative.graph.smul_mem (1/2:ℝ)
    (closedCylindricalDerivative.graph.sub_mem (closedCylindricalDerivative.graph.add_mem hf hh) hab),?_,?_,?_⟩
  · filter_upwards [Lp.coeFn_smul (1/2:ℝ) (f+h-A),Lp.coeFn_sub (f+h) A,
      Lp.coeFn_add f h,ha,Lp.coeFn_sub f h] with X hs hd hp ha he
    change ((1/2:ℝ) • (f+h-A)) X = _
    rw [hs,Pi.smul_apply,hd,Pi.sub_apply,hp,Pi.add_apply,ha,he,Pi.sub_apply]
    simp only [smul_eq_mul]
    rcases le_total (f X) (h X) with hl | hl
    · rw [min_eq_left hl,abs_of_nonpos (sub_nonpos.mpr hl)]; ring
    · rw [min_eq_right hl,abs_of_nonneg (sub_nonneg.mpr hl)]; ring
  · filter_upwards [Lp.coeFn_smul (1/2:ℝ) (g+k-B),Lp.coeFn_sub (g+k) B,
      Lp.coeFn_add g k,hb,Lp.coeFn_sub f h,Lp.coeFn_sub g k] with X hs hd hp hb he hk
    change ((1/2:ℝ) • (g+k-B)) X = _
    rw [hs,Pi.smul_apply,hd,Pi.sub_apply,hp,Pi.add_apply,hb,he,hk,Pi.sub_apply,Pi.sub_apply]
  · change ‖(1/2:ℝ) • (g+k-B)‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    have h1 := norm_sub_le (g+k) B
    have h2 := norm_add_le g k
    have h3 := norm_sub_le g k
    linarith

end OperatorDerivativeRewrite.Foundation.GaussianAbsoluteMinimumGraph
