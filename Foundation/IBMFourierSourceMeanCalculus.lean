import Foundation.IBMBoundedGaussianMeanDerivative
import Foundation.IBMFourierCylinderSeries
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Actual source means of the existing Fourier cylinders, differentiated on
finite families of source Hilbert directions. This is not physical-time Ito. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFourierSourceMeanCalculus
open InfiniteGaussian IBMFourierRidgeCoefficients IBMBoundedGaussianMeanDerivative
open IBMTimeAveragedObservable IBMIntrinsicOperators
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
variable {ι : Type*} [Fintype ι]

def row (b : ι → ℝ) : (ι → CoefficientSpace) →L[ℝ] CoefficientSpace :=
  ∑ i, b i • ContinuousLinearMap.proj i

theorem row_apply (b : ι → ℝ) (U : ι → CoefficientSpace) : row b U = ∑ i, b i • U i := by
  simp only [row,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply]

theorem row_bound (b : ι → ℝ) : ‖row b‖ ≤ IBMUniformRidgeNativeBounds.amplitude b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => abs_nonneg (b i))
  intro U
  rw [row_apply]
  calc
    _ ≤ ∑ i, ‖b i • U i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |b i| * ‖U‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm U i) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

variable (a : ℕ → ι → ℝ) (β w : ℕ → ℝ)

def meanTerm (k : ℕ) (U : ι → CoefficientSpace) : ℝ :=
  w k*mean (mode (β k)) (row (a k) U)

def sourceMean (U : ι → CoefficientSpace) : ℝ := ∑' k, meanTerm a β w k U

def derivativeTerm (k : ℕ) (U : ι → CoefficientSpace) : (ι → CoefficientSpace) →L[ℝ] ℝ :=
  w k • (derivative (mode (β k)) (row (a k) U)).comp (row (a k))

def sourceDerivative (U : ι → CoefficientSpace) : (ι → CoefficientSpace) →L[ℝ] ℝ :=
  ∑' k, derivativeTerm a β w k U

def firstCost (k : ℕ) : ℝ := |w k| * IBMUniformRidgeNativeBounds.amplitude (a k)

theorem meanTerm_bound (k : ℕ) (U : ι → CoefficientSpace) : ‖meanTerm a β w k U‖ ≤ |w k| := by
  have hb : ‖mean (mode (β k)) (row (a k) U)‖ ≤ 1 :=
    by simpa [mean] using
      norm_integral_le_of_norm_le_const (μ := gaussianProduct)
        (Eventually.of_forall fun X => mode_bound (β k) (firstChaosEmbedding (row (a k) U) X))
  rw [meanTerm,norm_mul,Real.norm_eq_abs]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (abs_nonneg _)

theorem derivativeTerm_bound (k : ℕ) (U : ι → CoefficientSpace) :
    ‖derivativeTerm a β w k U‖ ≤ firstCost a w k := by
  rw [derivativeTerm,norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hd := derivative_bound (mode_smooth (β k)) (mode_first_bound (β k))
    (mode_second_bound (β k)) (row (a k) U)
  exact (mul_le_mul hd (row_bound (a k)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem firstCost_summable (hv : Summable (fun k => |w k|))
    (hc : Summable (IBMFourierCylinderSeries.curvatureCost a w)) : Summable (firstCost a w) := by
  apply (hv.add hc).of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _)
    (Finset.sum_nonneg fun i _ => abs_nonneg _))
  intro k
  have ht : IBMUniformRidgeNativeBounds.amplitude (a k) ≤
      1+(IBMUniformRidgeNativeBounds.amplitude (a k))^2 := by
    nlinarith [sq_nonneg (IBMUniformRidgeNativeBounds.amplitude (a k)-1/2)]
  have hb := mul_le_mul_of_nonneg_left ht (abs_nonneg (w k))
  simp only [firstCost,IBMFourierCylinderSeries.curvatureCost,
    IBMUniformRidgeNativeBounds.amplitude,mul_add,mul_one] at hb ⊢
  exact hb

theorem meanTerm_hasFDerivAt (k : ℕ) (U : ι → CoefficientSpace) :
    HasFDerivAt (meanTerm a β w k) (derivativeTerm a β w k U) U := by
  exact ((mean_hasFDerivAt (mode_smooth (β k)) (mode_bound (β k))
    (mode_first_bound (β k)) (mode_second_bound (β k)) (row (a k) U)).comp U
      (row (a k)).hasFDerivAt).const_mul (w k)

theorem sourceMean_hasFDerivAt (hv : Summable (fun k => |w k|))
    (hc : Summable (IBMFourierCylinderSeries.curvatureCost a w)) (U : ι → CoefficientSpace) :
    HasFDerivAt (sourceMean a β w) (sourceDerivative a β w U) U :=
  hasFDerivAt_tsum (firstCost_summable a w hv hc) (meanTerm_hasFDerivAt a β w)
    (derivativeTerm_bound a β w)
    (hv.of_norm_bounded (fun k => meanTerm_bound a β w k U)) U

theorem derivativeTerm_formula (k : ℕ) (U V : ι → CoefficientSpace) :
    derivativeTerm a β w k U V =
      -(w k)*Real.cos (β k)*Real.exp (-‖row (a k) U‖^2/2)*
        inner ℝ (row (a k) U) (row (a k) V) := by
  rw [derivativeTerm,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    derivative_coefficient,coefficient_formula]
  simp only [smul_eq_mul]
  ring

theorem sourceMean_actual (hv : Summable (fun k => |w k|)) (U : ι → CoefficientSpace) :
    sourceMean a β w U = ∫ X, IBMFourierCylinderSeries.value a β w
      (fun i => firstChaosEmbedding (U i) X) ∂gaussianProduct := by
  let f : ℕ → SampleSpace → ℝ := fun k X => IBMFourierCylinderSeries.valueTerm a β w k
    (fun i => firstChaosEmbedding (U i) X)
  have hsum := hasSum_integral_of_dominated_convergence (fun k (_ : SampleSpace) => |w k|)
    (F := f) (fun k => by dsimp [f,IBMFourierCylinderSeries.valueTerm,mode]; fun_prop)
    (fun k => Eventually.of_forall fun X => IBMFourierCylinderSeries.valueTerm_bound a β w k _)
    (Eventually.of_forall fun _ => hv) (integrable_const _)
    (Eventually.of_forall fun X =>
      (hv.of_norm_bounded fun k => IBMFourierCylinderSeries.valueTerm_bound a β w k _).hasSum)
  have he (k : ℕ) : (∫ X, f k X ∂gaussianProduct) = meanTerm a β w k U := by
    change (∫ X, w k*mode (β k) (∑ i, a k i*firstChaosEmbedding (U i) X) ∂gaussianProduct) = _
    rw [integral_const_mul]
    apply congrArg (fun z => w k*z)
    apply integral_congr_ae
    filter_upwards [firstChaos_linearCombination_ae U (a k)] with X hX
    rw [← hX,← row_apply]
  change (∑' k, meanTerm a β w k U) = ∫ X,
    ∑' k, IBMFourierCylinderSeries.valueTerm a β w k
      (fun i => firstChaosEmbedding (U i) X) ∂gaussianProduct
  simpa only [he] using hsum.tsum_eq

def clockMean (r : ι → ℝ≥0) : GaussianL2 :=
  (innerSL ℝ gaussianOne).compLpL 2 gaussianProduct
    (sourceUnitary (IBMFourierCylinderSeries.observation a r β w : JointL2))

theorem clockMean_actual (r : ι → ℝ≥0) (hv : Summable (fun k => |w k|)) :
    clockMean a β w r =ᵐ[gaussianProduct]
      fun Y => sourceMean a β w (fun i => IBMRawStepSources.clockDirection (r i) Y) := by
  let Q : JointL2 := (IBMFourierCylinderSeries.observation a r β w : JointL2)
  have hu := ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct
    (ProductL2Curry.swap gaussianProduct gaussianProduct Q)
  have hs := ae_ae_of_ae_prod (ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct Q)
  have hq := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    (IBMFourierCylinderSeries.observation_actual a r β w hv))
  filter_upwards [(innerSL ℝ gaussianOne).coeFn_compLpL (sourceUnitary Q),hu,hs,hq,
    ae_all_iff.mpr fun i => IBMUnmollifiedSourceDerivative.actual_section_ae (r i)]
      with Y hm hu hs hq hi
  change clockMean a β w r Y = inner ℝ gaussianOne (sourceUnitary Q Y) at hm
  rw [hm,gaussianOne_inner_eq_integral,sourceMean_actual a β w hv]
  apply integral_congr_ae
  filter_upwards [hu,hs,hq,ae_all_iff.mpr hi] with X hu hs hq hi
  have hu' : sourceUnitary Q Y X = Q (X,Y) := hu.trans hs
  have hq' : Q (X,Y) = IBMFourierCylinderSeries.value a β w
      (fun i => IBMConstructedSources.ibmValue (r i) (X,Y)) := hq
  rw [hu',hq']
  apply congrArg (IBMFourierCylinderSeries.value a β w)
  funext i
  exact hi i

end OperatorDerivativeRewrite.Foundation.IBMFourierSourceMeanCalculus
