import Foundation.GaussianBoundedHeatDerivative
import Foundation.IBMSchwartzHeatPredictable

/-! The finite-energy nonlinear score is the genuine spatial derivative of
the ACTUAL Gaussian Bochner heat expectation and of the specified whole-clock
conditional-mean version. Native terminal reconstruction remains separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatDerivative
open InfiniteGaussian IBMSchwartzHalfHolderHeat GaussianCore
attribute [local irreducible] curve GaussianHalfHolderScore.score GaussianBoundedHeatDerivative.mean

def heatMean (g : SchwartzMap ℝ ℝ) (a b v : ℝ) : InfiniteGaussian.GaussianL2 :=
  GaussianBoundedHeatDerivative.mean (curve g a) b (Real.sqrt v)

theorem heatMean_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => heatMean g a p.1 p.2) :=
  (GaussianBoundedHeatDerivative.mean_continuous (curve g a) (curve_continuous g a)
    (SchwartzMap.seminorm ℝ 0 0 g) (curve_bound g a)).comp
      (continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd))

theorem heatMean_zero (g : SchwartzMap ℝ ℝ) (a b : ℝ) :
    heatMean g a b 0 = curve g a b := by
  simp [heatMean,GaussianBoundedHeatDerivative.mean]

theorem heatMean_hasDerivAt (g : SchwartzMap ℝ ℝ) (a b v : ℝ) (hv : 0 < v) :
    HasDerivAt (fun x => heatMean g a x v) (heatScore g a b v) b :=
  GaussianBoundedHeatDerivative.mean_hasDerivAt (curve g a) (curve_continuous g a)
    (SchwartzMap.seminorm ℝ 0 0 g) (by positivity) (curve_bound g a) b (Real.sqrt v)
      (ne_of_gt (Real.sqrt_pos.mpr hv))

theorem heatMean_gaussian (g : SchwartzMap ℝ ℝ) (a b : ℝ) (v : ℝ≥0) :
    heatMean g a b v = ∫ y, curve g a (b+y) ∂gaussianReal 0 v := by
  have hl : HasLaw (fun z : ℝ => Real.sqrt (v : ℝ)*z) (gaussianReal 0 v) γ := by
    refine ⟨by fun_prop,?_⟩
    simp [γ,gaussianReal_map_const_mul,Real.sq_sqrt v.coe_nonneg]
  have hf : AEStronglyMeasurable (fun y : ℝ => curve g a (b+y)) (gaussianReal 0 v) :=
    ((curve_continuous g a).comp
      ((continuous_const : Continuous (fun _ : ℝ => b)).add continuous_id)).aestronglyMeasurable
  have he := hl.integral_comp hf
  simpa only [heatMean,GaussianBoundedHeatDerivative.mean,Function.comp_def] using he

theorem conditional_value (g : SchwartzMap ℝ ℝ) (a : ℝ) (S T : ℝ≥0) (hST : S ≤ T) :
    gaussianProduct[fun Y => curve g a (GaussianTimeProcess.process T Y) |
      GaussianTimeProcess.naturalFiltration S] =ᵐ[gaussianProduct] fun Y =>
      heatMean g a (GaussianTimeProcess.process S Y) ((T : ℝ)-(S : ℝ)) := by
  apply (IBMSchwartzHalfHolderHeat.conditional_transition g a S T hST).trans
  exact Filter.Eventually.of_forall fun Y => by
    rw [← NNReal.coe_sub hST]
    exact (heatMean_gaussian g a _ (T-S)).symm

theorem conditional_gradient (g : SchwartzMap ℝ ℝ) (a : ℝ) (S T : ℝ≥0)
    (hST : S < T) (Y : SampleSpace) :
    HasDerivAt (fun b => heatMean g a b ((T : ℝ)-(S : ℝ)))
      (heatScore g a (GaussianTimeProcess.process S Y) ((T : ℝ)-(S : ℝ)))
      (GaussianTimeProcess.process S Y) :=
  heatMean_hasDerivAt g a (GaussianTimeProcess.process S Y) _ (sub_pos.mpr hST)

def heatProcess (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (Y : SampleSpace)
    (s : ℝ) : InfiniteGaussian.GaussianL2 :=
  heatMean g a (IBMConstructedSources.clockPath Y s.toNNReal) ((T : ℝ)-s)

theorem heatProcess_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (Y : SampleSpace) : Continuous (heatProcess g a T Y) :=
  (heatMean_continuous g a).comp
    (((IBMConstructedSources.clockPath Y).continuous.comp continuous_real_toNNReal).prodMk
      (continuous_const.sub continuous_id))

theorem heatProcess_terminal (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (Y : SampleSpace) :
    heatProcess g a T Y T = curve g a (IBMConstructedSources.clockPath Y T) := by
  simp [heatProcess,heatMean_zero]

theorem actual_raw_derivative (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (s : ℝ) (hs : s < T) (Y : SampleSpace) :
    HasDerivAt (fun b => heatMean g a b ((T : ℝ)-s))
      (IBMSchwartzHeatPredictable.raw g a T (s,Y))
      (IBMConstructedSources.clockPath Y s.toNNReal) :=
  heatMean_hasDerivAt g a _ _ (sub_pos.mpr hs)

theorem conditional_path_version (g : SchwartzMap ℝ ℝ) (a : ℝ) (S T : ℝ≥0) (hST : S ≤ T) :
    gaussianProduct[fun Y => curve g a (GaussianTimeProcess.process T Y) |
      GaussianTimeProcess.naturalFiltration S] =ᵐ[gaussianProduct]
      fun Y => heatProcess g a T Y S := by
  apply (conditional_value g a S T hST).trans
  filter_upwards [IBMConstructedSources.clockPath_coordinate_ae S] with Y hY
  simp only [heatProcess,Real.toNNReal_coe,hY]

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatDerivative
