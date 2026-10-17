import Foundation.FractionalDyadicControl

/-! A measurable continuous-path realization of fractional Brownian motion for
every 0 < H < 1, on the original countable Gaussian probability space. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ContinuousFractionalBrownian
open InfiniteGaussian FractionalDyadicControl
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable
attribute [local irreducible] GaussianContinuousModification.field IBMDyadicExtension.field
set_option backward.isDefEq.respectTransparency false

variable (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)

def twoSidedPath : SampleSpace → C(ℝ, ℝ) :=
  GaussianContinuousModification.path (value H hH0 hH1) (rate H)
    (rate_pos H).le (rate_lt_one H hH0)

theorem twoSidedPath_measurable : Measurable (twoSidedPath H hH0 hH1) :=
  GaussianContinuousModification.path_measurable _ _ _ _

theorem twoSidedPath_coordinate_ae (r : ℝ) :
    (fun ω => twoSidedPath H hH0 hH1 ω r) =ᵐ[gaussianProduct] value H hH0 hH1 r :=
  GaussianContinuousModification.field_coordinate_ae _ _ _ _
    (value_continuous H hH0 hH1) (good H hH0 hH1) r

def path (ω : SampleSpace) : C(ℝ≥0, ℝ) :=
  ⟨fun t => twoSidedPath H hH0 hH1 ω t,
    (twoSidedPath H hH0 hH1 ω).continuous.comp NNReal.continuous_coe⟩

def process (t : ℝ≥0) (ω : SampleSpace) : ℝ := path H hH0 hH1 ω t

theorem path_measurable : Measurable (path H hH0 hH1) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (ContinuousMap.measurable_eval (t : ℝ)).comp (twoSidedPath_measurable H hH0 hH1)

theorem process_jointly_measurable :
    Measurable (fun z : ℝ≥0 × SampleSpace => process H hH0 hH1 z.1 z.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun ω => (path H hH0 hH1 ω).continuous)
    (fun t => (ContinuousMap.measurable_eval t).comp (path_measurable H hH0 hH1))

theorem process_continuous (ω : SampleSpace) : Continuous (fun t => process H hH0 hH1 t ω) :=
  (path H hH0 hH1 ω).continuous

theorem process_coordinate_ae (t : ℝ≥0) :
    process H hH0 hH1 t =ᵐ[gaussianProduct] FractionalGaussianProcess.process H hH0 hH1 t :=
  twoSidedPath_coordinate_ae H hH0 hH1 t

theorem process_isGaussianProcess : IsGaussianProcess (process H hH0 hH1) gaussianProduct :=
  (FractionalGaussianProcess.process_isGaussianProcess H hH0 hH1).congr
    (fun t => (process_coordinate_ae H hH0 hH1 t).symm)

theorem process_centered (t : ℝ≥0) :
    (∫ ω, process H hH0 hH1 t ω ∂gaussianProduct) = 0 := by
  rw [integral_congr_ae (process_coordinate_ae H hH0 hH1 t)]
  exact FractionalGaussianProcess.process_centered H hH0 hH1 t

theorem process_covariance (s t : ℝ≥0) :
    cov[process H hH0 hH1 s, process H hH0 hH1 t; gaussianProduct] =
      ((s : ℝ)^(2*H)+(t : ℝ)^(2*H)-|(t : ℝ)-s|^(2*H))/2 := by
  have hs := process_coordinate_ae H hH0 hH1 s
  have ht := process_coordinate_ae H hH0 hH1 t
  have hEs := integral_congr_ae hs
  have hEt := integral_congr_ae ht
  calc
    _ = cov[FractionalGaussianProcess.process H hH0 hH1 s,
        FractionalGaussianProcess.process H hH0 hH1 t; gaussianProduct] := by
      unfold covariance
      apply integral_congr_ae
      filter_upwards [hs,ht] with ω hωs hωt
      rw [hωs,hωt,hEs,hEt]
    _ = _ := FractionalGaussianProcess.process_covariance H hH0 hH1 s t

theorem process_law (t : ℝ≥0) :
    gaussianProduct.map (process H hH0 hH1 t) =
      gaussianReal 0 ⟨(t : ℝ)^(2*H), Real.rpow_nonneg t.coe_nonneg _⟩ := by
  rw [Measure.map_congr (process_coordinate_ae H hH0 hH1 t)]
  exact FractionalGaussianProcess.process_law H hH0 hH1 t

theorem process_zero_ae : process H hH0 hH1 0 =ᵐ[gaussianProduct] 0 := by
  apply (process_coordinate_ae H hH0 hH1 0).trans
  have he := FractionalGaussianProcess.value_zero H hH0 hH1
  exact (Lp.ext_iff.mp he).trans (Lp.coeFn_zero ℝ 2 gaussianProduct)

theorem closed_derivative_graph (t : ℝ≥0) :
    ((FractionalGaussianProcess.process_memLp H hH0 hH1 t 2 (by simp)).ae_eq
      (process_coordinate_ae H hH0 hH1 t).symm |>.toLp (process H hH0 hH1 t),
      scalarTensor (FractionalGaussianProcess.direction H hH0 hH1 t)
        gaussianOne) ∈ closedCylindricalDerivative.graph := by
  have he : ((FractionalGaussianProcess.process_memLp H hH0 hH1 t 2 (by simp)).ae_eq
      (process_coordinate_ae H hH0 hH1 t).symm |>.toLp (process H hH0 hH1 t)) =
      FractionalGaussianProcess.value H hH0 hH1 t := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (process_coordinate_ae H hH0 hH1 t)
  rw [he]
  exact FractionalGaussianProcess.value_derivative_graph H hH0 hH1 t

end OperatorDerivativeRewrite.Foundation.ContinuousFractionalBrownian
