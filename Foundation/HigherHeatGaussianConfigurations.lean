import Foundation.HigherHeatGaussianLaw
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual order-two finite increment and position laws are Gaussian probability laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatGaussianConfigurations
open HigherHeatSignedLaws HigherHeatCylinderFourier HigherHeatBlockCoarsening
open SignedDensityIntegral SignedFourierUniqueness HigherHeatGaussianLaw

variable {ι : Type*} [Fintype ι]

def gaussianIncrements (t : ι → ℝ≥0) : Measure (ι → ℝ) :=
  Measure.pi (fun i => gaussianReal 0 (2*t i))

instance gaussianIncrements_probability (t : ι → ℝ≥0) : IsProbabilityMeasure (gaussianIncrements t) := by
  unfold gaussianIncrements
  infer_instance

theorem phase_product (ξ x : ι → ℝ) :
    configurationPhase ξ x=∏ i, phase (ξ i) (x i) := by
  unfold configurationPhase
  rw [← Finset.sum_neg_distrib,character_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg (fun r : ℝ => (Real.fourierChar r : ℂ))
    (show -(ξ i*x i)=-(x i*ξ i) by ring)

theorem gaussian_phase_integral (T : ℝ≥0) (hT : 0 < T) (ξ : ℝ) :
    (∫ x : ℝ, phase ξ x ∂gaussianReal 0 (2*T))=HigherHeatL2.symbol 1 T ξ := by
  have h : (∫ᵛ x : ℝ, phase ξ x ∂<•HigherHeatSignedLaws.law 1 (by norm_num) T hT)=
      HigherHeatL2.symbol 1 T ξ := by
    unfold HigherHeatSignedLaws.law
    rw [integral_density volume _ (realKernel 1 (by norm_num) T hT).integrable
      (realKernel 1 (by norm_num) T hT).continuous.measurable (phase ξ) (phase_continuous ξ).measurable
      1 (fun x => (phase_norm ξ x).le)]
    convert kernel_fourier 1 (by norm_num) T hT ξ using 1
    congr 1
    funext x
    rw [Complex.real_smul]
    ring
  rw [gaussian_law] at h
  simpa only [VectorMeasure.integral_toSignedMeasure] using h

theorem increment_gaussian (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) :
    incrementLaw 1 (by norm_num) t ht=(gaussianIncrements t).toSignedMeasure := by
  apply finite_signed_ext
  intro ξ
  rw [← identity_law 1 (by norm_num) t ht,configurationLaw_fourier,identity_dual,
    VectorMeasure.integral_toSignedMeasure]
  simp_rw [phase_product]
  change (∏ i, HigherHeatL2.symbol 1 (t i) (ξ i)) =
    ∫ x : ι → ℝ, ∏ i, phase (ξ i) (x i) ∂Measure.pi (fun i => gaussianReal 0 (2*t i))
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => phase (ξ i) x)]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussian_phase_integral (t i) (ht i) (ξ i)).symm

theorem map_toSigned {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → Y) (hf : Measurable f) :
    μ.toSignedMeasure.map f=(μ.map f).toSignedMeasure := by
  ext A hA
  rw [VectorMeasure.map_apply _ hf hA,Measure.toSignedMeasure_apply_measurable (hf hA),
    Measure.toSignedMeasure_apply_measurable hA]
  simp only [measureReal_def,Measure.map_apply hf hA]

def gaussianPositions (n : ℕ) (t : Fin n → ℝ≥0) : Measure (Fin n → ℝ) :=
  (gaussianIncrements t).map (linearImage (cumulativeMatrix n))

instance gaussianPositions_probability (n : ℕ) (t : Fin n → ℝ≥0) :
    IsProbabilityMeasure (gaussianPositions n t) := by
  unfold gaussianPositions
  infer_instance

theorem position_gaussian (n : ℕ) (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i) :
    positionLaw n 1 (by norm_num) t ht=(gaussianPositions n t).toSignedMeasure := by
  unfold positionLaw configurationLaw gaussianPositions
  rw [increment_gaussian,map_toSigned _ _ (linearImage_measurable _)]

end OperatorDerivativeRewrite.Foundation.HigherHeatGaussianConfigurations
