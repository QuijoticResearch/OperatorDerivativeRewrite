import Foundation.IBMDyadicExtension
import Foundation.IBMRandomDerivativeIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual product-space evaluation of the constructed continuous mollifier
fields at the independently constructed Brownian clock coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.IBMPointwiseEvaluation
open InfiniteGaussian IBMJointMollifierGaussian IBMDyadicExtension
open GaussianHilbertProcess FractionalSpectralKernel IBMContinuousScenery
open IBMSourceLaws IBMRandomDerivativeIntegrability
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable
attribute [local irreducible] IBMDyadicExtension.field

theorem field_memLp (n : ℕ) (i : Fin 3) (r : ℝ) :
    MemLp (fun ω => field n i ω r) 2 gaussianProduct :=
  (isonormal_memLp (wholeLineDirection (derivativeKernel n i) r) 2 (by norm_num)).ae_eq
    (field_coordinate_ae n i r).symm

theorem field_sq_integrable (n : ℕ) (i : Fin 3) (r : ℝ) :
    Integrable (fun ω => (field n i ω r)^2) gaussianProduct := by
  simpa only [Real.norm_eq_abs, sq_abs] using (field_memLp n i r).integrable_norm_pow'

theorem field_sq_integral (n : ℕ) (i : Fin 3) (r : ℝ) :
    (∫ ω, (field n i ω r)^2 ∂gaussianProduct) =
      ‖wholeLineScenery (derivativeKernel n i) r‖^2 := by
  have he : (∫ ω, (field n i ω r)^2 ∂gaussianProduct) =
      ∫ ω, (gaussianTriple n r i ω)^2 ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [field_coordinate_ae n i r] with ω hω
    rw [hω]
  rw [he]
  have h := isonormal_product_integral
    (wholeLineDirection (derivativeKernel n i) r) (wholeLineDirection (derivativeKernel n i) r)
  rw [wholeLineScenery_eq_sourceEmbedding, LinearIsometry.norm_map]
  simpa only [gaussianTriple, pow_two, real_inner_self_eq_norm_sq] using h

/-- Deterministic-coordinate identification as an L² class. -/
theorem field_toLp_eq (n : ℕ) (i : Fin 3) (r : ℝ) :
    (field_memLp n i r).toLp (fun ω => field n i ω r) =
      wholeLineScenery (derivativeKernel n i) r := by
  apply Lp.ext
  filter_upwards [(field_memLp n i r).coeFn_toLp, field_coordinate_ae n i r] with ω h1 h2
  rw [h1, h2, wholeLineScenery_eq_sourceEmbedding]
  rfl

def value (n : ℕ) (i : Fin 3) (t : ℝ≥0) (ω : JointSample) : ℝ :=
  field n i ω.1 |GaussianTimeProcess.process t ω.2|

theorem value_measurable (n : ℕ) (i : Fin 3) (t : ℝ≥0) : Measurable (value n i t) :=
  (field_jointly_measurable n i).comp
    ((continuous_abs.measurable.comp
      ((GaussianTimeProcess.process_stronglyMeasurable t).measurable.comp measurable_snd)).prodMk measurable_fst)

/-- For every clock sample, the actual pointwise section represents exactly
the previously constructed random Gaussian-L² class. -/
theorem value_section_toLp_eq (n : ℕ) (i : Fin 3) (t : ℝ≥0) (ωY : SampleSpace) :
    (field_memLp n i |GaussianTimeProcess.process t ωY|).toLp
      (fun ωX => value n i t (ωX, ωY)) =
        randomKernelClass (derivativeKernel n i) t ωY :=
  field_toLp_eq n i |GaussianTimeProcess.process t ωY|

/-- Fixed-time square integrability of actual U,V,W evaluations on the joint
probability space. No continuous Brownian clock is assumed. -/
theorem value_memLp (n : ℕ) (i : Fin 3) (t : ℝ≥0) :
    MemLp (value n i t) 2 jointMeasure := by
  apply (memLp_two_iff_integrable_sq (value_measurable n i t).aestronglyMeasurable).mpr
  change Integrable (fun ω => (value n i t ω)^2) (gaussianProduct.prod gaussianProduct)
  have hm : AEStronglyMeasurable (fun ω : SampleSpace × SampleSpace => (value n i t ω)^2)
      (gaussianProduct.prod gaussianProduct) :=
    ((value_measurable n i t).pow_const 2).aestronglyMeasurable
  have hsection : ∀ ωY : SampleSpace,
      Integrable (fun ωX => (value n i t (ωX, ωY))^2) gaussianProduct :=
    fun ωY => by simpa only [value] using
      field_sq_integrable n i |GaussianTimeProcess.process t ωY|
  have hnorm : Integrable (fun ωY => ∫ ωX, ‖(value n i t (ωX, ωY))^2‖ ∂gaussianProduct)
      gaussianProduct := by
    have hi := (memLp_two_iff_integrable_sq_norm
      (randomDerivativeClass_memLp n i t).aestronglyMeasurable).mp
        (randomDerivativeClass_memLp n i t)
    convert hi using 1
    funext ωY
    simp only [Real.norm_eq_abs, abs_pow, sq_abs, value, randomKernelClass]
    exact field_sq_integral n i _
  exact (integrable_prod_iff' (μ := gaussianProduct) (ν := gaussianProduct)
    (f := fun ω : SampleSpace × SampleSpace => (value n i t ω)^2) hm).mpr
      ⟨Filter.Eventually.of_forall hsection, hnorm⟩

theorem value_path_continuous_of_clock (n : ℕ) (i : Fin 3)
    (Y : ℝ≥0 → ℝ) (hY : Continuous Y) (ωX : SampleSpace) :
    Continuous (fun t => field n i ωX |Y t|) :=
  (field_continuous n i ωX).comp (continuous_abs.comp hY)

end OperatorDerivativeRewrite.Foundation.IBMPointwiseEvaluation
