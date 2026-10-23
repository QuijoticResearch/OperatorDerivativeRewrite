import Foundation.IBMActualQuarticMoment
import Foundation.IBMUniformClockMaximum

/-! Actual joint-law even moments of reflected-clock IBM increments.
The scenery is conditioned on the genuine clock; no increment independence
or replacement process is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMActualIncrementMoments
open InfiniteGaussian IBMConstructedSources IBMActualQuarticMoment GaussianAbsoluteMoments
open FractionalSpectralKernel FractionalSpectralGeometry SeparableHilbertEmbedding
attribute [local instance] spectralSpace_secondCountable
attribute [local irreducible] ibmValue clockPath sceneryPath

def direction (a b : ℝ) : CoefficientSpace := sceneryDirection b-sceneryDirection a

theorem direction_norm_sq (a b : ℝ) : ‖direction a b‖^2 = |b-a| := by
  unfold direction sceneryDirection
  rw [← map_sub, LinearIsometry.norm_map]
  simpa using normalized_sub_norm_sq (1/2) (by norm_num) (by norm_num) a b

theorem scenery_increment_ae (a b : ℝ) :
    (fun ξ => sceneryPath ξ b-sceneryPath ξ a) =ᵐ[gaussianProduct]
      firstChaosEmbedding (direction a b) := by
  have he : firstChaosEmbedding (direction a b) =
      firstChaosEmbedding (sceneryDirection b)-firstChaosEmbedding (sceneryDirection a) :=
    map_sub _ _ _
  rw [he]
  filter_upwards [scenery_firstChaos_ae a, scenery_firstChaos_ae b,
    Lp.coeFn_sub (firstChaosEmbedding (sceneryDirection b))
      (firstChaosEmbedding (sceneryDirection a))] with ξ ha hb hs
  rw [hs]
  exact congrArg₂ (fun x y : ℝ => x-y) hb ha

theorem scenery_increment_integrable (a b : ℝ) (p : ℕ) :
    Integrable (fun ξ => |sceneryPath ξ b-sceneryPath ξ a|^p) gaussianProduct :=
  (firstChaos_absolute_integrable (direction a b) p).congr
    ((scenery_increment_ae a b).mono fun _ξ h => congrArg (fun x : ℝ => |x|^p) h.symm)

theorem scenery_even_moment (a b : ℝ) (q : ℕ) :
    (∫ ξ, |sceneryPath ξ b-sceneryPath ξ a|^(2*q) ∂gaussianProduct) =
      |b-a|^q * standardMoment (2*q) := by
  rw [integral_congr_ae ((scenery_increment_ae a b).mono fun ξ h =>
    congrArg (fun x : ℝ => |x|^(2*q)) h), firstChaos_absolute_moment,
    pow_mul, direction_norm_sq]

theorem conditional_even_moment (s t : ℝ≥0) (q : ℕ) (ω : SampleSpace) :
    (∫ ξ, |ibmValue t (ξ,ω)-ibmValue s (ξ,ω)|^(2*q) ∂gaussianProduct) =
      abs (|clockPath ω t| - |clockPath ω s|)^q * standardMoment (2*q) := by
  simpa only [ibmValue_eq] using scenery_even_moment |clockPath ω s| |clockPath ω t| q

theorem reflected_power_integrable (s t : ℝ≥0) (q : ℕ) :
    Integrable (fun ω => abs (|clockPath ω t| - |clockPath ω s|)^q) gaussianProduct := by
  have hm (r : ℝ≥0) : Measurable (fun ω => clockPath ω r) :=
    (ContinuousMap.measurable_eval r).comp clockPath_measurable
  apply (IBMUniformClockMaximum.actual_increment_integrable s t q).mono'
    ((continuous_abs.measurable.comp ((continuous_abs.measurable.comp (hm t)).sub
      (continuous_abs.measurable.comp (hm s)))).pow_const q).aestronglyMeasurable
  apply ae_of_all
  intro ω
  change ‖abs (|clockPath ω t| - |clockPath ω s|)^q‖ ≤
    |clockPath ω t-clockPath ω s|^q
  rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) q)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_abs_sub_abs_le_abs_sub _ _) q

theorem increment_measurable (s t : ℝ≥0) (p : ℕ) :
    Measurable (fun ω : IBMSourceLaws.JointSample => |ibmValue t ω-ibmValue s ω|^p) := by
  have hm (r : ℝ≥0) : Measurable (ibmValue r) :=
    ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  exact (continuous_abs.measurable.comp ((hm t).sub (hm s))).pow_const p

theorem actual_even_integrable (s t : ℝ≥0) (q : ℕ) :
    Integrable (fun ω => |ibmValue t ω-ibmValue s ω|^(2*q)) IBMSourceLaws.jointMeasure := by
  apply (integrable_prod_iff' (increment_measurable s t (2*q)).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun ω => ?_, ?_⟩
  · simpa only [ibmValue_eq] using
      scenery_increment_integrable |clockPath ω s| |clockPath ω t| (2*q)
  · have he (ω : SampleSpace) :
        (∫ ξ, ‖|ibmValue t (ξ,ω)-ibmValue s (ξ,ω)|^(2*q)‖ ∂gaussianProduct) =
          abs (|clockPath ω t| - |clockPath ω s|)^q * standardMoment (2*q) := by
      calc
        _ = ∫ ξ, |ibmValue t (ξ,ω)-ibmValue s (ξ,ω)|^(2*q) ∂gaussianProduct :=
          integral_congr_ae (ae_of_all _ fun ξ =>
            Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) (2*q)))
        _ = _ := conditional_even_moment s t q ω
    simp_rw [he]
    exact (reflected_power_integrable s t q).mul_const _

theorem clock_absolute_moment (s t : ℝ≥0) (q : ℕ) :
    (∫ ω, |clockPath ω t-clockPath ω s|^q ∂gaussianProduct) =
      (Real.sqrt |(t : ℝ)-s|)^q * standardMoment q := by
  have he : (fun ω => |clockPath ω t-clockPath ω s|^q) =ᵐ[gaussianProduct]
      (fun ω => |GaussianTimeProcess.process t ω-GaussianTimeProcess.process s ω|^q) := by
    filter_upwards [clockPath_coordinate_ae s, clockPath_coordinate_ae t] with ω hs ht
    rw [hs,ht]
  rw [integral_congr_ae he]
  have hl := (GaussianTimeProcess.process_increment_hasLaw s t).integral_comp
    (f := fun x : ℝ => |x|^q) (by fun_prop)
  simp only [Function.comp_def, Pi.sub_apply] at hl
  rw [hl, IBMUniformClockMaximum.gaussian_absolute_moment, coe_nndist, Real.dist_eq]

/-- Genuine even-increment estimate with Brownian-in-Brownian scaling. -/
theorem actual_even_moment_le (s t : ℝ≥0) (q : ℕ) :
    (∫ ω, |ibmValue t ω-ibmValue s ω|^(2*q) ∂IBMSourceLaws.jointMeasure) ≤
      standardMoment (2*q) * (Real.sqrt |(t : ℝ)-s|)^q * standardMoment q := by
  have hprod := integral_prod_symm _ (actual_even_integrable s t q)
  change (∫ ω, |ibmValue t ω-ibmValue s ω|^(2*q) ∂gaussianProduct.prod gaussianProduct) = _ at hprod
  unfold IBMSourceLaws.jointMeasure
  rw [hprod]
  simp_rw [conditional_even_moment]
  rw [integral_mul_const]
  have hb : (∫ ω, abs (|clockPath ω t| - |clockPath ω s|)^q ∂gaussianProduct) ≤
      ∫ ω, |clockPath ω t-clockPath ω s|^q ∂gaussianProduct := by
    apply integral_mono (reflected_power_integrable s t q)
      (IBMUniformClockMaximum.actual_increment_integrable s t q)
    intro ω
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_abs_sub_abs_le_abs_sub _ _) q
  have h := mul_le_mul_of_nonneg_right hb (standardMoment_nonnegative (2*q))
  rw [clock_absolute_moment] at h
  nlinarith

end OperatorDerivativeRewrite.Foundation.IBMActualIncrementMoments
