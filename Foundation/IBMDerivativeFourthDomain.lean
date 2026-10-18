import Foundation.IBMClockSixthMoment
import Foundation.IBMFiniteHorizonEvaluation

/-! Genuine fourth moments of the constructed derivative fields on the
finite time/joint-source domain. Constants depend on the fixed mollifier. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMDerivativeFourthDomain
open InfiniteGaussian IBMSourceLaws IBMConstructedSources IBMGaussianSteinMoments
open IBMSceneryGlobalGrowth IBMClockSixthMoment IBMFiniteHorizonEvaluation
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable
attribute [local irreducible] mollifiedValue IBMDyadicExtension.field

theorem evaluation_eq (n : ℕ) (i : Fin 3) (t : ℝ≥0) (ω : JointSample) :
    mollifiedValue n i t ω = IBMDyadicExtension.field n i ω.1 |clockPath ω.2 t| := by
  simp only [mollifiedValue, IBMContinuousComposition.value, IBMContinuousComposition.path,
    IBMDyadicExtension.path, ContinuousMap.coe_mk]

theorem field_fourth_integrable (n : ℕ) (i : Fin 3) (r : ℝ) :
    Integrable (fun ω => (IBMDyadicExtension.field n i ω r)^4) gaussianProduct := by
  have hp : MemLp (fun ω => IBMDyadicExtension.field n i ω r) 4 gaussianProduct :=
    (GaussianHilbertProcess.isonormal_memLp
      (IBMJointMollifierGaussian.wholeLineDirection
        (IBMJointMollifierGaussian.derivativeKernel n i) r) 4 (by norm_num)).ae_eq
      (IBMDyadicExtension.field_coordinate_ae n i r).symm
  simpa only [Real.norm_eq_abs, (show Even 4 by decide).pow_abs] using
    hp.integrable_norm_pow (by norm_num)

theorem field_fourth_integral (n : ℕ) (i : Fin 3) (r : ℝ) :
    (∫ ω, (IBMDyadicExtension.field n i ω r)^4 ∂gaussianProduct) =
      3 * ‖tripleCoefficient n r i‖^4 := by
  rw [integral_congr_ae ((IBMDyadicExtension.field_coordinate_ae n i r).mono
    fun ω he => congrArg (fun x : ℝ => x^4) he), gaussianTriple_eq_firstChaos,
    IBMSourceMoments.firstChaos_fourth]
  ring

theorem fourth_growth (n : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, 3 * ‖tripleCoefficient n r i‖^4 ≤ C*(1+|r|)^6 := by
  obtain ⟨B, hB, hb⟩ := tripleCoefficient_global_growth n i
  refine ⟨3*B^4, by positivity, fun r => ?_⟩
  have he := pow_le_pow_left₀ (norm_nonneg _) (hb r) 4
  have hp : (1+|r|)^4 ≤ (1+|r|)^6 :=
    pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg r)) (by norm_num)
  rw [mul_pow] at he
  nlinarith [mul_le_mul_of_nonneg_left hp (pow_nonneg hB 4)]

theorem joint_fourth_integrable (n : ℕ) (i : Fin 3) (t : ℝ≥0) :
    Integrable (fun ω => (mollifiedValue n i t ω)^4) jointMeasure := by
  have hm : Measurable (fun ω : JointSample => (mollifiedValue n i t ω)^4) :=
    ((mollifiedValue_jointly_measurable n i).comp
    (measurable_const.prodMk measurable_id)).pow_const 4
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun ωY => by
      simpa only [evaluation_eq] using field_fourth_integrable n i |clockPath ωY t|
  · obtain ⟨C,hC,hgrowth⟩ := fourth_growth n i
    have hi : Integrable (fun ω => C*(1+|clockPath ω t|)^6) gaussianProduct := by
      simpa only [← pow_mul] using
        ((IBMClockCubicJointL2.clock_cubic_growth_memLp t).integrable_sq.const_mul C)
    apply hi.mono' hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    exact Eventually.of_forall fun ωY => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have he : (∫ ωX, ‖(mollifiedValue n i t (ωX,ωY))^4‖ ∂gaussianProduct) =
          3 * ‖tripleCoefficient n |clockPath ωY t| i‖^4 := by
        simp_rw [evaluation_eq]
        simpa only [evaluation_eq, Real.norm_eq_abs, abs_pow, (show Even 4 by decide).pow_abs] using
          field_fourth_integral n i |clockPath ωY t|
      rw [he]
      simpa only [abs_abs] using hgrowth |clockPath ωY t|

theorem joint_fourth_growth (n : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ≥0,
      (∫ ω, (mollifiedValue n i t ω)^4 ∂jointMeasure) ≤ C*(1+15*(t : ℝ)^3) := by
  obtain ⟨C,hC,hgrowth⟩ := fourth_growth n i
  refine ⟨64*C, by positivity, fun t => ?_⟩
  change (∫ ω : SampleSpace × SampleSpace, (mollifiedValue n i t ω)^4
    ∂gaussianProduct.prod gaussianProduct) ≤ _
  rw [integral_prod_symm _ (joint_fourth_integrable n i t)]
  have hi : Integrable (fun ωY => ∫ ωX, (mollifiedValue n i t (ωX,ωY))^4
      ∂gaussianProduct) gaussianProduct := (joint_fourth_integrable n i t).integral_prod_right
  have hj : Integrable (fun ω => C*(1+|clockPath ω t|)^6) gaussianProduct := by
    simpa only [← pow_mul] using
      ((IBMClockCubicJointL2.clock_cubic_growth_memLp t).integrable_sq.const_mul C)
  calc
    _ ≤ ∫ ω, C*(1+|clockPath ω t|)^6 ∂gaussianProduct := by
      apply integral_mono hi hj
      intro ωY
      simp_rw [evaluation_eq]
      rw [field_fourth_integral]
      simpa only [abs_abs] using hgrowth |clockPath ωY t|
    _ = C*(∫ ω, (1+|clockPath ω t|)^6 ∂gaussianProduct) := integral_const_mul _ _
    _ ≤ C*(64*(1+15*(t : ℝ)^3)) :=
      mul_le_mul_of_nonneg_left (clock_growth_sixth_integral_le t) hC
    _ = _ := by ring

theorem horizon_fourth_integrable (n : ℕ) (i : Fin 3) (T : ℝ) :
    Integrable (fun p : ℝ × JointSample => (horizonValue n i p)^4)
      ((volume.restrict (Set.Ioc 0 T)).prod jointMeasure) := by
  have hm := (horizonValue_measurable n i).pow_const 4
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun t => joint_fourth_integrable n i t.toNNReal
  · obtain ⟨C,hC,hgrowth⟩ := joint_fourth_growth n i
    have hc : Continuous (fun t : ℝ => C*(1+15*(t.toNNReal : ℝ)^3)) := by fun_prop
    apply hc.integrableOn_Ioc.mono' hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have he : (∫ ω, ‖(horizonValue n i (t,ω))^4‖ ∂jointMeasure) =
          ∫ ω, (mollifiedValue n i t.toNNReal ω)^4 ∂jointMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => Real.norm_of_nonneg (by positivity)
      rw [he]
      exact hgrowth t.toNNReal

end OperatorDerivativeRewrite.Foundation.IBMDerivativeFourthDomain
