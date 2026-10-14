import Foundation.IBMClockCubicJointTimeL2
import Foundation.GaussianBochnerDivergenceRecovery

/-! Actual joint clock-parameterized L2 source recovery of the cubic time target. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.IBMClockCubicBochnerRecovery
open InfiniteGaussian IBMClockCubicSourcePrimitive IBMClockCubicRepresentative
open IBMClockCubicCorrection IBMClockCubicTimeProjection IBMClockCubicJointTimeL2
open GaussianBochnerDivergenceRecovery GaussianNumberSectors
attribute [local irreducible] IBMConstructedSources.mollifiedValue IBMDyadicExtension.field

theorem integratedCorrection_stronglyMeasurable (n : ℕ) (T : ℝ) :
    StronglyMeasurable (fun ωY => integratedCorrection n ωY T) := by
  letI : Fact ((2 : ℝ≥0∞)≠∞) := ⟨by norm_num⟩
  letI : MeasurableSpace GaussianL2 := borel GaussianL2
  letI : BorelSpace GaussianL2 := ⟨rfl⟩
  have hm : Measurable (fun p : ℝ × SampleSpace => sectionClass n (Real.toNNReal p.1) p.2) := by
    apply measurable_uncurry_of_continuous_of_measurable
      (u := fun s : ℝ => fun ωY : SampleSpace => sectionClass n (Real.toNNReal s) ωY)
    · intro ωY
      exact (spatialCorrection_continuous n).comp (continuous_abs.comp
        ((IBMConstructedSources.clockPath ωY).continuous.comp continuous_real_toNNReal))
    · intro s
      exact (spatialCorrection_continuous n).measurable.comp (continuous_abs.measurable.comp
        ((ContinuousMap.measurable_eval (Real.toNNReal s)).comp IBMConstructedSources.clockPath_measurable))
  exact hm.stronglyMeasurable.integral_prod_left'

theorem integratedCorrection_energy (n : ℕ) (T : ℝ) (ωY : SampleSpace) :
    ‖integratedCorrection n ωY T‖^2=
      ∫ ωX, (integratedValue n ωY T ωX)^2 ∂gaussianProduct := by
  rw [← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [integratedCorrection_coeFn n ωY T] with ωX hx
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs,hx]

theorem integratedCorrection_memLp (n : ℕ) (T : ℝ) :
    MemLp (fun ωY => integratedCorrection n ωY T) 2 gaussianProduct := by
  have hm := integratedCorrection_stronglyMeasurable n T
  apply (memLp_norm_iff hm.aestronglyMeasurable).mp
  apply (memLp_two_iff_integrable_sq hm.norm.aestronglyMeasurable).mpr
  have hi := (integratedValue_memLp_joint n T).integrable_sq
  exact hi.integral_prod_right.congr
    (Eventually.of_forall fun ωY => (integratedCorrection_energy n T ωY).symm)

def clockTargetClass (n : ℕ) (T : ℝ) : Lp GaussianL2 2 gaussianProduct :=
  (integratedCorrection_memLp n T).toLp (fun ωY => integratedCorrection n ωY T)

theorem clockTargetClass_coeFn (n : ℕ) (T : ℝ) :
    clockTargetClass n T =ᵐ[gaussianProduct] fun ωY => integratedCorrection n ωY T :=
  MemLp.coeFn_toLp _

def clockPrimitiveClass (n : ℕ) (T : ℝ) : Lp GaussianVectorL2 2 gaussianProduct :=
  fiberRecovery gaussianProduct (clockTargetClass n T)

theorem clockPrimitiveClass_coeFn (n : ℕ) (T : ℝ) :
    clockPrimitiveClass n T =ᵐ[gaussianProduct] fun ωY => sourcePrimitive n ωY T := by
  filter_upwards [fiberRecovery_coeFn gaussianProduct (clockTargetClass n T),
    clockTargetClass_coeFn n T] with ωY hp ht
  change clockPrimitiveClass n T ωY= _ at hp
  rw [hp,ht]
  rfl

theorem sourcePrimitive_memLp (n : ℕ) (T : ℝ) :
    MemLp (fun ωY => sourcePrimitive n ωY T) 2 gaussianProduct :=
  (Lp.memLp (clockPrimitiveClass n T)).ae_eq (clockPrimitiveClass_coeFn n T)

theorem clockTarget_center (n : ℕ) (T : ℝ) :
    fiberCenter gaussianProduct (clockTargetClass n T)=clockTargetClass n T := by
  apply Lp.ext
  filter_upwards [fiberCenter_coeFn gaussianProduct (clockTargetClass n T),
    clockTargetClass_coeFn n T] with ωY hc ht
  rw [hc,ht,projection_zero,integratedCorrection_centered,zero_smul,sub_zero]

theorem clockPrimitive_graph (n : ℕ) (T : ℝ) :
    (clockPrimitiveClass n T,clockTargetClass n T) ∈
      (BochnerClosedOperator.lift gaussianProduct hilbertDivergence).graph := by
  have hg := fiberRecovery_graph gaussianProduct (clockTargetClass n T)
  simpa only [clockTarget_center,clockPrimitiveClass] using hg

theorem clockPrimitive_norm_le (n : ℕ) (T : ℝ) :
    ‖clockPrimitiveClass n T‖ ≤ ‖clockTargetClass n T‖ :=
  fiberRecovery_norm_le gaussianProduct (clockTargetClass n T)

theorem clockPrimitive_minimal_norm (n : ℕ) (T : ℝ) (v : Lp GaussianVectorL2 2 gaussianProduct)
    (hv : (v,clockTargetClass n T) ∈ (BochnerClosedOperator.lift gaussianProduct hilbertDivergence).graph) :
    ‖clockPrimitiveClass n T‖ ≤ ‖v‖ := by
  apply fiberRecovery_minimal_norm gaussianProduct (clockTargetClass n T) v
  simpa only [clockTarget_center] using hv

theorem clockTarget_energy (n : ℕ) (T : ℝ) :
    ‖clockTargetClass n T‖^2=
      ∫ ω : IBMSourceLaws.JointSample, (integratedValue n ω.2 T ω.1)^2
        ∂IBMSourceLaws.jointMeasure := by
  have hi := (integratedValue_memLp_joint n T).integrable_sq
  rw [← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
  change (∫ ωY, inner ℝ (clockTargetClass n T ωY) (clockTargetClass n T ωY) ∂gaussianProduct)=
    ∫ ω : SampleSpace × SampleSpace, (integratedValue n ω.2 T ω.1)^2
      ∂gaussianProduct.prod gaussianProduct
  rw [integral_prod_symm (fun ω => (integratedValue n ω.2 T ω.1)^2) hi]
  apply integral_congr_ae
  filter_upwards [clockTargetClass_coeFn n T] with ωY ht
  rw [real_inner_self_eq_norm_sq,ht,integratedCorrection_energy]

theorem integratedValue_joint_centered (n : ℕ) (T : ℝ) :
    (∫ ω : IBMSourceLaws.JointSample, integratedValue n ω.2 T ω.1
      ∂IBMSourceLaws.jointMeasure)=0 := by
  have hi : Integrable (fun ω : IBMSourceLaws.JointSample => integratedValue n ω.2 T ω.1)
      IBMSourceLaws.jointMeasure :=
    memLp_one_iff_integrable.mp ((integratedValue_memLp_joint n T).mono_exponent (by norm_num))
  change (∫ ω : SampleSpace × SampleSpace, integratedValue n ω.2 T ω.1
    ∂gaussianProduct.prod gaussianProduct)=0
  rw [integral_prod_symm (fun ω => integratedValue n ω.2 T ω.1) hi]
  simp only [integratedValue_centered,integral_zero]

end OperatorDerivativeRewrite.Foundation.IBMClockCubicBochnerRecovery
