import Foundation.HigherHeatBrownianDyadicLaw

/-! Exact probability and finite-signed realization classification of the even heat cylinder family. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology SchwartzMap BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatRealizationClassification
open HigherHeatDyadicLaws HigherHeatCylindricalExpectation HigherHeatContinuousCylinders
open HigherHeatPathCylinderAlgebra HigherHeatSignedRepresentation HigherHeatBrownianSource
open HigherHeatBrownianDyadicLaw HigherHeatCylindricalOperator

theorem level_expectation (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (f : Test n) :
    expectation 1 (by norm_num) T hT n f=∫ ω : Path, f (sample n ω) ∂sourceMeasure T := by
  change (∫ᵛ x : Grid n, f x ∂•HigherHeatDyadicLaws.law 1 (by norm_num) T hT n) = _
  rw [← sourceMeasure_signed_samples T hT n]
  have hi := bounded_real_integrable (sourceMeasure T).toSignedMeasure (sampleLift n f)
  rw [VectorMeasure.integral_map (sample_continuous n).measurable f.continuous.aestronglyMeasurable hi]
  exact real_integral_toSigned (sourceMeasure T) (sampleLift n f)

theorem algebra_representation (T : ℝ≥0) (hT : 0 < T) (F : cylinderAlgebra) :
    algebraExpectation 1 (by norm_num) T hT F=∫ ω : Path, F.val ω ∂sourceMeasure T := by
  obtain ⟨c,hc⟩ := F.property
  obtain ⟨n,f,hf⟩ := DirectLimit.exists_eq_mk transition c
  change c=cylinderOf n f at hf
  have he : F=representCylinder (cylinderOf n f) := by
    apply Subtype.ext
    change F.val=realize (cylinderOf n f)
    rw [← hf]
    exact hc.symm
  rw [he,algebraExpectation_represent,cylindricalExpectation_apply]
  exact level_expectation T hT n f

theorem signed_representation (T : ℝ≥0) (hT : 0 < T) (F : cylinderAlgebra) :
    algebraExpectation 1 (by norm_num) T hT F=∫ᵛ ω : Path, F.val ω ∂•(sourceMeasure T).toSignedMeasure := by
  rw [real_integral_toSigned]
  exact algebra_representation T hT F

theorem probability_realizable_iff (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    (∃ μ : Measure Path, IsProbabilityMeasure μ ∧
      ∀ F : cylinderAlgebra, algebraExpectation m hm T hT F=∫ ω : Path, F.val ω ∂μ) ↔ m=1 := by
  constructor
  · rintro ⟨μ,hμ,h⟩
    by_contra hm1
    have hm2 : 2 ≤ m := by omega
    letI : IsProbabilityMeasure μ := hμ
    exact no_positive_measure_realization m hm2 T hT μ h
  · intro hm1
    subst m
    exact ⟨sourceMeasure T,inferInstance,algebra_representation T hT⟩

theorem signed_realizable_iff (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    (∃ μ : SignedMeasure Path,
      ∀ F : cylinderAlgebra, algebraExpectation m hm T hT F=∫ᵛ ω : Path, F.val ω ∂•μ) ↔ m=1 := by
  constructor
  · rintro ⟨μ,h⟩
    by_contra hm1
    have hm2 : 2 ≤ m := by omega
    exact no_signed_observable_realization m hm2 T hT μ h
  · intro hm1
    subst m
    exact ⟨(sourceMeasure T).toSignedMeasure,signed_representation T hT⟩

theorem probability_operator_realization (T : ℝ≥0) (hT : 0 < T) (f : 𝓢(ℝ,ℝ)) :
    ∃ g : 𝓢(ℝ,ℂ), HigherHeatL2.evolution 1 T ((complexify f).toLp 2)=g.toLp 2 ∧
      ∀ x : ℝ, ((∫ ω : Path, f (x-coordinate 1 ω) ∂sourceMeasure T : ℝ) : ℂ)=g x := by
  refine ⟨evolved 1 (by norm_num) T hT f,evolution_realized 1 (by norm_num) T hT f,?_⟩
  intro x
  let F := representCylinder (observationCylinder f x)
  have h := algebra_representation T hT F
  have he (ω : Path) : F.val ω=f (x-coordinate 1 ω) := by
    change shiftedTest f x (sample 0 ω HigherHeatNegativeProbe.terminalIndex)=_
    rw [shiftedTest_apply]
    congr 2
    change ω.val (sampleTime 0 HigherHeatNegativeProbe.terminalIndex)=ω.val 1
    congr 1
    norm_num [sampleTime,HigherHeatDyadicLaws.time,duration,gridSize,HigherHeatNegativeProbe.terminalIndex]
  calc
    ((∫ ω : Path, f (x-coordinate 1 ω) ∂sourceMeasure T : ℝ) : ℂ) =
        (algebraExpectation 1 (by norm_num) T hT F : ℂ) := by
      congr 1
      rw [h]
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => (he ω).symm
    _ = (cylindricalExpectation 1 (by norm_num) T hT (observationCylinder f x) : ℂ) := by
      change (algebraExpectation 1 (by norm_num) T hT
        (representCylinder (observationCylinder f x)) : ℂ)=_
      rw [algebraExpectation_represent]
    _ = evolved 1 (by norm_num) T hT f x := expectation_evolved 1 (by norm_num) T hT f x

end OperatorDerivativeRewrite.Foundation.HigherHeatRealizationClassification
