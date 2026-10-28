import Foundation.SU2TwoLoopChain
/-! A genuine two-step SU(2) path law and exact independence of its closed products. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.SU2TraceHessianModel
open OperatorDerivativeRewrite.Foundation.SU2TwoLoopChain
namespace OperatorDerivativeRewrite.Foundation.SU2TwoLoopJointLaw

private theorem measurable_mul_pair : Measurable (fun p : SU2 × SU2 => p.1 * p.2) := by
  apply Measurable.subtype_mk
  change Measurable (fun p : SU2 × SU2 => (p.1 : M2) * (p.2 : M2))
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro k hk
  have hL : Measurable (fun p : SU2 × SU2 => (p.1 : M2) i k) :=
    (measurable_pi_apply k).comp
      ((measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_fst))
  have hR : Measurable (fun p : SU2 × SU2 => (p.2 : M2) k j) :=
    (measurable_pi_apply j).comp
      ((measurable_pi_apply k).comp (measurable_subtype_coe.comp measurable_snd))
  exact hL.mul hR

private theorem measurable_loop_pair (A : SU2) :
    Measurable (fun p : SU2 × SU2 => (A * p.1, p.1 * p.2)) :=
  ((measurable_const_mul A).comp measurable_fst).prodMk measurable_mul_pair

/-- The sequential one-word update is an actual probability law on two links. -/
theorem two_step_probability (A : SU2) (β : ℝ) :
    IsProbabilityMeasure (SU2OneWordTransfer.transition law β A ⊗ₘ
      SU2OneWordTransfer.transition law β) := by
  let K := SU2OneWordTransfer.transition law β
  have : IsMarkovKernel K := SU2OneWordTransfer.transition_markov law β
  constructor
  rw [Measure.compProd_apply_univ]
  exact measure_univ

private theorem joint_finite (A : SU2) (β : ℝ) :
    IsFiniteMeasure (SU2OneWordTransfer.transition law β A ⊗ₘ
      SU2OneWordTransfer.transition law β) := by
  letI : IsProbabilityMeasure (SU2OneWordTransfer.transition law β A ⊗ₘ
    SU2OneWordTransfer.transition law β) := two_step_probability A β
  infer_instance

set_option maxRecDepth 2000 in
/-- The two consecutive closed products have exactly the product tilted law. -/
theorem two_loop_joint_law (A : SU2) (β : ℝ) :
    (SU2OneWordTransfer.transition law β A ⊗ₘ
      SU2OneWordTransfer.transition law β).map
      (fun p : SU2 × SU2 => (A * p.1, p.1 * p.2)) =
    (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β).prod
      (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β) := by
  let K := SU2OneWordTransfer.transition law β
  have : IsMarkovKernel K := SU2OneWordTransfer.transition_markov law β
  have : IsFiniteMeasure ((K A ⊗ₘ K).map
      (fun p : SU2 × SU2 => (A * p.1, p.1 * p.2))) :=
    letI := joint_finite A β
    (K A ⊗ₘ K).isFiniteMeasure_map _
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (measurable_loop_pair A) (hs.prod ht)]
  rw [Measure.compProd_apply ((hs.prod ht).preimage (measurable_loop_pair A))]
  have : IsProbabilityMeasure
      (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β) :=
    BoundedExponentialTiltResponse.tiltedMeasure_probability law halfTrace
      halfTrace_measurable halfTrace_bound β
  rw [Measure.prod_prod]
  have hS : MeasurableSet {B : SU2 | A * B ∈ s} :=
    hs.preimage (measurable_const_mul A)
  have hsection (B : SU2) :
      K B (Prod.mk B ⁻¹' (fun p : SU2 × SU2 => (A * p.1, p.1 * p.2)) ⁻¹' s ×ˢ t) =
      Set.indicator {B : SU2 | A * B ∈ s}
        (fun B => K B {D | B * D ∈ t}) B := by
    by_cases hB : A * B ∈ s
    · simp [Set.indicator, hB, Set.preimage, Set.mem_prod]
    · simp [Set.indicator, hB, Set.preimage, Set.mem_prod]
  change (∫⁻ B, K B
    (Prod.mk B ⁻¹' (fun p : SU2 × SU2 => (A * p.1, p.1 * p.2)) ⁻¹' s ×ˢ t)
    ∂K A) = _
  simp_rw [hsection]
  rw [lintegral_indicator hS]
  exact two_loop_rectangle A β s t hs ht

end OperatorDerivativeRewrite.Foundation.SU2TwoLoopJointLaw
