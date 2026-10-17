import Foundation.StoppingTimeRounding
import Foundation.RightContinuousProgressive
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! Bounded optional sampling for right-continuous Banach-valued martingales. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RightContinuousBoundedSampling
open StoppingTimeRounding

variable {Ω E : Type*} [m : MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℝ≥0 m) (M : ℝ≥0 → Ω → E)
  (hM : Martingale M ℱ μ) (hr : ∀ ω, IsRightContinuous (fun t => M t ω))
  (τ : Ω → ℝ≥0) (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
  (N : ℕ) (hN : ∀ ω, τ ω ≤ N)

def sampled (n : ℕ) (ω : Ω) : E := M (rounded n (τ ω)) ω

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
include hM hτ hN in
theorem sampled_ae_condExp (n : ℕ) :
    sampled M τ n =ᵐ[μ] μ[M (N : ℝ≥0) |
      (rounded_isStoppingTime ℱ τ hτ n).measurableSpace] := by
  have hs := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    (rounded_isStoppingTime ℱ τ hτ n)
    (fun ω => show (rounded n (τ ω) : WithTop ℝ≥0) ≤ (N : ℝ≥0) from
      WithTop.coe_le_coe.mpr (rounded_bounded n (τ ω) (hN ω)))
    (rounded_countable_range n τ)
  exact hs

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
theorem conditional_uniformIntegrable {ι : Type*} (g : Ω → E) (hg : Integrable g μ)
    (A : ι → MeasurableSpace Ω) (hA : ∀ i, A i ≤ m) :
    UniformIntegrable (fun i => μ[g | A i]) 1 μ := by
  have hu := hg.norm.uniformIntegrable_condExp hA
  have hm (i : ι) : AEStronglyMeasurable (μ[g | A i]) μ :=
    (stronglyMeasurable_condExp.mono (hA i)).aestronglyMeasurable
  have hb (i : ι) : ∀ᵐ ω ∂μ, ‖μ[g | A i] ω‖ ≤ ‖μ[fun ω => ‖g ω‖ | A i] ω‖ := by
    filter_upwards [norm_condExp_le (μ := μ) (m := A i) g] with ω hω
    simpa only [Real.norm_eq_abs] using hω.trans (le_abs_self _)
  have hs : UnifIntegrable (fun i => μ[g | A i]) 1 μ := by
    apply unifIntegrable_iff.mpr
    intro ε hε
    obtain ⟨δ,hδ,hbound⟩ := unifIntegrable_iff.mp hu.1 ε hε
    refine ⟨δ,hδ,fun i s hμs => ?_⟩
    exact (eLpNorm_mono_ae (hm i).restrict (ae_restrict_of_ae (hb i))).trans (hbound i s hμs)
  obtain ⟨C,hC⟩ := hu.2
  exact ⟨hs,C,fun i => (eLpNorm_mono_ae (hm i) (hb i)).trans (hC i)⟩

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
include hM hτ hN in
theorem sampled_uniformIntegrable : UniformIntegrable (sampled M τ) 1 μ := by
  have hu := conditional_uniformIntegrable μ (M (N : ℝ≥0)) (hM.integrable (N : ℝ≥0))
    (fun n => (rounded_isStoppingTime ℱ τ hτ n).measurableSpace)
    (fun n => (rounded_isStoppingTime ℱ τ hτ n).measurableSpace_le)
  exact hu.ae_eq (fun n => (sampled_ae_condExp μ ℱ M hM τ hτ N hN n).symm)

omit [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] [IsFiniteMeasure μ] in
include hr in
theorem sampled_ae_tendsto : ∀ᵐ ω ∂μ,
    Tendsto (fun n => sampled M τ n ω) atTop (𝓝 (M (τ ω) ω)) := by
  apply Eventually.of_forall
  intro ω
  have hge : Tendsto (fun n => rounded n (τ ω)) atTop (𝓟 (Ici (τ ω))) :=
    tendsto_principal.mpr (Eventually.of_forall (fun n => le_rounded n (τ ω)))
  have ht := (rounded_tendsto (τ ω)).inf hge
  simp only [inf_idem] at ht
  exact Filter.Tendsto.comp (continuousWithinAt_Ioi_iff_Ici.mp (hr ω (τ ω))) ht

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
include hM hr hτ hN in
theorem stopped_integrable : Integrable (fun ω => M (τ ω) ω) μ :=
  (sampled_uniformIntegrable μ ℱ M hM τ hτ N hN).integrable_of_ae_tendsto
    (sampled_ae_tendsto μ M hr τ)

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
include hM hr hτ hN in
theorem sampled_L1_tendsto :
    Tendsto (fun n => eLpNorm (sampled M τ n-(fun ω => M (τ ω) ω)) 1 μ) atTop (𝓝 0) := by
  have hu := sampled_uniformIntegrable μ ℱ M hM τ hτ N hN
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp)
    hu.aestronglyMeasurable
    (memLp_one_iff_integrable.mpr (stopped_integrable μ ℱ M hM hr τ hτ N hN))
    hu.1 (sampled_ae_tendsto μ M hr τ)

include hM hr hτ hN in
theorem stopped_ae_condExp :
    (fun ω => M (τ ω) ω) =ᵐ[μ] μ[M (N : ℝ≥0) | hτ.measurableSpace] := by
  have hi := stopped_integrable μ ℱ M hM hr τ hτ N hN
  have hu := sampled_uniformIntegrable μ ℱ M hM τ hτ N hN
  have hL := sampled_L1_tendsto μ ℱ M hM hr τ hτ N hN
  have hs : Measurable[hτ.measurableSpace] (fun ω => M (τ ω) ω) := by
    have hfun : stoppedValue M (fun ω => (τ ω : WithTop ℝ≥0)) =
        (fun ω => M (τ ω) ω) := by funext ω; rfl
    rw [← hfun]
    exact measurable_stoppedValue
      (RightContinuousProgressive.progressive ℱ M hM.stronglyAdapted hr) hτ
  apply ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le (hM.integrable (N : ℝ≥0))
    (fun _ _ _ => hi.integrableOn) _ hs.stronglyMeasurable.aestronglyMeasurable
  intro A hA _
  have hlin : Tendsto (fun n => ∫⁻ ω, ‖sampled M τ n ω-M (τ ω) ω‖ₑ ∂μ) atTop (𝓝 0) := by
    convert hL using 1
    funext n
    rw [eLpNorm_one_eq_lintegral_enorm ((hu.aestronglyMeasurable n).sub hi.aestronglyMeasurable)]
    rfl
  have ht := tendsto_setIntegral_of_L1 (fun ω => M (τ ω) ω) hi.aestronglyMeasurable
    (Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hu.memLp n)) hlin A
  have he (n : ℕ) : (∫ ω in A, sampled M τ n ω ∂μ) = ∫ ω in A, M (N : ℝ≥0) ω ∂μ := by
    rw [integral_congr_ae (ae_restrict_of_ae (sampled_ae_condExp μ ℱ M hM τ hτ N hN n))]
    exact setIntegral_condExp (rounded_isStoppingTime ℱ τ hτ n).measurableSpace_le
      (hM.integrable (N : ℝ≥0))
      ((hτ.measurableSpace_mono (rounded_isStoppingTime ℱ τ hτ n)
        (fun ω => WithTop.coe_le_coe.mpr (le_rounded n (τ ω)))) A hA)
  exact tendsto_nhds_unique ht (by simp only [he]; exact tendsto_const_nhds)

include hM hr hτ hN in
theorem stopped_expectation :
    (∫ ω, M (τ ω) ω ∂μ) = ∫ ω, M (N : ℝ≥0) ω ∂μ := by
  rw [integral_congr_ae (stopped_ae_condExp μ ℱ M hM hr τ hτ N hN)]
  exact integral_condExp hτ.measurableSpace_le

include hM hr hτ hN in
theorem sample_two (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0))) (hστ : ∀ ω, σ ω ≤ τ ω) :
    μ[fun ω => M (τ ω) ω | hσ.measurableSpace] =ᵐ[μ] fun ω => M (σ ω) ω := by
  have hS := stopped_ae_condExp μ ℱ M hM hr σ hσ N (fun ω => (hστ ω).trans (hN ω))
  have hT := stopped_ae_condExp μ ℱ M hM hr τ hτ N hN
  have hle := hσ.measurableSpace_mono hτ (fun ω => WithTop.coe_le_coe.mpr (hστ ω))
  have hC := condExp_congr_ae (m := hσ.measurableSpace) hT
  exact (hC.trans (condExp_condExp_of_le hle hτ.measurableSpace_le)).trans hS.symm

end OperatorDerivativeRewrite.Foundation.RightContinuousBoundedSampling
