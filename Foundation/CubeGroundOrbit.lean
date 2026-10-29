import Foundation.CubeGroundMass

/-! Actual native ground-law concentration of the gauge-invariant reduced energy.
This is not a time-mixing or spectral-gap theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CubeGroundOrbit
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab CubeSlabGround
open CubeAxialSlice CubeAxialGauge CubeGroundMass

private theorem rooted_measurable (v : SpatialVertex) :
    Measurable (fun U : State => rootedGauge U v) := by
  unfold rootedGauge
  split_ifs <;> fun_prop

private theorem reduced_measurable : Measurable reduced := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((rooted_measurable (chordEdge i).val.1).mul (measurable_pi_apply (chordEdge i))).mul
    (rooted_measurable (shift (chordEdge i).val.1 (chordEdge i).val.2)).inv

theorem energy_measurable : Measurable (fun U : State => chordEnergy (reduced U)) := by
  unfold chordEnergy FourCubePinnedCoercivity.defect
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.sub (halfTrace_measurable.comp
    ((measurable_pi_apply i).comp reduced_measurable))

private theorem tail_subset (eps : ℝ) :
    {U : State | eps ≤ chordEnergy (reduced U)} ⊆ {U | eps/4 ≤ spatialAction U} := by
  intro U hU
  change eps ≤ chordEnergy (reduced U) at hU
  have h := coercive_mod_gauge U
  change eps/4 ≤ spatialAction U
  linarith

/-- Threshold-dependent exponential concentration for the actual native probability. -/
theorem reduced_tail_exponential (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ beta : ℝ, 0 ≤ beta → ∀ d : GroundData beta,
      d.stationary.real {U | eps ≤ chordEnergy (reduced U)} ≤ C*Real.exp (-beta*eps/8) := by
  obtain ⟨C,hC,hb⟩ := action_tail_exponential (eps/4) (by positivity)
  refine ⟨C,hC,?_⟩
  intro beta hbeta d
  letI : IsProbabilityMeasure d.stationary := d.stationary_probability
  have h := measureReal_mono (μ := d.stationary) (tail_subset eps) (measure_ne_top _ _)
  have hs := h.trans (hb beta hbeta d)
  convert hs using 1
  congr 2
  ring

/-- Actual stationary canonical-energy tail tends to zero as coupling grows. -/
theorem reduced_tail_tendsto_zero (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun beta : ℝ => (ground beta).stationary.real
      {U | eps ≤ chordEnergy (reduced U)}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun beta => measureReal_nonneg)) ?_
    (action_tail_tendsto_zero (eps/4) (by positivity))
  apply Eventually.of_forall
  intro beta
  letI : IsProbabilityMeasure (ground beta).stationary := (ground beta).stationary_probability
  exact measureReal_mono (μ := (ground beta).stationary) (tail_subset eps) (measure_ne_top _ _)

end OperatorDerivativeRewrite.Foundation.CubeGroundOrbit
