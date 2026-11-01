import Foundation.PeriodicPhysicalFisherWitness
/-! Endpoint-law invariance does not identify endpoint tangent directions.
The actual Wilson conditional score needs the transported curve, not just its
base law. These results do not exclude a covariantly defined boundary calculus. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicEndpointTangentDescent
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicEndpointScore PeriodicEndpointFibreWitness PeriodicPhysicalBridgeScore
attribute [local irreducible] kernel boundaryHaar gaugeHaar spatialAction temporalAction

private theorem gauge_one (U : State) : gaugeAction 1 U = U := by
  funext e
  simp only [gaugeAction, Pi.one_apply, inv_one, one_mul, mul_one]

/-- Independent endpoint gauge transformations leave the ORIGINAL middle law
unchanged, including its normalizer. The middle variable is not transformed. -/
theorem law_endpoint_gauge (β : ℝ) (a b : Gauge) (U W : State) :
    PeriodicGroundBridge.law β (gaugeAction a U) (gaugeAction b W) =
      PeriodicGroundBridge.law β U W := by
  have he : PeriodicGroundBridge.bridgeWeight β (gaugeAction a U) (gaugeAction b W) =
      PeriodicGroundBridge.bridgeWeight β U W := by
    funext V
    unfold PeriodicGroundBridge.bridgeWeight
    rw [kernel_left_invariant, kernel_right_invariant]
  unfold PeriodicGroundBridge.law
  rw [he]

/-- The two explicit witness pairs have exactly the same actual conditional law. -/
theorem witness_law (β : ℝ) :
    PeriodicGroundBridge.law β leftEndpoint rightEndpoint =
      PeriodicGroundBridge.law β leftEndpoint leftEndpoint := by
  rw [← PeriodicWindingEndpointResponse.endpoint_flip]
  have h := law_endpoint_gauge β 1 (fun _ => PeriodicEndpointWard.flip)
    leftEndpoint leftEndpoint
  simpa only [PeriodicEndpointWard.field, gauge_one] using h

/-- Positive physical score energy persists in the IDENTICAL diagonal base law.
It belongs to the off-diagonal representative's prescribed tangent curve. -/
theorem witness_energy (β : ℝ) (hβ : 0 ≤ β)
    (hα : SU2WilsonConvolution.coefficient β ≠ 0) :
    0 < ∫ V, (physicalScore β leftEndpoint rightEndpoint V)^2
      ∂PeriodicGroundBridge.law β leftEndpoint leftEndpoint := by
  rw [← witness_law]
  exact PeriodicPhysicalFisherWitness.physical_energy_positive β hβ hα

/-- Keeping a fixed Lie-algebra axis while changing endpoint representatives
does not define the same physical L2 score, even though the laws agree. -/
theorem witness_scores_distinct (β : ℝ) (hβ : 0 ≤ β)
    (hα : SU2WilsonConvolution.coefficient β ≠ 0) :
    ¬ physicalScore β leftEndpoint rightEndpoint =ᵐ[
        PeriodicGroundBridge.law β leftEndpoint leftEndpoint]
      physicalScore β leftEndpoint leftEndpoint := by
  intro he
  have hz := he.trans (diagonal_physical_zero β leftEndpoint)
  have hi : (∫ V, (physicalScore β leftEndpoint rightEndpoint V)^2
      ∂PeriodicGroundBridge.law β leftEndpoint leftEndpoint) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hz] with V hV
    change physicalScore β leftEndpoint rightEndpoint V = 0 at hV
    change (physicalScore β leftEndpoint rightEndpoint V)^2 = 0
    rw [hV, zero_pow (by norm_num : 2 ≠ 0)]
  exact (ne_of_gt (witness_energy β hβ hα)) hi

/-- This refutes endpoint gauge descent for the SPECIFIED fixed-axis score.
It does not refute transport of tangent vectors or all gauge-covariant scores. -/
theorem no_fixed_axis_endpoint_descent (β : ℝ) (hβ : 0 ≤ β)
    (hα : SU2WilsonConvolution.coefficient β ≠ 0) :
    ¬ ∀ (a b : Gauge) (U W : State),
      physicalScore β (gaugeAction a U) (gaugeAction b W) =ᵐ[PeriodicGroundBridge.law β U W]
        physicalScore β U W := by
  intro hh
  have he := hh 1 (fun _ => PeriodicEndpointWard.flip) leftEndpoint leftEndpoint
  have hf : gaugeAction (fun _ => PeriodicEndpointWard.flip) leftEndpoint = rightEndpoint :=
    PeriodicWindingEndpointResponse.endpoint_flip
  rw [gauge_one, hf] at he
  exact witness_scores_distinct β hβ hα he

/-- In particular the base conditional measure alone does not determine this
score. A law AND a tangent variation must be supplied to a reconstruction. -/
theorem no_law_only_score (β : ℝ) (hβ : 0 ≤ β)
    (hα : SU2WilsonConvolution.coefficient β ≠ 0) :
    ¬ ∃ F : Measure State → State → ℝ, ∀ U W,
      physicalScore β U W =ᵐ[PeriodicGroundBridge.law β U W]
        F (PeriodicGroundBridge.law β U W) := by
  rintro ⟨F, hF⟩
  have ho := hF leftEndpoint rightEndpoint
  rw [witness_law] at ho
  exact witness_scores_distinct β hβ hα (ho.trans (hF leftEndpoint leftEndpoint).symm)

/-- Positive repair: gauge-transform the ENTIRE endpoint paths, retaining the
induced tangent motion. No continuity of the gauge choices is needed for this
pointwise law identity; no new differentiability is inferred from it. -/
theorem curve_law (β : ℝ) (L R : ℝ → State) (a b : ℝ → Gauge) :
    (fun h => PeriodicGroundBridge.law β (gaugeAction (a h) (L h)) (gaugeAction (b h) (R h))) =
      (fun h => PeriodicGroundBridge.law β (L h) (R h)) := by
  funext h
  exact law_endpoint_gauge β (a h) (b h) (L h) (R h)

theorem curve_expectation (β : ℝ) (L R : ℝ → State) (a b : ℝ → Gauge)
    (f : State → ℝ) :
    (fun h => ∫ V, f V
      ∂PeriodicGroundBridge.law β (gaugeAction (a h) (L h)) (gaugeAction (b h) (R h))) =
      (fun h => ∫ V, f V ∂PeriodicGroundBridge.law β (L h) (R h)) := by
  funext h
  rw [law_endpoint_gauge]

/-- Transport of a proved derivative along the actual boundary curve. The
original derivative hypothesis is essential; this is not an existence theorem. -/
theorem curve_derivative (β : ℝ) (L R : ℝ → State) (a b : ℝ → Gauge)
    (f : State → ℝ) (v t : ℝ)
    (hd : HasDerivAt (fun h => ∫ V, f V ∂PeriodicGroundBridge.law β (L h) (R h)) v t) :
    HasDerivAt (fun h => ∫ V, f V
      ∂PeriodicGroundBridge.law β (gaugeAction (a h) (L h)) (gaugeAction (b h) (R h))) v t := by
  rw [curve_expectation]
  exact hd

/-- On the actual bounded core the existing score reconstruction transports
with the full curve. It does NOT become the untransported fixed-axis score at
the gauge-transformed base representatives. -/
theorem transported_physical_derivative (β : ℝ) (U W : State) (a b : ℝ → Gauge)
    (f : State → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ V, |f V| ≤ M) :
    HasDerivAt (fun h => ∫ V, f V ∂PeriodicGroundBridge.law β
      (gaugeAction (a h) (left h U)) (gaugeAction (b h) (right h W)))
      (∫ V, f V * physicalScore β U W V ∂PeriodicGroundBridge.law β U W) 0 := by
  exact curve_derivative β (fun h => left h U) (fun h => right h W) a b f _ _
    (physical_derivative β U W f hf M hM hb)

/-- The endpoint descent obstruction holds on a proved large-coupling tail,
not at beta zero or by an assumed all-positive-beta coefficient theorem. -/
theorem eventual_no_fixed_axis_descent : ∀ᶠ β : ℝ in atTop,
    ¬ ∀ (a b : Gauge) (U W : State),
      physicalScore β (gaugeAction a U) (gaugeAction b W) =ᵐ[PeriodicGroundBridge.law β U W]
        physicalScore β U W := by
  have hc := (tendsto_order.mp SU2WilsonConvolution.coefficient_tendsto_one).1
    (1/2 : ℝ) (by norm_num)
  filter_upwards [hc, eventually_ge_atTop (0 : ℝ)] with β hα hβ
  exact no_fixed_axis_endpoint_descent β hβ (ne_of_gt (by linarith))

end OperatorDerivativeRewrite.Foundation.PeriodicEndpointTangentDescent
