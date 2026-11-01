import Foundation.PeriodicEndpointTangentDescent
/-! Exchange-blind first-order boundary directions in the actual Wilson bridge.
An explicit gauge-invariant winding signal changes to first order while every
bounded middle observable has zero first response. Higher responses are not
asserted to vanish, and no averaged or continuum gap conclusion is drawn. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicBridgeExchangeObstruction
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicEndpointScore PeriodicEndpointFibreWitness PeriodicPhysicalBridgeScore
attribute [local irreducible] kernel boundaryHaar gaugeHaar spatialAction temporalAction

/-- Endpoint exchange is an exact symmetry of the normalized actual bridge. -/
theorem law_swap (β : ℝ) (U W : State) :
    PeriodicGroundBridge.law β U W = PeriodicGroundBridge.law β W U := by
  have he : PeriodicGroundBridge.bridgeWeight β U W = PeriodicGroundBridge.bridgeWeight β W U := by
    funext V
    unfold PeriodicGroundBridge.bridgeWeight
    rw [kernel_symmetric β U V, kernel_symmetric β V W]
    exact mul_comm _ _
  unfold PeriodicGroundBridge.law
  rw [he]

/-- ALL opposite endpoint paths, not just one Lie-algebra axis, give an even
middle law. No differentiability or independence of the paths is assumed. -/
theorem opposite_law_even (β : ℝ) (X : ℝ → State) (h : ℝ) :
    PeriodicGroundBridge.law β (X h) (X (-h)) =
      PeriodicGroundBridge.law β (X (-h)) (X (-(-h))) := by
  rw [neg_neg]
  exact law_swap β _ _

/-- If a first derivative along ANY opposite path exists, it is zero for
every fixed middle test. Integrability and existence are not manufactured. -/
theorem opposite_derivative_zero (β : ℝ) (X : ℝ → State) (f : State → ℝ) (v : ℝ)
    (hd : HasDerivAt (fun h => ∫ V, f V
      ∂PeriodicGroundBridge.law β (X h) (X (-h))) v 0) : v = 0 := by
  let F := fun h : ℝ => ∫ V, f V ∂PeriodicGroundBridge.law β (X h) (X (-h))
  have he : (fun h => F (-h)) = F := by
    funext h
    dsimp only [F]
    rw [neg_neg, law_swap]
  have hd0 : HasDerivAt F v (-(0 : ℝ)) := by simpa only [neg_zero] using hd
  have hn := hd0.comp 0 (hasDerivAt_neg (0 : ℝ))
  change HasDerivAt (fun h => F (-h)) _ 0 at hn
  rw [he] at hn
  have hu := hd.unique hn
  nlinarith

def path (h : ℝ) : State := right (-h) leftEndpoint

def boundarySignal (U W : State) : ℝ :=
  PeriodicCenteredHolonomy.first U - PeriodicCenteredHolonomy.first W

def signal (h : ℝ) : ℝ := boundarySignal (path h) (path (-h))

theorem path_zero : path 0 = leftEndpoint := by
  have ha : SU2JointPlaquetteCubic.axis 0 0 = 1 := by
    apply Subtype.ext
    change (SU2JointPlaquetteCubic.axis 0 0 : SU2TraceHessianModel.M2) = 1
    simp [SU2AxisMatrixJets.axis_matrix_formula]
  funext e
  simp only [path, right, neg_zero, ha, mul_one]

/-- This boundary signal is physical: each endpoint may be gauge transformed
independently, without changing the signal. -/
theorem boundarySignal_gauge (a b : Gauge) (U W : State) :
    boundarySignal (gaugeAction a U) (gaugeAction b W) = boundarySignal U W := by
  unfold boundarySignal PeriodicCenteredHolonomy.first
  rw [PeriodicSpatialHolonomy.trace_gauge, PeriodicSpatialHolonomy.trace_gauge]

theorem path_winding (h : ℝ) : PeriodicCenteredHolonomy.first (path h) = Real.sin (4*h) :=
  PeriodicWindingEndpointResponse.winding_curve h

theorem signal_exact (h : ℝ) : signal h = 2 * Real.sin (4*h) := by
  unfold signal boundarySignal
  rw [path_winding, path_winding, mul_neg, Real.sin_neg]
  ring

theorem signal_derivative : HasDerivAt signal 8 0 := by
  have he : signal = (fun h : ℝ => 2 * Real.sin (4*h)) := funext signal_exact
  rw [he]
  convert ((hasDerivAt_id (0 : ℝ)).const_mul 4).sin.const_mul 2 using 1 <;> norm_num

/-- The opposite endpoint configurations are not gauge equivalent for these
small positive parameters. This is more than a pure-gauge source direction. -/
theorem path_not_gauge (h : ℝ) (h0 : 0 < h) (h1 : h < Real.pi / 4) :
    ¬ ∃ a : Gauge, gaugeAction a (path h) = path (-h) := by
  rintro ⟨a, ha⟩
  have ht := congrArg PeriodicCenteredHolonomy.first ha
  have hg : PeriodicCenteredHolonomy.first (gaugeAction a (path h)) =
      PeriodicCenteredHolonomy.first (path h) :=
    PeriodicSpatialHolonomy.trace_gauge a (path h) PeriodicCenteredHolonomy.origin 0
  rw [hg, path_winding, path_winding, mul_neg, Real.sin_neg] at ht
  have hs := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < 4*h) (by linarith : 4*h < Real.pi)
  linarith

/-- The explicit opposite path is the existing coherent diagonal response
after the exact endpoint gauge change. The actual normalizers are retained. -/
theorem coherent_law (β h : ℝ) :
    PeriodicGroundBridge.law β (left h leftEndpoint) (right h leftEndpoint) =
      PeriodicGroundBridge.law β (path h) (path (-h)) := by
  have he : PeriodicGroundBridge.bridgeWeight β (left h leftEndpoint) (right h leftEndpoint) =
      PeriodicGroundBridge.bridgeWeight β (path h) (path (-h)) := by
    funext V
    unfold PeriodicGroundBridge.bridgeWeight path
    rw [kernel_left_right, neg_neg]
  unfold PeriodicGroundBridge.law
  rw [he]

/-- Here existence IS established on the actual bounded middle core by the
existing Wilson derivative theorem, rather than assumed from symmetry. -/
theorem actual_derivative_zero (β : ℝ) (f : State → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) :
    HasDerivAt (fun h => ∫ V, f V ∂PeriodicGroundBridge.law β (path h) (path (-h))) 0 0 := by
  have he : (fun h => ∫ V, f V
      ∂PeriodicGroundBridge.law β (left h leftEndpoint) (right h leftEndpoint)) =
      (fun h => ∫ V, f V ∂PeriodicGroundBridge.law β (path h) (path (-h))) := by
    funext h
    rw [coherent_law]
  have hd := physical_derivative β leftEndpoint leftEndpoint f hf M hM hb
  rw [he] at hd
  have hz := opposite_derivative_zero β path f _ hd
  rw [hz] at hd
  exact hd

/-- No positive pointwise first-order Fisher budget controls even this one
gauge-invariant boundary signal. This is not an endpoint-averaged statement. -/
theorem no_positive_signal_budget (β c : ℝ) (hc : 0 < c) :
    ¬ c * (deriv signal 0)^2 ≤
      ∫ V, (physicalScore β leftEndpoint leftEndpoint V)^2
        ∂PeriodicGroundBridge.law β leftEndpoint leftEndpoint := by
  rw [signal_derivative.deriv, diagonal_physical_energy_zero]
  intro hh
  norm_num at hh
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicBridgeExchangeObstruction
