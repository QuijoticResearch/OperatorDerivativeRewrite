import Foundation.PeriodicNativeCompression
import Foundation.PeriodicGaugeSaturatedGround

/-! Gauge covariance of the native Wilson compression requires the actual
compensated transformation of BOTH temporal fields, not Haar independence. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.PeriodicGaugeCompression
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicNativeCompression HilbertRepresentation
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar
  PeriodicGroundBridge.law PeriodicAugmentedBridge.law PeriodicLinkDisintegration.marginal

def middle (g : Gauge) : State ≃ᵐ State := PeriodicGaugeSaturatedGround.gaugeEquiv g

def joint (g : Gauge) : PeriodicAugmentedBridge.Space ≃ᵐ PeriodicAugmentedBridge.Space :=
  (middle g).prodCongr ((MeasurableEquiv.mulRight g⁻¹).prodCongr (MeasurableEquiv.mulLeft g))

def rest (e : SpatialEdge) (g : Gauge) :
    PeriodicLinkDisintegration.Rest e ≃ᵐ PeriodicLinkDisintegration.Rest e :=
  ((MeasurableEquiv.mulLeft (fun j : {j : SpatialEdge // j ≠ e} => g j.val.1)).trans
    (MeasurableEquiv.mulRight (fun j : {j : SpatialEdge // j ≠ e} =>
      (g (shift j.val.1 j.val.2))⁻¹))).prodCongr
        ((MeasurableEquiv.mulRight g⁻¹).prodCongr (MeasurableEquiv.mulLeft g))

theorem middle_apply (g : Gauge) (V : State) : middle g V = gaugeAction g V := rfl

theorem joint_apply (g : Gauge) (q : PeriodicAugmentedBridge.Space) :
    joint g q = (gaugeAction g q.1,(q.2.1*g⁻¹,g*q.2.2)) := rfl

theorem rest_square (e : SpatialEdge) (g : Gauge) (q : PeriodicAugmentedBridge.Space) :
    ((PeriodicLinkDisintegration.split e) (joint g q)).1 =
      rest e g (((PeriodicLinkDisintegration.split e) q).1) := rfl

/-- The original density is invariant only with the temporal compensation. -/
theorem density_invariant (g : Gauge) (β : ℝ) (U W : State)
    (q : PeriodicAugmentedBridge.Space) :
    PeriodicAugmentedBridge.density β U W (joint g q) =
      PeriodicAugmentedBridge.density β U W q := by
  simp only [joint_apply, PeriodicAugmentedBridge.density]
  rw [weight_right, weight_left]
  simp only [inv_mul_cancel_right]

theorem reference_preserving (g : Gauge) :
    MeasurePreserving (joint g) PeriodicAugmentedBridge.reference PeriodicAugmentedBridge.reference :=
  (PeriodicGaugeSaturatedGround.action_boundary_preserving g).prod
    ((gauge_right_preserving g⁻¹).prod (gauge_left_preserving g))

theorem joint_preserving (g : Gauge) (β : ℝ) (U W : State) :
    MeasurePreserving (joint g) (PeriodicAugmentedBridge.law β U W)
      (PeriodicAugmentedBridge.law β U W) := by
  refine ⟨(joint g).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [Measure.map_apply (joint g).measurable hs]
  change (PeriodicAugmentedBridge.law β U W).real ((joint g) ⁻¹' s) =
    (PeriodicAugmentedBridge.law β U W).real s
  rw [← integral_indicator_one (μ := PeriodicAugmentedBridge.law β U W)
      (hs.preimage (joint g).measurable),
    ← integral_indicator_one (μ := PeriodicAugmentedBridge.law β U W) hs]
  rw [PeriodicAugmentedBridge.integral_formula, PeriodicAugmentedBridge.integral_formula]
  congr 1
  have h := (reference_preserving g).integral_comp' (fun q =>
    PeriodicAugmentedBridge.density β U W q*s.indicator (1 : PeriodicAugmentedBridge.Space → ℝ) q)
  rw [← h]
  apply integral_congr_ae
  filter_upwards with q
  rw [density_invariant]
  congr 1

theorem middle_preserving (g : Gauge) (β : ℝ) (U W : State) :
    MeasurePreserving (middle g) (PeriodicGroundBridge.law β U W)
      (PeriodicGroundBridge.law β U W) := by
  refine ⟨(middle g).measurable, ?_⟩
  have h := ((PeriodicAugmentedBridge.projection_preserving β U W).comp
    (joint_preserving g β U W)).map_eq
  have hc := (PeriodicAugmentedBridge.projection_preserving β U W).map_eq
  change Measure.map ((middle g) ∘ Prod.fst) (PeriodicAugmentedBridge.law β U W) = _ at h
  rw [← Measure.map_map (middle g).measurable measurable_fst, hc] at h
  exact h

theorem rest_preserving (e : SpatialEdge) (g : Gauge) (β : ℝ) (U W : State) :
    MeasurePreserving (rest e g) (PeriodicLinkDisintegration.marginal e β U W)
      (PeriodicLinkDisintegration.marginal e β U W) := by
  refine ⟨(rest e g).measurable, ?_⟩
  have hp := PeriodicConditionalEndpointScore.rest_preserving e β U W
  have h := (hp.comp (joint_preserving g β U W)).map_eq
  have he : (fun q => ((PeriodicLinkDisintegration.split e) q).1) ∘ joint g =
      rest e g ∘ (fun q => ((PeriodicLinkDisintegration.split e) q).1) := by
    funext q
    exact rest_square e g q
  rw [he, ← Measure.map_map (rest e g).measurable hp.measurable, hp.map_eq] at h
  exact h

private def pullbackEquiv {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a : α ≃ᵐ α) (ha : MeasurePreserving a μ μ) : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℝ a ha) (by
    intro f
    refine ⟨Lp.compMeasurePreserving a.symm (MeasurePreserving.symm a ha) f, ?_⟩
    change Lp.compMeasurePreserving a ha
      (Lp.compMeasurePreserving a.symm (MeasurePreserving.symm a ha) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    have he : a.symm ∘ a = id := funext a.symm_apply_apply
    simpa only [he, Lp.compMeasurePreserving_id_apply])

private theorem pullback_square {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure γ) (p : α → γ) (hp : MeasurePreserving p μ ν)
    (a : α ≃ᵐ α) (ha : MeasurePreserving a μ μ)
    (b : γ ≃ᵐ γ) (hb : MeasurePreserving b ν ν)
    (h : ∀ x, p (a x) = b (p x)) (f : Lp ℝ 2 ν) :
    pullbackEquiv μ a ha (Lp.compMeasurePreserving p hp f) =
      Lp.compMeasurePreserving p hp (pullbackEquiv ν b hb f) := by
  change Lp.compMeasurePreserving a ha (Lp.compMeasurePreserving p hp f) =
    Lp.compMeasurePreserving p hp (Lp.compMeasurePreserving b hb f)
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  have he : p ∘ a = b ∘ p := funext h
  simp only [he]

def middleUnitary (g : Gauge) (β : ℝ) (U W : State) : Middle β U W ≃ₗᵢ[ℝ] Middle β U W :=
  pullbackEquiv _ (middle g) (middle_preserving g β U W)

def jointUnitary (g : Gauge) (β : ℝ) (U W : State) : Joint β U W ≃ₗᵢ[ℝ] Joint β U W :=
  pullbackEquiv _ (joint g) (joint_preserving g β U W)

def restUnitary (e : SpatialEdge) (g : Gauge) (β : ℝ) (U W : State) :
    Rest e β U W ≃ₗᵢ[ℝ] Rest e β U W :=
  pullbackEquiv _ (rest e g) (rest_preserving e g β U W)

/-- Pointwise gauge invariance genuinely gives native AE invariance on L2. -/
theorem middleUnitary_fixed_of_pointwise (g : Gauge) (β : ℝ) (U W : State)
    (f : State → ℝ) (hm : MemLp f 2 (PeriodicGroundBridge.law β U W))
    (hf : ∀ V, f (gaugeAction g V) = f V) :
    middleUnitary g β U W (hm.toLp f) = hm.toLp f := by
  apply Lp.ext
  have h1 := (hm.comp_measurePreserving (middle_preserving g β U W)).coeFn_toLp
  filter_upwards [h1, hm.coeFn_toLp] with V hl hr
  exact hl.trans ((hf V).trans hr.symm)

theorem middle_intertwine (g : Gauge) (β : ℝ) (U W : State) (f : Middle β U W) :
    jointUnitary g β U W (middleLift β U W f) =
      middleLift β U W (middleUnitary g β U W f) :=
  pullback_square _ _ Prod.fst (PeriodicAugmentedBridge.projection_preserving β U W)
    (joint g) (joint_preserving g β U W) (middle g) (middle_preserving g β U W)
    (fun _ => rfl) f

theorem rest_intertwine (e : SpatialEdge) (g : Gauge) (β : ℝ) (U W : State)
    (f : Rest e β U W) :
    jointUnitary g β U W (restLift e β U W f) =
      restLift e β U W (restUnitary e g β U W f) :=
  pullback_square _ _ (fun q => ((PeriodicLinkDisintegration.split e) q).1)
    (PeriodicConditionalEndpointScore.rest_preserving e β U W)
    (joint g) (joint_preserving g β U W) (rest e g) (rest_preserving e g β U W)
    (rest_square e g) f

theorem channel_covariant (e : SpatialEdge) (g : Gauge) (β : ℝ) (U W : State)
    (f : Middle β U W) :
    channel e β U W (middleUnitary g β U W f) =
      restUnitary e g β U W (channel e β U W f) := by
  apply ext_inner_right ℝ
  intro h
  calc
    _ = inner ℝ (middleLift β U W (middleUnitary g β U W f)) (restLift e β U W h) :=
      channel_pairing e β U W _ h
    _ = inner ℝ (jointUnitary g β U W (middleLift β U W f))
        (jointUnitary g β U W (restLift e β U W ((restUnitary e g β U W).symm h))) := by
      rw [middle_intertwine, rest_intertwine, LinearIsometryEquiv.apply_symm_apply]
    _ = inner ℝ (middleLift β U W f)
        (restLift e β U W ((restUnitary e g β U W).symm h)) :=
      (jointUnitary g β U W).inner_map_map _ _
    _ = inner ℝ (channel e β U W f) ((restUnitary e g β U W).symm h) :=
      (channel_pairing e β U W f _).symm
    _ = _ := ((restUnitary e g β U W).inner_map_eq_flip _ _).symm

theorem compression_covariant (e : SpatialEdge) (g : Gauge) (β : ℝ) (U W : State)
    (f : Middle β U W) :
    compression e β U W (middleUnitary g β U W f) =
      middleUnitary g β U W (compression e β U W f) := by
  apply ext_inner_right ℝ
  intro h
  have ht : restUnitary e g β U W
      (channel e β U W ((middleUnitary g β U W).symm h)) = channel e β U W h := by
    rw [← channel_covariant, LinearIsometryEquiv.apply_symm_apply]
  calc
    _ = inner ℝ (restUnitary e g β U W (channel e β U W f)) (channel e β U W h) := by
      rw [compression_pairing, channel_covariant]
    _ = inner ℝ (channel e β U W f)
        (channel e β U W ((middleUnitary g β U W).symm h)) := by
      rw [← ht, (restUnitary e g β U W).inner_map_map]
    _ = inner ℝ (compression e β U W f) ((middleUnitary g β U W).symm h) :=
      (compression_pairing e β U W f _).symm
    _ = _ := ((middleUnitary g β U W).inner_map_eq_flip _ _).symm

/-- The exact AE gauge-invariant native domain is preserved. No gauge fixing. -/
theorem compression_preserves_physical (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : Middle β U W) (hf : ∀ g, middleUnitary g β U W f = f) :
    ∀ g, middleUnitary g β U W (compression e β U W f) = compression e β U W f := by
  intro g
  rw [← compression_covariant, hf]

theorem residual_covariant (e : SpatialEdge) (g : Gauge) (β : ℝ) (U W : State)
    (f : Middle β U W) :
    residual e β U W (middleUnitary g β U W f) =
      jointUnitary g β U W (residual e β U W f) := by
  change middleLift β U W (middleUnitary g β U W f) -
    restLift e β U W (channel e β U W (middleUnitary g β U W f)) =
    jointUnitary g β U W (middleLift β U W f-restLift e β U W (channel e β U W f))
  rw [map_sub, middle_intertwine, rest_intertwine, channel_covariant]

theorem residual_energy_invariant (e : SpatialEdge) (g : Gauge) (β : ℝ) (U W : State)
    (f : Middle β U W) :
    ‖residual e β U W (middleUnitary g β U W f)‖^2 = ‖residual e β U W f‖^2 := by
  rw [residual_covariant, LinearIsometryEquiv.norm_map]

end OperatorDerivativeRewrite.Foundation.PeriodicGaugeCompression
