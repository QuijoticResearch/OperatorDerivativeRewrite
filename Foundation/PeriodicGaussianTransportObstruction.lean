import Foundation.PeriodicGaussianTransferGram
import Foundation.PeriodicLogActionMoment
/-! The actual Wilson Gaussian Gram map is not an isometric transport.
This excludes that specific route to Gaussian closed-operator calculus, not
other intertwiners or a physical mass gap. All claims concern the native
finite periodic Wilson transfer and a bounded gauge-invariant plaquette. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicGaussianTransportObstruction
open PeriodicTemporalSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicCurvatureVariance PeriodicCurvatureTransfer PeriodicGaussianTransferGram

variable {β : ℝ} (g : GroundData β)
private instance probability : IsProbabilityMeasure g.stationary := g.stationary_probability

/-- A pointwise representative, so the Gaussian feature formula applies on its proved core. -/
def probe (p : SpatialFace) (U : State) : ℝ := ‖vector g p‖⁻¹ * centered g p U

theorem probe_measurable (p : SpatialFace) : Measurable (probe g p) :=
  measurable_const.mul ((plaquette_measurable p).sub measurable_const)

theorem probe_memLp (p : SpatialFace) : MemLp (probe g p) 2 g.stationary :=
  (centered_memLp g p).const_smul ‖vector g p‖⁻¹

theorem probe_toLp (p : SpatialFace) : (probe_memLp g p).toLp (probe g p)=normalized g p := by
  exact MemLp.toLp_const_smul (𝕜 := ℝ) ‖vector g p‖⁻¹ (centered_memLp g p)

theorem probe_bounded (p : SpatialFace) :
    ∀ U, |probe g p U| ≤ |‖vector g p‖⁻¹| * (1+|∫ V,plaquette p V ∂g.stationary|) := by
  intro U
  unfold probe centered
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (abs_sub _ _).trans (add_le_add (QuaternionSU2Representation.halfTrace_bound _) le_rfl)

theorem probe_gauge (p : SpatialFace) (a : Gauge) (U : State) :
    probe g p (PeriodicSlabGauge.gaugeAction a U)=probe g p U := by
  unfold probe centered
  rw [plaquette_gauge]

/-- The exact normalized squared Gaussian feature norm, with the native ground retained. -/
def featureEnergy (f : State → ℝ) : ℝ :=
  (1/(g.value*g.normalizer))*
    ‖∫ U, (PeriodicLocalGroundHarnack.dressed g U*f U) •
      wilsonFeature β U ∂PeriodicWilsonSlab.boundaryHaar‖^2

theorem probe_feature_energy (hb : 0 ≤ β) (p : SpatialFace) :
    featureEnergy g (probe g p)=inner ℝ (operator g (normalized g p)) (normalized g p) := by
  have h := native_gram hb g (probe g p) (probe_measurable g p) (probe_memLp g p)
    _ (probe_bounded g p) (probe_gauge g p)
  rw [probe_toLp] at h
  exact h.symm

/-- A strict, quantitative failure of native norm preservation on an actual physical probe. -/
theorem probe_feature_loss (hb : 16777216 ≤ β) (p : SpatialFace) :
    featureEnergy g (probe g p)+3/(2401*PeriodicLogActionMoment.squareConstant) ≤ 1 := by
  rw [probe_feature_energy g (by linarith) p]
  have h := (PeriodicLogActionMoment.plaquette_native_loss hb g p).2.1
  unfold SelfAdjointContractionIteration.dissipation at h
  rw [real_inner_self_eq_norm_sq,normalized_norm] at h
  linarith

/-- No isometry into any Hilbert target can realize this Gram norm on the proved physical core.
This is a statement about this Wilson feature map, not about arbitrary Hilbert equivalences. -/
theorem no_isometric_gram_transport (hb : 16777216 ≤ β)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    ¬ ∃ J : StateL2 g →ₗᵢ[ℝ] H,
      ∀ (f : State → ℝ) (_hf : Measurable f) (hm : MemLp f 2 g.stationary)
        (B : ℝ) (_hB : ∀ U, |f U| ≤ B)
        (_hInv : ∀ a U, f (PeriodicSlabGauge.gaugeAction a U)=f U),
      ‖J (hm.toLp f)‖^2=featureEnergy g f := by
  rintro ⟨J,hJ⟩
  let p : SpatialFace := ⟨(0,(0,1)),by decide⟩
  have he := hJ (probe g p) (probe_measurable g p) (probe_memLp g p)
    _ (probe_bounded g p) (probe_gauge g p)
  rw [probe_toLp,J.norm_map,normalized_norm] at he
  have hl := probe_feature_loss g hb p
  have hp : 0 < 3/(2401*PeriodicLogActionMoment.squareConstant) := by
    exact div_pos (by norm_num) (mul_pos (by norm_num) PeriodicLogActionMoment.squareConstant_pos)
  norm_num only [one_pow] at he
  linarith
end OperatorDerivativeRewrite.Foundation.PeriodicGaussianTransportObstruction
