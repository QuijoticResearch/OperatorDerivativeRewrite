import Foundation.PeriodicConditionalCurvatureIdentification
import Foundation.PeriodicLowActionBlock
/-! Original middle-L2 nontriviality of the actual physical second channel.
No pointwise separation is promoted to native energy before continuity and
strictly positive actual middle density have been verified. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.PeriodicNativeSecondChannel
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab
open PeriodicTemporalLaplaceContrast PeriodicConditionalCurvatureIdentification
attribute [local irreducible] gaugeHaar boundaryHaar kernel spatialAction temporalAction

private instance boundary_open : boundaryHaar.IsOpenPosMeasure := by unfold boundaryHaar; infer_instance

private theorem trace_joint_continuous (U : State) :
    Continuous (fun q : State × Gauge => PeriodicTemporalParity.traceSum U q.1 q.2) := by
  unfold PeriodicTemporalParity.traceSum
  apply continuous_finsetSum
  intro e _
  exact PeriodicLowActionBlock.trace_continuous.comp (by unfold temporalWord; fun_prop)

private theorem integral_continuous (F : State × Gauge → ℝ) (hF : Continuous F) :
    Continuous (fun V => ∫ a, F (V,a) ∂gaugeHaar) := by
  have hh := continuous_parametric_integral_of_continuous (μ := gaugeHaar)
    (f := fun V a => F (V,a)) hF (s := Set.univ) isCompact_univ
  simpa only [Measure.restrict_univ] using hh

theorem partition_continuous (β : ℝ) (U : State) : Continuous (partition β U) := by
  have hh := integral_continuous (fun q => Real.exp (β*PeriodicTemporalParity.traceSum U q.1 q.2))
    (Real.continuous_exp.comp ((trace_joint_continuous U).const_mul β))
  have he : partition β U=(fun V => ∫ a, Real.exp (β*PeriodicTemporalParity.traceSum U V a) ∂gaugeHaar) := by
    funext V
    simp only [partition,PeriodicTemporalLaplaceContrast.weighted,one_mul]
  rw [he]
  exact hh

private theorem cTrace_joint_continuous (h : ℝ) (U : State) :
    Continuous (fun q : State × Gauge => cTrace h U q.1 q.2) := trace_joint_continuous _

private theorem dTrace_joint_continuous (h : ℝ) (U : State) :
    Continuous (fun q : State × Gauge => dTrace h U q.1 q.2) := by
  exact ((trace_joint_continuous U).const_mul (-Real.sin h)).add
    ((trace_joint_continuous _).const_mul (Real.cos h))

theorem firstJet_continuous (β : ℝ) (U : State) (h : ℝ) :
    Continuous (fun V => firstJet β U V h) := by
  exact integral_continuous _ ((Real.continuous_exp.comp ((cTrace_joint_continuous h U).const_mul β)).mul
    ((dTrace_joint_continuous h U).const_mul β))

theorem secondJet_continuous (β : ℝ) (U : State) (h : ℝ) :
    Continuous (fun V => secondJet β U V h) := by
  exact integral_continuous _ ((Real.continuous_exp.comp ((cTrace_joint_continuous h U).const_mul β)).mul
    ((((dTrace_joint_continuous h U).const_mul β).pow 2).sub
      ((cTrace_joint_continuous h U).const_mul β)))

theorem logCurvature_continuous (β : ℝ) (U : State) (h : ℝ) :
    Continuous (fun V => logCurvature β U V h) := by
  unfold logCurvature
  exact ((secondJet_continuous β U h).div (partition_continuous β _) (fun V =>
    (partition_pos β _ V).ne')).sub (((firstJet_continuous β U h).div
      (partition_continuous β _) (fun V => (partition_pos β _ V).ne')).pow 2)

theorem physical_second_continuous (β : ℝ) (U : State) :
    Continuous (PeriodicEndpointSecondResponse.physicalSecond β U U) := by
  have he : PeriodicEndpointSecondResponse.physicalSecond β U U = (fun V =>
      2*logCurvature β U V 0+
        (PeriodicEndpointSecondResponse.physicalSecond β U U 1-2*logCurvature β U 1 0)) := by
    funext V
    have hh := physical_second_contrast β U V 1
    linarith
  rw [he]
  exact (continuous_const.mul (logCurvature_continuous β U 0)).add continuous_const

theorem middle_ae_iff (β : ℝ) (U W : State) (P : State → Prop) :
    (∀ᵐ V ∂PeriodicGroundBridge.law β U W, P V) ↔ ∀ᵐ V ∂boundaryHaar, P V := by
  rw [PeriodicGroundBridge.law_withDensity,ae_withDensity_iff
    ((PeriodicGroundBridge.bridgeWeight_measurable β U W).div_const _).ennreal_ofReal]
  constructor
  · intro hh
    filter_upwards [hh] with V hV
    exact hV (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos
      (PeriodicGroundBridge.bridgeWeight_pos β U W V) (PeriodicGroundBridge.normalizer_pos β U W))))
  · intro hh
    filter_upwards [hh] with V hV
    exact fun _ => hV

theorem physical_energy_positive_of_separation (β : ℝ) (U V W : State)
    (hne : PeriodicEndpointSecondResponse.physicalSecond β U U V ≠
      PeriodicEndpointSecondResponse.physicalSecond β U U W) :
    0 < ∫ X, (PeriodicEndpointSecondResponse.physicalSecond β U U X)^2
      ∂PeriodicGroundBridge.law β U U := by
  let ψ := PeriodicEndpointSecondResponse.physicalSecond β U U
  let μ := PeriodicGroundBridge.law β U U
  by_contra hn
  have hz : (∫ X, (ψ X)^2 ∂μ)=0 :=
    le_antisymm (not_lt.mp hn) (integral_nonneg (fun X => sq_nonneg _))
  have hAE := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun X => sq_nonneg (ψ X)))
    (PeriodicEndpointSecondResponse.physicalSecond_memLp β U U).integrable_sq).mp hz
  have hzero : ∀ᵐ X ∂μ, ψ X=0 := by
    filter_upwards [hAE] with X hX
    change (ψ X)^2=0 at hX
    nlinarith
  have hHaar := (middle_ae_iff β U U (fun X => ψ X=0)).mp hzero
  have heq := Measure.eq_of_ae_eq hHaar (physical_second_continuous β U) continuous_const
  apply hne
  change ψ V=ψ W
  rw [congrFun heq V,congrFun heq W]

theorem eventual_physical_energy : ∀ᶠ β : ℝ in 𝓝[≠] 0,
    ∃ t ∈ Set.Ioo (-Real.pi/4) (Real.pi/4),
      0 < ∫ V, (PeriodicEndpointSecondResponse.physicalSecond β
        (PeriodicTemporalCycleMoment.orbit t) (PeriodicTemporalCycleMoment.orbit t) V)^2
        ∂PeriodicGroundBridge.law β (PeriodicTemporalCycleMoment.orbit t)
          (PeriodicTemporalCycleMoment.orbit t) := by
  filter_upwards [eventual_physical_second_separation] with β hh
  obtain ⟨t,ht,hsep⟩ := hh
  refine ⟨t,ht,physical_energy_positive_of_separation β (PeriodicTemporalCycleMoment.orbit t)
    1 (PeriodicCenterSeam.flip 1 1) ?_⟩
  intro he
  rw [he,sub_self] at hsep
  exact (lt_irrefl (0 : ℝ)) hsep

theorem eventual_first_zero_second_positive : ∀ᶠ β : ℝ in 𝓝[≠] 0,
    ∃ t ∈ Set.Ioo (-Real.pi/4) (Real.pi/4),
      (∫ V, (PeriodicPhysicalBridgeScore.physicalScore β (PeriodicTemporalCycleMoment.orbit t)
        (PeriodicTemporalCycleMoment.orbit t) V)^2 ∂PeriodicGroundBridge.law β
          (PeriodicTemporalCycleMoment.orbit t) (PeriodicTemporalCycleMoment.orbit t))=0 ∧
      0 < ∫ V, (PeriodicEndpointSecondResponse.physicalSecond β (PeriodicTemporalCycleMoment.orbit t)
        (PeriodicTemporalCycleMoment.orbit t) V)^2 ∂PeriodicGroundBridge.law β
          (PeriodicTemporalCycleMoment.orbit t) (PeriodicTemporalCycleMoment.orbit t) := by
  filter_upwards [eventual_physical_energy] with β hh
  obtain ⟨t,ht,hpos⟩ := hh
  exact ⟨t,ht,PeriodicPhysicalBridgeScore.diagonal_physical_energy_zero β _,hpos⟩

theorem physical_energy_bound (β : ℝ) (U W : State) :
    (∫ V, (PeriodicEndpointSecondResponse.physicalSecond β U W V)^2
      ∂PeriodicGroundBridge.law β U W) ≤ (6*(384*|β|)^2+2*(384*|β|))^2 := by
  have hp (V : State) : (PeriodicEndpointSecondResponse.physicalSecond β U W V)^2 ≤
      (6*(384*|β|)^2+2*(384*|β|))^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2
      (PeriodicEndpointSecondResponse.physicalSecond_bound β U W V)
  have hh := integral_mono (PeriodicEndpointSecondResponse.physicalSecond_memLp β U W).integrable_sq
    (integrable_const ((6*(384*|β|)^2+2*(384*|β|))^2)) hp
  simpa only [integral_const,probReal_univ,one_smul] using hh

/-- Uniform original-norm degeneration at beta0, even for arbitrary endpoint
families. This excludes an unrenormalized coupling-uniform positive floor here. -/
theorem physical_energy_tendsto (U W : ℝ → State) :
    Tendsto (fun β => ∫ V, (PeriodicEndpointSecondResponse.physicalSecond β (U β) (W β) V)^2
      ∂PeriodicGroundBridge.law β (U β) (W β)) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun β : ℝ => (6*(384*|β|)^2+2*(384*|β|))^2) := by fun_prop
  have ht : Tendsto (fun β : ℝ => (6*(384*|β|)^2+2*(384*|β|))^2) (𝓝 0) (𝓝 0) := by
    simpa only [abs_zero,mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero] using hc.tendsto 0
  exact squeeze_zero' (Eventually.of_forall (fun β => integral_nonneg (fun V => sq_nonneg _)))
    (Eventually.of_forall (fun β => physical_energy_bound β (U β) (W β))) ht

theorem no_uniform_positive_energy_floor (U W : ℝ → State) (c : ℝ) (hc : 0<c) :
    ¬ (∀ᶠ β : ℝ in 𝓝[≠] 0, c ≤ ∫ V,
      (PeriodicEndpointSecondResponse.physicalSecond β (U β) (W β) V)^2
        ∂PeriodicGroundBridge.law β (U β) (W β)) := by
  intro hlow
  have ht : Tendsto (fun β => ∫ V,
      (PeriodicEndpointSecondResponse.physicalSecond β (U β) (W β) V)^2
        ∂PeriodicGroundBridge.law β (U β) (W β)) (𝓝[≠] 0) (𝓝 0) :=
    (physical_energy_tendsto U W).mono_left nhdsWithin_le_nhds
  have hs := ht.eventually (gt_mem_nhds hc)
  obtain ⟨β,hb,hsmall⟩ := (hlow.and hs).exists
  exact (not_lt_of_ge hb) hsmall

theorem eventual_positive_second_response : ∀ᶠ β : ℝ in 𝓝[≠] 0,
    ∃ t ∈ Set.Ioo (-Real.pi/4) (Real.pi/4),
      0 < deriv (deriv (fun h => ∫ V, PeriodicEndpointSecondResponse.physicalSecond β
        (PeriodicTemporalCycleMoment.orbit t) (PeriodicTemporalCycleMoment.orbit t) V
        ∂PeriodicGroundBridge.law β (PeriodicEndpointScore.left h (PeriodicTemporalCycleMoment.orbit t))
          (PeriodicEndpointScore.right h (PeriodicTemporalCycleMoment.orbit t)))) 0 := by
  filter_upwards [eventual_physical_energy] with β hh
  obtain ⟨t,ht,hpos⟩ := hh
  refine ⟨t,ht,?_⟩
  rw [(PeriodicEndpointSecondResponse.frozen_second_derivative β
    (PeriodicTemporalCycleMoment.orbit t) (PeriodicTemporalCycleMoment.orbit t)).deriv]
  exact hpos

private theorem curvature_affine (β : ℝ) (U : State) :
    (fun V => logCurvature β U V 0)=(fun V =>
      (1/2 : ℝ)*PeriodicEndpointSecondResponse.physicalSecond β U U V+
        (logCurvature β U 1 0-(1/2 : ℝ)*PeriodicEndpointSecondResponse.physicalSecond β U U 1)) := by
  funext V
  have hh := physical_second_contrast β U V 1
  linarith

theorem logCurvature_memLp (β : ℝ) (U : State) :
    MemLp (fun V => logCurvature β U V 0) 2 (PeriodicGroundBridge.law β U U) := by
  rw [curvature_affine]
  exact ((PeriodicEndpointSecondResponse.physicalSecond_memLp β U U).const_mul (1/2 : ℝ)).add
    (memLp_const _)

/-- The ORIGINAL score is exactly the centered conditional-temporal cumulant,
with centering under the ORIGINAL TWO-sided physical middle law. -/
theorem physical_second_centered (β : ℝ) (U V : State) :
    PeriodicEndpointSecondResponse.physicalSecond β U U V =
      2*(logCurvature β U V 0-
        ∫ W, logCurvature β U W 0 ∂PeriodicGroundBridge.law β U U) := by
  have hi := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (PeriodicEndpointSecondResponse.physicalSecond_memLp β U U)
  have he : (∫ W, logCurvature β U W 0 ∂PeriodicGroundBridge.law β U U) =
      logCurvature β U 1 0-(1/2 : ℝ)*PeriodicEndpointSecondResponse.physicalSecond β U U 1 := by
    have hf := curvature_affine β U
    rw [hf]
    rw [integral_add (hi.const_mul _) (integrable_const _),integral_const_mul,
      PeriodicEndpointSecondResponse.physicalSecond_mean_zero,integral_const]
    simp only [probReal_univ,one_smul,mul_zero,zero_add]
  rw [he]
  have hh := physical_second_contrast β U V 1
  linarith

theorem physical_second_covariance (β : ℝ) (U : State) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ V, |f V| ≤ M) :
    (∫ V, f V*PeriodicEndpointSecondResponse.physicalSecond β U U V ∂PeriodicGroundBridge.law β U U) =
      2*((∫ V, f V*logCurvature β U V 0 ∂PeriodicGroundBridge.law β U U)-
        (∫ V, f V ∂PeriodicGroundBridge.law β U U)*
          ∫ V, logCurvature β U V 0 ∂PeriodicGroundBridge.law β U U) := by
  let μ := PeriodicGroundBridge.law β U U
  have hf2 : MemLp f 2 μ := by
    apply MemLp.of_bound hf.aestronglyMeasurable M
    filter_upwards with V
    simpa only [Real.norm_eq_abs] using hb V
  have hi : Integrable (fun V => f V*logCurvature β U V 0) μ :=
    hf2.integrable_mul (logCurvature_memLp β U)
  have hfi := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf2
  let c := ∫ V, logCurvature β U V 0 ∂μ
  have he (V : State) : f V*PeriodicEndpointSecondResponse.physicalSecond β U U V =
      2*(f V*logCurvature β U V 0-f V*c) := by
    rw [physical_second_centered]
    dsimp only [c,μ]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_sub hi (hfi.mul_const c),integral_mul_const]

/-- Actual second derivative on the verified bounded measurable physical core.
The covariance is under the original nonlinear middle law, not Gaussian noise. -/
theorem physical_second_covariance_derivative (β : ℝ) (U : State) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) :
    HasDerivAt (deriv (fun h => ∫ V, f V ∂PeriodicGroundBridge.law β
      (PeriodicEndpointScore.left h U) (PeriodicEndpointScore.right h U)))
      (2*((∫ V, f V*logCurvature β U V 0 ∂PeriodicGroundBridge.law β U U)-
        (∫ V, f V ∂PeriodicGroundBridge.law β U U)*
          ∫ V, logCurvature β U V 0 ∂PeriodicGroundBridge.law β U U)) 0 := by
  have hh := PeriodicEndpointSecondResponse.physical_second_derivative β U U f hf M hM hb
  rwa [physical_second_covariance β U f hf M hb] at hh

def sineSignal (U : State) : ℝ := PeriodicCenteredHolonomy.first U
def cosineSignal (U : State) : ℝ := halfTrace (PeriodicSpatialHolonomy.winding U
  (PeriodicTemporalCycleMoment.vertex (fun _ => 0) 0) 1)

theorem signals_gauge (a : Gauge) (U : State) :
    sineSignal (PeriodicSlabGauge.gaugeAction a U)=sineSignal U ∧
      cosineSignal (PeriodicSlabGauge.gaugeAction a U)=cosineSignal U := by
  constructor
  · unfold sineSignal PeriodicCenteredHolonomy.first
    rw [PeriodicSpatialHolonomy.trace_gauge]
  · unfold cosineSignal
    rw [PeriodicSpatialHolonomy.trace_gauge]

theorem orbit_sine (h : ℝ) : sineSignal (PeriodicTemporalCycleMoment.orbit h)=Real.sin (4*h) := by
  have he : PeriodicTemporalCycleMoment.orbit h=PeriodicSlabGauge.gaugeAction
      (fun _ => SU2JointPlaquetteCubic.axis 0 h)
        (PeriodicEndpointScore.right (-h) PeriodicEndpointFibreWitness.leftEndpoint) := by
    funext e
    simp only [PeriodicTemporalCycleMoment.orbit,PeriodicEndpointScore.left,
      PeriodicEndpointScore.right,PeriodicSlabGauge.gaugeAction,neg_neg]
    group
  rw [he,(signals_gauge _ _).1]
  exact PeriodicWindingEndpointResponse.winding_curve h

theorem orbit_cosine (h : ℝ) : cosineSignal (PeriodicTemporalCycleMoment.orbit h)=Real.cos (4*h) :=
  PeriodicTemporalCycleMoment.orbit_winding h (fun _ => 0)

theorem signal_derivatives (t : ℝ) :
    HasDerivAt (fun h => sineSignal (PeriodicEndpointScore.left h (PeriodicTemporalCycleMoment.orbit t)))
      (4*Real.cos (4*t)) 0 ∧
    HasDerivAt (fun h => cosineSignal (PeriodicEndpointScore.left h (PeriodicTemporalCycleMoment.orbit t)))
      (-4*Real.sin (4*t)) 0 := by
  have he (h : ℝ) : PeriodicEndpointScore.left h (PeriodicTemporalCycleMoment.orbit t)=
      PeriodicTemporalCycleMoment.orbit (h+t) := left_add h t PeriodicEndpointFibreWitness.leftEndpoint
  have hs : (fun h => sineSignal (PeriodicEndpointScore.left h (PeriodicTemporalCycleMoment.orbit t))) =
      (fun h => Real.sin (4*(h+t))) := funext (fun h => by rw [he,orbit_sine])
  have hc : (fun h => cosineSignal (PeriodicEndpointScore.left h (PeriodicTemporalCycleMoment.orbit t))) =
      (fun h => Real.cos (4*(h+t))) := funext (fun h => by rw [he,orbit_cosine])
  rw [hs,hc]
  constructor
  · convert ((((hasDerivAt_id (0 : ℝ)).add_const t).const_mul 4).sin) using 1 <;> norm_num <;> ring
  · convert ((((hasDerivAt_id (0 : ℝ)).add_const t).const_mul 4).cos) using 1 <;> norm_num <;> ring

def signalEnergy (t : ℝ) : ℝ :=
  (deriv (fun h => sineSignal (PeriodicEndpointScore.left h (PeriodicTemporalCycleMoment.orbit t))) 0)^2+
    (deriv (fun h => cosineSignal (PeriodicEndpointScore.left h (PeriodicTemporalCycleMoment.orbit t))) 0)^2

/-- Exact squared signal-derivative norm for two gauge-invariant boundary words.
This detects the coherent tangent at EVERY translated base point. -/
theorem signal_tangent_norm (t : ℝ) : signalEnergy t=16 := by
  unfold signalEnergy
  rw [(signal_derivatives t).1.deriv,(signal_derivatives t).2.deriv]
  nlinarith [Real.sin_sq_add_cos_sq (4*t)]

/-- Adding the genuine second channel does not give a positive coupling-uniform
budget for this fixed-amplitude physical boundary tangent near beta0. This does
not exclude rescaled channels, averaged frames or a high-beta spectral bound. -/
theorem no_uniform_two_channel_signal_budget (t : ℝ → ℝ) (c : ℝ) (hc : 0<c) :
    ¬ (∀ᶠ β : ℝ in 𝓝[≠] 0,
      c*signalEnergy (t β) ≤
      (∫ V, (PeriodicPhysicalBridgeScore.physicalScore β (PeriodicTemporalCycleMoment.orbit (t β))
        (PeriodicTemporalCycleMoment.orbit (t β)) V)^2 ∂PeriodicGroundBridge.law β
          (PeriodicTemporalCycleMoment.orbit (t β)) (PeriodicTemporalCycleMoment.orbit (t β)))+
      ∫ V, (PeriodicEndpointSecondResponse.physicalSecond β (PeriodicTemporalCycleMoment.orbit (t β))
        (PeriodicTemporalCycleMoment.orbit (t β)) V)^2 ∂PeriodicGroundBridge.law β
          (PeriodicTemporalCycleMoment.orbit (t β)) (PeriodicTemporalCycleMoment.orbit (t β))) := by
  intro hh
  apply no_uniform_positive_energy_floor (fun β => PeriodicTemporalCycleMoment.orbit (t β))
    (fun β => PeriodicTemporalCycleMoment.orbit (t β)) (16*c) (by positivity)
  filter_upwards [hh] with β hb
  rw [signal_tangent_norm,PeriodicPhysicalBridgeScore.diagonal_physical_energy_zero,zero_add] at hb
  nlinarith

end OperatorDerivativeRewrite.Foundation.PeriodicNativeSecondChannel
