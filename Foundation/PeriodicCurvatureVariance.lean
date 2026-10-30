import Foundation.PeriodicTransferVariation
/-! Actual local Wilson plaquette variance: collapse at large coupling, strict
positivity at each finite coupling. These are compatible statements and do
not imply a local spectral gap. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicCurvatureVariance
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab
open PeriodicSlabGround PeriodicSlabJoint PeriodicTemporalConcentration

def plaquette (p : SpatialFace) (U : State) : ℝ := halfTrace (spatialWord U p)

theorem plaquette_measurable (p : SpatialFace) : Measurable (plaquette p) :=
  halfTrace_measurable.comp (by unfold spatialWord; fun_prop)

theorem deviation_bound (p : SpatialFace) (q : Triple) :
    (plaquette p q.1.1-1)^2 ≤ 4*energy q := by
  have hd := Finset.single_le_sum (fun p (_ : p∈Finset.univ) =>
    FourCubePinnedCoercivity.defect_nonneg (spatialWord q.1.1 p)) (Finset.mem_univ p)
  change 1-plaquette p q.1.1 ≤ spatialAction q.1.1 at hd
  have hs : spatialAction q.1.1 ≤ 2*energy q := by
    unfold energy halfAction
    linarith [(spatial_action_bounds q.1.2).1,(temporal_action_bounds q.1.1 q.1.2 q.2).1]
  have ht := abs_le.mp (halfTrace_bound (spatialWord q.1.1 p))
  change -1 ≤ plaquette p q.1.1 ∧ plaquette p q.1.1 ≤ 1 at ht
  nlinarith

variable {beta : ℝ} (g : GroundData beta)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability
private instance joint_probability : IsProbabilityMeasure (tripleLaw g) := triple_probability g

theorem deviation_integral (p : SpatialFace) :
    (∫ U,(plaquette p U-1)^2 ∂g.stationary) ≤ 4*(∫ q,energy q ∂tripleLaw g) := by
  have mp := (PeriodicSlabL2.left_preserving g).comp (pair_preserving g)
  have hm : Measurable (fun U : State => (plaquette p U-1)^2) :=
    ((plaquette_measurable p).sub measurable_const).pow_const 2
  have he := integral_map (μ := tripleLaw g) (φ := (fun q : Triple => q.1.1))
    mp.measurable.aemeasurable hm.aestronglyMeasurable
  have mp0 : MeasurePreserving (fun q : Triple => q.1.1) (tripleLaw g) g.stationary := mp
  rw [mp0.map_eq] at he
  rw [he]
  have hi : Integrable (fun q : Triple => (plaquette p q.1.1-1)^2) (tripleLaw g) := by
    apply Integrable.of_bound (hm.comp mp.measurable).aestronglyMeasurable 4
    filter_upwards with q
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    change (plaquette p q.1.1-1)^2 ≤ 4
    have ht := abs_le.mp (halfTrace_bound (spatialWord q.1.1 p))
    change -1 ≤ plaquette p q.1.1 ∧ plaquette p q.1.1 ≤ 1 at ht
    nlinarith
  have h := integral_mono hi ((energy_integrable g).const_mul 4) (deviation_bound p)
  rwa [integral_const_mul] at h



theorem plaquette_memLp (p : SpatialFace) : MemLp (plaquette p) 2 g.stationary :=
  MemLp.of_bound (plaquette_measurable p).aestronglyMeasurable 1
    (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs,plaquette] using halfTrace_bound (spatialWord U p)))

theorem variance_bound (p : SpatialFace) :
    variance (plaquette p) g.stationary ≤ 4*(∫ q,energy q ∂tripleLaw g) := by
  have hf := plaquette_memLp g p
  have hd : MemLp (fun U => plaquette p U-1) 2 g.stationary := hf.sub (memLp_const 1)
  have hv := variance_sub_const hf.aestronglyMeasurable 1
  change variance (fun U => plaquette p U-1) g.stationary=variance (plaquette p) g.stationary at hv
  rw [← hv,variance_eq_sub hd]
  simp only [Pi.pow_apply]
  have h := deviation_integral g p
  nlinarith [sq_nonneg (∫ U,plaquette p U-1 ∂g.stationary)]


theorem eventual_variance_small (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ beta : ℝ in atTop,∀ g : GroundData beta,∀ p : SpatialFace,
      variance (plaquette p) g.stationary < eps := by
  filter_upwards [energy_small (eps/8) (by positivity)] with beta hb
  intro g p
  have h := variance_bound g p
  linarith [hb g]

theorem variance_tendsto_zero (p : SpatialFace) :
    Tendsto (fun beta : ℝ => variance (plaquette p) (ground beta).stationary) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun beta => ha.trans_le (variance_nonneg (plaquette p) (ground beta).stationary))
  · intro b hb
    filter_upwards [eventual_variance_small b hb] with beta hbeta
    exact hbeta (ground beta) p



private instance boundary_open : boundaryHaar.IsOpenPosMeasure := by unfold boundaryHaar; infer_instance

theorem stationary_ae_iff (P : State → Prop) :
    (∀ᵐ U ∂g.stationary,P U) ↔ ∀ᵐ U ∂boundaryHaar,P U := by
  change (∀ᵐ U ∂(ENNReal.ofReal (SignedDensityProbabilitySampling.mass boundaryHaar
    (fun U => g.function U^2)))⁻¹ • SignedAbsoluteIntegration.absoluteDensity boundaryHaar
      (fun U => g.function U^2),P U) ↔ _
  rw [Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)]
  unfold SignedAbsoluteIntegration.absoluteDensity
  simp only [abs_pow,sq_abs]
  rw [ae_withDensity_iff (g.measurable.pow_const 2).ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h] with U hU
    exact hU (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (g.function_pos U))))
  · intro h
    filter_upwards [h] with U hU
    exact fun _ => hU

theorem plaquette_continuous (p : SpatialFace) : Continuous (plaquette p) :=
  PeriodicLowActionBlock.trace_continuous.comp (by unfold spatialWord; fun_prop)

def singleTwist (p : SpatialFace) : State :=
  fun e => if e=(p.val.1,p.val.2.1) then SU2StapleExtremes.minusOne else 1

theorem plaquette_one (p : SpatialFace) : plaquette p (1 : State)=1 := by
  simp [plaquette,spatialWord,SU2OpenLinkGaugeObstruction.halfTrace_one]

theorem plaquette_singleTwist (p : SpatialFace) : plaquette p (singleTwist p)= -1 := by
  have hij := ne_of_lt p.property
  have hs : shift p.val.1 p.val.2.2 ≠ p.val.1 := by
    intro h
    have hv := congrArg (fun v : SpatialVertex => v p.val.2.2) h
    simp [shift] at hv
    exact (by decide : (1 : ZMod 4) ≠ 0) hv
  have he : spatialWord (singleTwist p) p=SU2StapleExtremes.minusOne := by
    simp [spatialWord,singleTwist,Ne.symm hij,hs]
  rw [plaquette,he,SU2StapleExtremes.minusOne,halfTrace_map]
  rfl

theorem variance_pos (p : SpatialFace) : 0 < variance (plaquette p) g.stationary := by
  have hn := variance_nonneg (plaquette p) g.stationary
  by_contra h
  have hz : variance (plaquette p) g.stationary=0 := le_antisymm (le_of_not_gt h) hn
  have hae := ae_eq_integral_of_variance_eq_zero (plaquette_memLp g p) hz
  have hh := (stationary_ae_iff g _).mp hae
  have heq := MeasureTheory.Measure.eq_of_ae_eq hh (plaquette_continuous p) continuous_const
  have h0 := congrFun heq (1 : State)
  have h1 := congrFun heq (singleTwist p)
  rw [plaquette_one] at h0
  rw [plaquette_singleTwist] at h1
  linarith
end OperatorDerivativeRewrite.Foundation.PeriodicCurvatureVariance
