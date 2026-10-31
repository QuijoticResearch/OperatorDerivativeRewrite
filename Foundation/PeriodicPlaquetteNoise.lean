import Foundation.PeriodicPlaquetteVarianceLower
import Foundation.PeriodicCurvatureWeighted
import Foundation.PeriodicWindingRate

/-! Actual one-step plaquette noise and native per-probe transfer estimates.
The true two-sided bridge gives a uniform transition variance floor. Exact
bounded-core agreement with the native L2 operator transports it to norm loss,
residual and Rayleigh-form lower bounds for the normalized local plaquette.
The existing actual energy-tail estimate also gives a second-moment bound and
an explicit logarithmic residual floor. These are fixed-cell single-probe
estimates, not a full spectral gap, an iterated contraction bound or a physical
continuum or infinite-volume mass-gap result. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
open PeriodicCurvatureVariance PeriodicPlaquetteVarianceLower
namespace OperatorDerivativeRewrite.Foundation.PeriodicPlaquetteNoise
attribute [local irreducible] boundaryHaar gaugeHaar PeriodicWilsonSlab.kernel

theorem transition_centered_lower (β : ℝ) (hβ : 0 ≤ β) (g : GroundData β)
    (p : SpatialFace) (U : State) (c : ℝ) :
    6/(49*(1+6*β)^2) ≤ ∫ V,(plaquette p V-c)^2 ∂g.transition U := by
  let := g.transition_markov
  let f : State → ℝ := fun V => (plaquette p V-c)^2
  have hf : Measurable f := ((plaquette_measurable p).sub measurable_const).pow_const 2
  have hb (V : State) : |f V| ≤ (1+|c|)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := (abs_sub (plaquette p V) c).trans
      (add_le_add (halfTrace_bound (spatialWord V p)) (le_refl |c|))
    nlinarith [abs_nonneg (plaquette p V-c),abs_nonneg c,sq_abs (plaquette p V-c)]
  let M : State → ℝ := fun W => ∫ V,f V ∂PeriodicGroundBridge.law β U W
  have hm0 : Measurable (fun q : State × State => ∫ V,f V ∂PeriodicGroundBridge.bridgeKernel β q) :=
    hf.stronglyMeasurable.integral_kernel.measurable
  have hm : Measurable M := by
    simpa only [PeriodicGroundBridge.bridgeKernel_apply,Function.comp_def,M,id_eq] using
      hm0.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable M ((g.transition ∘ₖ g.transition) U) := by
    apply Integrable.of_bound hm.aestronglyMeasurable ((1+|c|)^2)
    filter_upwards with W
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := PeriodicGroundBridge.law β U W) (f := f)
      (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using hb V))
  have h := integral_mono (integrable_const (6/(49*(1+6*β)^2))) hi
    (fun W => centered_bridge p β hβ U W c)
  simp only [integral_const,probReal_univ,one_smul] at h
  dsimp only [M] at h
  rw [PeriodicGroundBridge.bridge_average g U f hf ((1+|c|)^2) hb] at h
  exact h

theorem transition_variance_lower (β : ℝ) (hβ : 0 ≤ β) (g : GroundData β)
    (p : SpatialFace) (U : State) :
    6/(49*(1+6*β)^2) ≤ variance (plaquette p) (g.transition U) := by
  rw [variance_eq_integral (plaquette_measurable p).aemeasurable]
  exact transition_centered_lower β hβ g p U _


open PeriodicSlabL2 PeriodicCurvatureTransfer PeriodicTransferVariation
private theorem centered_bound (β : ℝ) (g : GroundData β) (p : SpatialFace) (U : State) :
    |centered g p U| ≤ 2 := by
  let := g.stationary_probability
  have hm : |∫ V,plaquette p V ∂g.stationary| ≤ 1 := by
    have h := norm_integral_le_of_norm_le_const (μ := g.stationary) (f := plaquette p)
      (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs,plaquette] using halfTrace_bound (spatialWord V p)))
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using h
  have hp : |plaquette p U| ≤ 1 := halfTrace_bound (spatialWord U p)
  exact (abs_sub (plaquette p U) _).trans (by linarith)

theorem vector_norm_loss (β : ℝ) (hβ : 0 ≤ β) (g : GroundData β) (p : SpatialFace) :
    ‖operator g (vector g p)‖^2+6/(49*(1+6*β)^2) ≤ ‖vector g p‖^2 := by
  let := g.stationary_probability
  let := g.transition_markov
  let f : State → ℝ := centered g p
  have hm : Measurable f := (plaquette_measurable p).sub measurable_const
  have hb (U : State) : |f U| ≤ 2 := centered_bound β g p U
  have hsq (U : State) : |f U^2| ≤ 4 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := hb U
    nlinarith [sq_abs (f U),abs_nonneg (f U)]
  have hp := transfer_memLp g f hm 2 hb
  have hP2 : Integrable (fun U => transfer g f U^2) g.stationary := hp.integrable_sq
  have hF2 : Integrable (fun U => ∫ V,f V^2 ∂g.transition U) g.stationary := by
    apply Integrable.of_bound ((hm.pow_const 2).stronglyMeasurable.integral_kernel.measurable).aestronglyMeasurable 4
    filter_upwards with U
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := g.transition U) (f := fun V => f V^2)
      (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using hsq V))
  have lower (U : State) : 6/(49*(1+6*β)^2) ≤
      (∫ V,f V^2 ∂g.transition U)-(transfer g f U)^2 := by
    have h := transition_variance_lower β hβ g p U
    have hs := variance_sub_const (μ := g.transition U) (plaquette_measurable p).aestronglyMeasurable
      (∫ V,plaquette p V ∂g.stationary)
    have hl : MemLp f 2 (g.transition U) := MemLp.of_bound hm.aestronglyMeasurable 2
      (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using hb V))
    have hv : variance f (g.transition U) = variance (plaquette p) (g.transition U) := hs
    rw [← hv,variance_eq_sub hl] at h
    simpa only [Pi.pow_apply,transfer] using h
  have h := integral_mono (integrable_const (6/(49*(1+6*β)^2))) (hF2.sub hP2) lower
  simp only [integral_const,probReal_univ,one_smul,Pi.sub_apply] at h
  rw [integral_sub hF2 hP2,g.transition_stationary (fun V => f V^2) (hm.pow_const 2) 4 hsq] at h
  have hn : ‖operator g (vector g p)‖^2 = ∫ U,transfer g f U^2 ∂g.stationary := by
    rw [vector,operator_toLp g f (centered_memLp g p) hm 2 hb,state_norm_square]
  have hf := state_norm_square g f (centered_memLp g p)
  change ‖vector g p‖^2=∫ U,f U^2 ∂g.stationary at hf
  rw [← hn,← hf] at h
  linarith


theorem normalized_norm_loss (β : ℝ) (hβ : 0 ≤ β) (g : GroundData β) (p : SpatialFace) :
    ‖operator g (normalized g p)‖^2+
      (6/(49*(1+6*β)^2))/variance (plaquette p) g.stationary ≤ 1 := by
  have hl := vector_norm_loss β hβ g p
  have he : ‖vector g p‖^2*‖operator g (normalized g p)‖^2=‖operator g (vector g p)‖^2 := by
    rw [normalized,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (vector_norm_pos g p))]
    field_simp [(vector_norm_pos g p).ne']
  have hc : ((6/(49*(1+6*β)^2))/variance (plaquette p) g.stationary)*‖vector g p‖^2=
      6/(49*(1+6*β)^2) := by
    rw [vector_norm_square]
    exact div_mul_cancel₀ _ (variance_pos g p).ne'
  rw [← vector_norm_square] at hc
  apply (mul_le_mul_iff_right₀ (variance_pos g p)).mp
  rw [← vector_norm_square]
  nlinarith [hl,he,hc]

theorem normalized_residual_lower (β : ℝ) (hβ : 0 ≤ β) (g : GroundData β) (p : SpatialFace) :
    (6/(49*(1+6*β)^2))/(2*variance (plaquette p) g.stationary) ≤
      ‖operator g (normalized g p)-normalized g p‖ := by
  have hl := normalized_norm_loss β hβ g p
  have ht := norm_sub_norm_le (normalized g p) (operator g (normalized g p))
  rw [normalized_norm,norm_sub_rev] at ht
  have he : (6/(49*(1+6*β)^2))/(2*variance (plaquette p) g.stationary)=
      ((6/(49*(1+6*β)^2))/variance (plaquette p) g.stationary)/2 := by ring
  rw [he]
  nlinarith [sq_nonneg (‖operator g (normalized g p)‖-1)]


open PeriodicSlabJoint PeriodicTemporalConcentration PeriodicCurvatureWeighted
attribute [local irreducible] PeriodicSlabJoint.reference tripleLaw GroundData.stationary
private theorem deviation_square_point (p : SpatialFace) (q : Triple) :
    (plaquette p q.1.1-1)^2 ≤ 4*energy q^2 := by
  have hd := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    FourCubePinnedCoercivity.defect_nonneg (spatialWord q.1.1 j)) (Finset.mem_univ p)
  change 1-plaquette p q.1.1 ≤ spatialAction q.1.1 at hd
  have hs : spatialAction q.1.1 ≤ 2*energy q := by
    unfold energy halfAction
    linarith [(spatial_action_bounds q.1.2).1,(temporal_action_bounds q.1.1 q.1.2 q.2).1]
  have hn : 0 ≤ 1-plaquette p q.1.1 := sub_nonneg.mpr (abs_le.mp (halfTrace_bound (spatialWord q.1.1 p))).2
  have h := pow_le_pow_left₀ hn (hd.trans hs) 2
  nlinarith [h]

theorem variance_bound_square (β : ℝ) (g : GroundData β) (p : SpatialFace) :
    variance (plaquette p) g.stationary ≤ 4*(∫ q,energy q^2 ∂tripleLaw g) := by
  let := g.stationary_probability
  have hv := variance_le_expectation_sq (μ := g.stationary)
    (X := fun U => plaquette p U-1) ((plaquette_measurable p).sub measurable_const).aestronglyMeasurable
  rw [variance_sub_const (plaquette_measurable p).aestronglyMeasurable 1] at hv
  simp only [Pi.pow_apply] at hv
  have mp := (PeriodicSlabL2.left_preserving g).comp (pair_preserving g)
  have hm : Measurable (fun U => (plaquette p U-1)^2) :=
    ((plaquette_measurable p).sub measurable_const).pow_const 2
  have he := integral_map (μ := tripleLaw g) (φ := fun q : Triple => q.1.1)
    mp.measurable.aemeasurable hm.aestronglyMeasurable
  have mp0 : MeasurePreserving (fun q : Triple => q.1.1) (tripleLaw g) g.stationary := mp
  rw [mp0.map_eq] at he
  have h := integral_mono_of_nonneg (μ := tripleLaw g)
    (ae_of_all _ (fun q : Triple => sq_nonneg (plaquette p q.1.1-1)))
    ((energy_square_integrable g).const_mul 4) (ae_of_all _ (deviation_square_point p))
  rw [integral_const_mul] at h
  rw [← he] at h
  exact hv.trans h

theorem energy_square_from_tail (β : ℝ) (g : GroundData β) (eps : ℝ) :
    (∫ q,energy q^2 ∂tripleLaw g) ≤ eps^2+768^2*(tripleLaw g).real {q | eps ≤ energy q} := by
  let S : Set Triple := {q | eps ≤ energy q}
  have hS : MeasurableSet S := measurableSet_le measurable_const energy_measurable
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) (tripleLaw g) :=
    (integrable_const 1).indicator hS
  have hp (q : Triple) : energy q^2 ≤ eps^2+768^2*S.indicator (fun _ => (1:ℝ)) q := by
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq,mul_one]
      have h := pow_le_pow_left₀ (energy_bounds q).1 (energy_bounds q).2 2
      nlinarith [h,sq_nonneg eps]
    · rw [Set.indicator_of_notMem hq,mul_zero,add_zero]
      have h : energy q ≤ eps := le_of_lt (lt_of_not_ge hq)
      exact pow_le_pow_left₀ (energy_bounds q).1 h 2
  have h := integral_mono (energy_square_integrable g)
    ((integrable_const (eps^2)).add (hi.const_mul (768^2))) hp
  simp only [Pi.add_apply] at h
  have hid : (∫ q,S.indicator (fun _ => (1:ℝ)) q ∂tripleLaw g)=(tripleLaw g).real S :=
    integral_indicator_one hS
  rw [integral_add (integrable_const (eps^2)) (hi.const_mul (768^2)),integral_const_mul,hid] at h
  simpa only [integral_const,probReal_univ,one_smul,S] using h


def squareThreshold (β : ℝ) : ℝ := PeriodicEnergyRate.threshold β+Real.log (768*β)/β

theorem squareThreshold_exp (β : ℝ) (hb : 1 ≤ β) :
    Real.exp (-β*squareThreshold β)=(PeriodicPolynomialGround.lowerConstant/(768^2))/β^386 := by
  have hp : 0 < β := by linarith
  have hex : -β*squareThreshold β = -β*PeriodicEnergyRate.threshold β-Real.log (768*β) := by
    unfold squareThreshold
    field_simp [hp.ne']
    ring
  rw [hex,Real.exp_sub,PeriodicEnergyRate.threshold_exp β hb,
    Real.exp_log (by positivity : 0 < 768*β)]
  field_simp [hp.ne']

theorem energy_square_log_bound (β : ℝ) (hb : 1 ≤ β) (g : GroundData β) :
    (∫ q,energy q^2 ∂tripleLaw g) ≤ squareThreshold β^2+1/β^2 := by
  have hp : 0 < β := by linarith
  have ht := PeriodicPolynomialGround.energy_tail_polynomial g hb (squareThreshold β)
  rw [squareThreshold_exp β hb] at ht
  have ht' : (768:ℝ)^2*(tripleLaw g).real {q | squareThreshold β ≤ energy q} ≤ 1/β^2 := by
    have h := mul_le_mul_of_nonneg_left ht (sq_nonneg (768:ℝ))
    convert h using 1
    field_simp [hp.ne',PeriodicPolynomialGround.lowerConstant_pos.ne']
  exact (energy_square_from_tail β g (squareThreshold β)).trans (add_le_add (le_refl _) ht')

theorem variance_log_bound (β : ℝ) (hb : 1 ≤ β) (g : GroundData β) (p : SpatialFace) :
    variance (plaquette p) g.stationary ≤ 4*(squareThreshold β^2+1/β^2) :=
  (variance_bound_square β g p).trans
    (mul_le_mul_of_nonneg_left (energy_square_log_bound β hb g) (by norm_num : (0:ℝ) ≤ 4))

theorem logarithmic_residual_lower (β : ℝ) (hb : 1 ≤ β) (g : GroundData β) (p : SpatialFace) :
    (6/(49*(1+6*β)^2))/(8*(squareThreshold β^2+1/β^2)) ≤
      ‖operator g (normalized g p)-normalized g p‖ := by
  have hβ : 0 ≤ β := by linarith
  have hv := variance_log_bound β hb g p
  have hden : 2*variance (plaquette p) g.stationary ≤ 8*(squareThreshold β^2+1/β^2) := by linarith
  have hc : 0 ≤ 6/(49*(1+6*β)^2) := by positivity
  have h := div_le_div_of_nonneg_left hc (mul_pos (by norm_num : (0:ℝ) < 2) (variance_pos g p)) hden
  exact h.trans (normalized_residual_lower β hβ g p)

theorem normalized_dirichlet_lower (β : ℝ) (hβ : 0 ≤ β) (g : GroundData β) (p : SpatialFace) :
    (6/(49*(1+6*β)^2))/(2*variance (plaquette p) g.stationary) ≤
      SelfAdjointContractionIteration.dissipation (operator g) (normalized g p) := by
  have hl := normalized_norm_loss β hβ g p
  have hc := real_inner_le_norm (operator g (normalized g p)) (normalized g p)
  rw [normalized_norm,mul_one] at hc
  unfold SelfAdjointContractionIteration.dissipation
  rw [real_inner_self_eq_norm_sq,normalized_norm]
  have he : (6/(49*(1+6*β)^2))/(2*variance (plaquette p) g.stationary)=
      ((6/(49*(1+6*β)^2))/variance (plaquette p) g.stationary)/2 := by ring
  rw [he]
  nlinarith [sq_nonneg (‖operator g (normalized g p)‖-1)]

end OperatorDerivativeRewrite.Foundation.PeriodicPlaquetteNoise
