import Foundation.PeriodicCurvatureTransfer
/-! Curvature-weighted actual plaquette transfer. All mixed moments use the
actual stationary triple law. The normalized Dirichlet identity retains its
actual variance denominator; no asymptotic physical mass gap is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Quaternion
namespace OperatorDerivativeRewrite.Foundation.PeriodicCurvatureWeighted
open QuaternionSU2Representation PeriodicLoopVariation

private theorem quaternion_weighted (a b : QuaternionAngularHaar.Group) :
    ((a : ℍ).re-(b : ℍ).re)^2 ≤
      (2-(a : ℍ).re-(b : ℍ).re)*‖(a : ℍ)-(b : ℍ)‖^2 := by
  have hn (c : QuaternionAngularHaar.Group) : Quaternion.normSq (c : ℍ)=1 := by
    rw [Quaternion.normSq_eq_norm_mul_self,CStarRing.norm_coe_unitary,one_mul]
  let x : ℍ := (a : ℍ)-(b : ℍ)
  let y : ℍ := (a : ℍ)+(b : ℍ)-(⟨2,0,0,0⟩ : ℍ)
  have hxy : inner ℝ x y= -2*((a : ℍ).re-(b : ℍ).re) := by
    have ha := hn a
    have hb := hn b
    dsimp [x,y]
    norm_num [Quaternion.inner_def,Quaternion.re_mul,Quaternion.normSq_def'] at ha hb ⊢
    nlinarith
  have hs : ‖x‖^2+‖y‖^2=4*(2-(a : ℍ).re-(b : ℍ).re) := by
    have ha := hn a
    have hb := hn b
    dsimp [x,y]
    simp only [pow_two,← Quaternion.normSq_eq_norm_mul_self]
    norm_num [Quaternion.normSq_def'] at ha hb ⊢
    nlinarith
  have hc := real_inner_mul_inner_self_le x y
  rw [hxy,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hc
  have hm := congrArg (fun t : ℝ => ‖x‖^2*t) hs
  change ((a : ℍ).re-(b : ℍ).re)^2 ≤ (2-(a : ℍ).re-(b : ℍ).re)*‖x‖^2
  nlinarith [sq_nonneg (‖x‖^2)]

theorem weighted_trace_distance (A B : SU2) :
    (halfTrace A-halfTrace B)^2 ≤
      (FourCubePinnedCoercivity.defect A+FourCubePinnedCoercivity.defect B)*distance A B^2 := by
  obtain ⟨a,rfl⟩ := hom_surjective A
  obtain ⟨b,rfl⟩ := hom_surjective B
  have hl (c : QuaternionAngularHaar.Group) : lift (hom c)=(c : ℍ) := by
    change ((equiv.symm (equiv c) : QuaternionAngularHaar.Group) : ℍ)=_
    rw [equiv.symm_apply_apply]
  simp only [FourCubePinnedCoercivity.defect,halfTrace_map,QuaternionAngularHaar.realCoordinate,distance,hl]
  have h := quaternion_weighted a b
  convert h using 1 <;> ring




open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabJoint
open PeriodicSlabL2 PeriodicTemporalConcentration PeriodicCurvatureVariance PeriodicCurvatureTransfer

def pairedDefect (p : SpatialFace) (q : Triple) : ℝ :=
  (1-plaquette p q.1.1)+(1-plaquette p q.1.2)

def mixedEnergy (p : SpatialFace) (q : Triple) : ℝ := temporalEnergy q*pairedDefect p q

def increment (p : SpatialFace) (q : State × State) : ℝ := (plaquette p q.2-plaquette p q.1)^2

theorem paired_bounds (p : SpatialFace) (q : Triple) :
    0 ≤ pairedDefect p q ∧ pairedDefect p q ≤ 4 := by
  have hU := abs_le.mp (halfTrace_bound (spatialWord q.1.1 p))
  have hV := abs_le.mp (halfTrace_bound (spatialWord q.1.2 p))
  change -1 ≤ plaquette p q.1.1 ∧ plaquette p q.1.1 ≤ 1 at hU
  change -1 ≤ plaquette p q.1.2 ∧ plaquette p q.1.2 ≤ 1 at hV
  unfold pairedDefect
  constructor <;> linarith

theorem weighted_plaquette_change (U V : State) (a : Gauge) (p : SpatialFace) :
    (plaquette p U-plaquette p V)^2 ≤ 32*mixedEnergy p ((U,V),a) := by
  have ht := weighted_trace_distance (spatialWord U p) (spatialWord (PeriodicSlabGauge.gaugeAction a V) p)
  change (plaquette p U-plaquette p (PeriodicSlabGauge.gaugeAction a V))^2 ≤
    ((1-plaquette p U)+(1-plaquette p (PeriodicSlabGauge.gaugeAction a V)))*_ at ht
  rw [plaquette_gauge a V p] at ht
  have hm := mul_le_mul_of_nonneg_left (plaquette_distance_sq U V a p) (paired_bounds p ((U,V),a)).1
  change pairedDefect p ((U,V),a)*distance (spatialWord U p)
    (spatialWord (PeriodicSlabGauge.gaugeAction a V) p)^2 ≤ _ at hm
  change _ ≤ pairedDefect p ((U,V),a)*distance (spatialWord U p)
    (spatialWord (PeriodicSlabGauge.gaugeAction a V) p)^2 at ht
  exact ht.trans (hm.trans_eq (by unfold mixedEnergy temporalEnergy; ring))

theorem mixed_bounds (p : SpatialFace) (q : Triple) : 0 ≤ mixedEnergy p q ∧ mixedEnergy p q ≤ 1536 := by
  unfold mixedEnergy
  constructor
  · exact mul_nonneg (temporal_bounds q).1 (paired_bounds p q).1
  · nlinarith [(temporal_bounds q).1,(temporal_bounds q).2,(paired_bounds p q).1,(paired_bounds p q).2]

theorem mixed_measurable (p : SpatialFace) : Measurable (mixedEnergy p) := by
  unfold mixedEnergy pairedDefect
  exact temporal_measurable.mul
    ((measurable_const.sub ((plaquette_measurable p).comp (measurable_fst.comp measurable_fst))).add
      (measurable_const.sub ((plaquette_measurable p).comp (measurable_snd.comp measurable_fst))))



variable {beta : ℝ} (g : GroundData beta)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability
private instance joint_probability : IsProbabilityMeasure (tripleLaw g) := triple_probability g

theorem mixed_integrable (p : SpatialFace) : Integrable (mixedEnergy p) (tripleLaw g) :=
  Integrable.of_bound (mixed_measurable p).aestronglyMeasurable 1536
    (ae_of_all _ (fun q => by rw [Real.norm_eq_abs,abs_of_nonneg (mixed_bounds p q).1]; exact (mixed_bounds p q).2))

theorem increment_measurable (p : SpatialFace) : Measurable (increment p) :=
  (((plaquette_measurable p).comp measurable_snd).sub ((plaquette_measurable p).comp measurable_fst)).pow_const 2

theorem increment_integrable (p : SpatialFace) : Integrable (increment p) (edgeLaw g) := by
  haveI : IsProbabilityMeasure (edgeLaw g) := by
    unfold edgeLaw
    letI := g.transition_markov
    infer_instance
  apply Integrable.of_bound (increment_measurable p).aestronglyMeasurable 4
  filter_upwards with q
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hU := abs_le.mp (halfTrace_bound (spatialWord q.1 p))
  have hV := abs_le.mp (halfTrace_bound (spatialWord q.2 p))
  change -1 ≤ plaquette p q.1 ∧ plaquette p q.1 ≤ 1 at hU
  change -1 ≤ plaquette p q.2 ∧ plaquette p q.2 ≤ 1 at hV
  unfold increment
  nlinarith

theorem increment_projection (p : SpatialFace) :
    (∫ q,increment p q ∂edgeLaw g)=(∫ q : Triple,increment p q.1 ∂tripleLaw g) := by
  have h := integral_map (μ := tripleLaw g) (φ := (Prod.fst : Triple → State × State))
    measurable_fst.aemeasurable (increment_measurable p).aestronglyMeasurable
  rwa [(pair_preserving g).map_eq] at h

theorem increment_moment_bound (p : SpatialFace) :
    (∫ q,increment p q ∂edgeLaw g) ≤ 32*(∫ q,mixedEnergy p q ∂tripleLaw g) := by
  rw [increment_projection]
  have hi : Integrable (fun q : Triple => increment p q.1) (tripleLaw g) := by
    change Integrable ((increment p) ∘ (Prod.fst : Triple → State × State)) (tripleLaw g)
    exact MeasurePreserving.integrable_comp_of_integrable (g := increment p)
      (pair_preserving g) (increment_integrable g p)
  have hp (q : Triple) : increment p q.1 ≤ 32*mixedEnergy p q := by
    have h := weighted_plaquette_change q.1.1 q.1.2 q.2 p
    unfold increment
    nlinarith
  have h := integral_mono hi ((mixed_integrable g p).const_mul 32) hp
  rwa [integral_const_mul] at h

theorem vector_edge_square (p : SpatialFace) :
    ‖rightEmbedding g (vector g p)-leftEmbedding g (vector g p)‖^2=
      ∫ q,increment p q ∂edgeLaw g := by
  calc
    _ = ∫ q,(centered g p q.2-centered g p q.1)^2 ∂edgeLaw g :=
      PeriodicTransferVariation.edge_norm_square g (centered g p) (centered_memLp g p)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with q
      unfold centered increment
      ring

theorem vector_mixed_bound (p : SpatialFace) :
    ‖operator g (vector g p)-vector g p‖^2 ≤ 32*(∫ q,mixedEnergy p q ∂tripleLaw g) := by
  have hr := PeriodicTransferVariation.operator_residual g (vector g p)
  have hs := mul_self_le_mul_self (norm_nonneg _) hr
  have he := vector_edge_square g p
  have hm := increment_moment_bound g p
  nlinarith

theorem normalized_residual_identity (p : SpatialFace) :
    ‖operator g (normalized g p)-normalized g p‖^2=
      ‖operator g (vector g p)-vector g p‖^2/variance (plaquette p) g.stationary := by
  have he : operator g (normalized g p)-normalized g p=
      ‖vector g p‖⁻¹ • (operator g (vector g p)-vector g p) := by
    rw [normalized,map_smul,smul_sub]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (vector_norm_pos g p))]
  apply (eq_div_iff (ne_of_gt (variance_pos g p))).mpr
  have hinv : ‖vector g p‖⁻¹*‖vector g p‖=1 := inv_mul_cancel₀ (ne_of_gt (vector_norm_pos g p))
  calc
    _ = (‖vector g p‖⁻¹*‖vector g p‖)^2*‖operator g (vector g p)-vector g p‖^2 := by
      rw [← vector_norm_square]
      ring
    _ = _ := by rw [hinv]; ring

theorem normalized_mixed_bound (p : SpatialFace) :
    ‖operator g (normalized g p)-normalized g p‖^2 ≤
      32*(∫ q,mixedEnergy p q ∂tripleLaw g)/variance (plaquette p) g.stationary := by
  rw [normalized_residual_identity]
  exact div_le_div_of_nonneg_right (vector_mixed_bound g p) (variance_pos g p).le



theorem vector_dirichlet_identity (p : SpatialFace) :
    variance (plaquette p) g.stationary-inner ℝ (operator g (vector g p)) (vector g p)=
      (∫ q,increment p q ∂edgeLaw g)/2 := by
  have hn := norm_sub_sq_real (rightEmbedding g (vector g p)) (leftEmbedding g (vector g p))
  rw [(rightEmbedding g).norm_map,(leftEmbedding g).norm_map] at hn
  have hp := HilbertRepresentation.predictableAdjoint_pairing (leftEmbedding g)
    (rightEmbedding g (vector g p)) (vector g p)
  change inner ℝ (operator g (vector g p)) (vector g p)=
    inner ℝ (rightEmbedding g (vector g p)) (leftEmbedding g (vector g p)) at hp
  rw [← hp,vector_edge_square,vector_norm_square] at hn
  linarith

theorem normalized_dirichlet_identity (p : SpatialFace) :
    1-inner ℝ (operator g (normalized g p)) (normalized g p)=
      (∫ q,increment p q ∂edgeLaw g)/(2*variance (plaquette p) g.stationary) := by
  have hi : inner ℝ (operator g (normalized g p)) (normalized g p)=
      ‖vector g p‖⁻¹^2*inner ℝ (operator g (vector g p)) (vector g p) := by
    rw [normalized,map_smul,real_inner_smul_left,real_inner_smul_right]
    ring
  rw [hi]
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (variance_pos g p)))).mpr
  have hinv : ‖vector g p‖⁻¹*‖vector g p‖=1 := inv_mul_cancel₀ (ne_of_gt (vector_norm_pos g p))
  have hinv2 : ‖vector g p‖⁻¹^2*variance (plaquette p) g.stationary=1 := by
    rw [← vector_norm_square]
    calc
      _ = (‖vector g p‖⁻¹*‖vector g p‖)^2 := by ring
      _ = 1 := by rw [hinv]; norm_num
  calc
    _ = 2*(variance (plaquette p) g.stationary-
        (‖vector g p‖⁻¹^2*variance (plaquette p) g.stationary)*
          inner ℝ (operator g (vector g p)) (vector g p)) := by ring
    _ = 2*(variance (plaquette p) g.stationary-inner ℝ (operator g (vector g p)) (vector g p)) := by
      rw [hinv2,one_mul]
    _ = _ := by linarith [vector_dirichlet_identity g p]

theorem normalized_dirichlet_bound (p : SpatialFace) :
    1-inner ℝ (operator g (normalized g p)) (normalized g p) ≤
      16*(∫ q,mixedEnergy p q ∂tripleLaw g)/variance (plaquette p) g.stationary := by
  rw [normalized_dirichlet_identity]
  calc
    _ ≤ (32*(∫ q,mixedEnergy p q ∂tripleLaw g))/(2*variance (plaquette p) g.stationary) :=
      div_le_div_of_nonneg_right (increment_moment_bound g p) (mul_pos (by norm_num : (0 : ℝ) < 2) (variance_pos g p)).le
    _ = _ := by field_simp; ring

theorem paired_le_spatial (p : SpatialFace) (q : Triple) :
    pairedDefect p q ≤ spatialAction q.1.1+spatialAction q.1.2 := by
  have hU := Finset.single_le_sum (fun p (_ : p∈Finset.univ) =>
    FourCubePinnedCoercivity.defect_nonneg (spatialWord q.1.1 p)) (Finset.mem_univ p)
  have hV := Finset.single_le_sum (fun p (_ : p∈Finset.univ) =>
    FourCubePinnedCoercivity.defect_nonneg (spatialWord q.1.2 p)) (Finset.mem_univ p)
  change 1-plaquette p q.1.1 ≤ spatialAction q.1.1 at hU
  change 1-plaquette p q.1.2 ≤ spatialAction q.1.2 at hV
  unfold pairedDefect
  linarith

theorem mixed_le_square (p : SpatialFace) (q : Triple) : mixedEnergy p q ≤ energy q^2/2 := by
  have ht : 0 ≤ temporalAction q.1.1 q.1.2 q.2 := (temporal_bounds q).1
  have hm := mul_le_mul_of_nonneg_left (paired_le_spatial p q) ht
  have hs := sq_nonneg (temporalAction q.1.1 q.1.2 q.2-
    (spatialAction q.1.1+spatialAction q.1.2)/2)
  unfold mixedEnergy temporalEnergy energy halfAction
  nlinarith

theorem energy_square_integrable : Integrable (fun q => energy q^2) (tripleLaw g) := by
  apply Integrable.of_bound (energy_measurable.pow_const 2).aestronglyMeasurable (768^2)
  filter_upwards with q
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  nlinarith [(energy_bounds q).1,(energy_bounds q).2]

theorem mixed_moment_le_square (p : SpatialFace) :
    (∫ q,mixedEnergy p q ∂tripleLaw g) ≤ (∫ q,energy q^2 ∂tripleLaw g)/2 := by
  have h := integral_mono (mixed_integrable g p) ((energy_square_integrable g).div_const 2)
    (mixed_le_square p)
  rwa [integral_div] at h

theorem energy_square_le_mean :
    (∫ q,energy q^2 ∂tripleLaw g) ≤ 768*(∫ q,energy q ∂tripleLaw g) := by
  have h := integral_mono (energy_square_integrable g) ((energy_integrable g).const_mul 768)
    (fun q => by nlinarith [(energy_bounds q).1,(energy_bounds q).2])
  rwa [integral_const_mul] at h

theorem normalized_second_moment_bound (p : SpatialFace) :
    ‖operator g (normalized g p)-normalized g p‖^2 ≤
      16*(∫ q,energy q^2 ∂tripleLaw g)/variance (plaquette p) g.stationary := by
  apply (normalized_mixed_bound g p).trans
  apply div_le_div_of_nonneg_right _ (variance_pos g p).le
  linarith [mixed_moment_le_square g p]

theorem eventual_mixed_small (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ beta : ℝ in atTop,∀ g : GroundData beta,∀ p : SpatialFace,
      (∫ q,mixedEnergy p q ∂tripleLaw g) < eps := by
  filter_upwards [energy_small (eps/3072) (by positivity)] with beta hb
  intro g p
  have h1 := mixed_moment_le_square g p
  have h2 := energy_square_le_mean g
  linarith [hb g]
end OperatorDerivativeRewrite.Foundation.PeriodicCurvatureWeighted
