import Foundation.PeriodicCurvatureVariance
/-! Actual gauge-invariant local plaquette transfer and finite-coupling normalization.
The proved residual bound retains its variance denominator; no asymptotic
contraction or local mass gap is inferred from vanishing unnormalized energy. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace OperatorDerivativeRewrite.Foundation.PeriodicCurvatureTransfer
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicSlabGround
open PeriodicSlabJoint PeriodicSlabL2 PeriodicTemporalConcentration PeriodicLoopVariation
open PeriodicCurvatureVariance

private theorem distance_inv (A B : SU2) : distance A⁻¹ B⁻¹=distance A B := by
  obtain ⟨a,rfl⟩ := hom_surjective A
  obtain ⟨b,rfl⟩ := hom_surjective B
  have hl (c : QuaternionAngularHaar.Group) : lift (hom c)=(c : ℍ) := by
    change ((equiv.symm (equiv c) : QuaternionAngularHaar.Group) : ℍ)=_
    rw [equiv.symm_apply_apply]
  unfold distance
  rw [← hom.map_inv,← hom.map_inv,hl,hl,hl,hl]
  change ‖star (a : ℍ)-star (b : ℍ)‖=‖(a : ℍ)-(b : ℍ)‖
  rw [← star_sub,Quaternion.norm_star]

private theorem four_distance (a b c d A B C D : SU2) (r : ℝ)
    (ha : distance a A ≤ r) (hb : distance b B ≤ r)
    (hc : distance c C ≤ r) (hd : distance d D ≤ r) :
    distance (a*b*c*d) (A*B*C*D) ≤ 4*r := by
  linarith [distance_mul a b A B,distance_mul (a*b) c (A*B) C,
    distance_mul (a*b*c) d (A*B*C) D]

theorem plaquette_gauge (a : Gauge) (U : State) (p : SpatialFace) :
    plaquette p (PeriodicSlabGauge.gaugeAction a U)=plaquette p U := by
  rw [plaquette,PeriodicSlabGauge.spatial_word_covariant,halfTrace_conjugate]
  rfl

theorem plaquette_change (U V : State) (a : Gauge) (p : SpatialFace) :
    (plaquette p U-plaquette p V)^2 ≤ 32*PeriodicWilsonSlab.temporalAction U V a := by
  let W := PeriodicSlabGauge.gaugeAction a V
  have he (e : SpatialEdge) : distance (U e) (W e) ≤
      Real.sqrt (2*PeriodicWilsonSlab.temporalAction U V a) := edge_distance U V a e
  have hd : distance (spatialWord U p) (spatialWord W p) ≤
      4*Real.sqrt (2*PeriodicWilsonSlab.temporalAction U V a) := by
    unfold spatialWord
    apply four_distance
    · exact he _
    · exact he _
    · rw [distance_inv]; exact he _
    · rw [distance_inv]; exact he _
  have ht := trace_distance (spatialWord U p) (spatialWord W p)
  have hg : plaquette p W=plaquette p V := plaquette_gauge a V p
  change (plaquette p U-plaquette p W)^2 ≤ _ at ht
  rw [hg] at ht
  have hs := Real.sq_sqrt (by linarith [(PeriodicWilsonSlab.temporal_action_bounds U V a).1] :
    0 ≤ 2*PeriodicWilsonSlab.temporalAction U V a)
  have hsq := mul_self_le_mul_self (norm_nonneg (lift (spatialWord U p)-lift (spatialWord W p))) hd
  change distance (spatialWord U p) (spatialWord W p)*distance (spatialWord U p) (spatialWord W p) ≤ _ at hsq
  nlinarith

variable {beta : ℝ} (g : GroundData beta)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability

def centered (p : SpatialFace) (U : State) : ℝ := plaquette p U-(∫ V,plaquette p V ∂g.stationary)

theorem centered_memLp (p : SpatialFace) : MemLp (centered g p) 2 g.stationary :=
  (plaquette_memLp g p).sub (memLp_const _)

def vector (p : SpatialFace) : StateL2 g := (centered_memLp g p).toLp (centered g p)

theorem vector_norm_square (p : SpatialFace) : ‖vector g p‖^2=variance (plaquette p) g.stationary := by
  rw [vector,PeriodicTransferVariation.state_norm_square]
  exact (variance_eq_integral (plaquette_measurable p).aemeasurable).symm

theorem vector_mean_zero (p : SpatialFace) : (∫ U,vector g p U ∂g.stationary)=0 := by
  rw [vector,integral_congr_ae (MemLp.coeFn_toLp (centered_memLp g p))]
  unfold centered
  rw [integral_sub ((plaquette_memLp g p).integrable (by norm_num)) (integrable_const _),
    integral_const,probReal_univ,one_smul,sub_self]

theorem vector_norm_pos (p : SpatialFace) : 0 < ‖vector g p‖ := by
  have h := variance_pos g p
  rw [← vector_norm_square] at h
  nlinarith [norm_nonneg (vector g p)]

def normalized (p : SpatialFace) : StateL2 g := ‖vector g p‖⁻¹ • vector g p

theorem normalized_norm (p : SpatialFace) : ‖normalized g p‖=1 := by
  rw [normalized,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (vector_norm_pos g p))]
  exact inv_mul_cancel₀ (ne_of_gt (vector_norm_pos g p))

theorem normalized_mean_zero (p : SpatialFace) : (∫ U,normalized g p U ∂g.stationary)=0 := by
  rw [normalized,integral_congr_ae (Lp.coeFn_smul ‖vector g p‖⁻¹ (vector g p))]
  simp only [Pi.smul_apply]
  rw [integral_smul,vector_mean_zero,smul_zero]

theorem vector_residual_bound (p : SpatialFace) :
    ‖operator g (vector g p)-vector g p‖^2 ≤ 32*(∫ q,temporalEnergy q ∂tripleLaw g) := by
  apply PeriodicTransferVariation.variation_bound g (centered g p) (centered_memLp g p)
    ((plaquette_measurable p).sub measurable_const) 32
  intro q
  have h := plaquette_change q.1.1 q.1.2 q.2 p
  change (plaquette p q.1.1-plaquette p q.1.2)^2 ≤ 32*temporalEnergy q at h
  unfold centered
  nlinarith

theorem normalized_residual_bound (p : SpatialFace) :
    ‖operator g (normalized g p)-normalized g p‖^2 ≤
      32*(∫ q,temporalEnergy q ∂tripleLaw g)/variance (plaquette p) g.stationary := by
  have he : operator g (normalized g p)-normalized g p=
      ‖vector g p‖⁻¹ • (operator g (vector g p)-vector g p) := by
    rw [normalized,map_smul,smul_sub]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (vector_norm_pos g p))]
  apply (le_div_iff₀ (variance_pos g p)).mpr
  have hinv : ‖vector g p‖⁻¹*‖vector g p‖=1 := inv_mul_cancel₀ (ne_of_gt (vector_norm_pos g p))
  calc
    _ = (‖vector g p‖⁻¹*‖vector g p‖)^2*‖operator g (vector g p)-vector g p‖^2 := by
      rw [← vector_norm_square]
      ring
    _ = ‖operator g (vector g p)-vector g p‖^2 := by rw [hinv]; ring
    _ ≤ _ := vector_residual_bound g p
end OperatorDerivativeRewrite.Foundation.PeriodicCurvatureTransfer
