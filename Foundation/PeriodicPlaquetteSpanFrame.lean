import Foundation.PeriodicBridgeInnovation
import Foundation.PeriodicGaugeSaturatedGround

/-! Actual local plaquette-span frames from private observable coordinates.
No independence of the coupled Wilson conditional laws is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicPlaquetteSpanFrame
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicLinkStaples
open PeriodicNativeCompression PeriodicBridgeInnovation PeriodicCurvatureVariance PeriodicSlabGround
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar
  PeriodicAugmentedBridge.law PeriodicGroundBridge.law PeriodicLinkDisintegration.split
  PeriodicLinkDisintegration.marginal GroundData.stationary GroundData.transition incidentFaces
private abbrev vertexDecidableEq : DecidableEq SpatialVertex :=
  fun a b => Fintype.decidablePiFintype a b
attribute [local instance] vertexDecidableEq

def pair (p q : SpatialFace) (a b : ℝ) (V : State) : ℝ := a*plaquette p V+b*plaquette q V

theorem pair_measurable (p q : SpatialFace) (a b : ℝ) : Measurable (pair p q a b) :=
  ((plaquette_measurable p).const_mul a).add ((plaquette_measurable q).const_mul b)

theorem pair_bound (p q : SpatialFace) (a b : ℝ) (V : State) :
    |pair p q a b V| ≤ |a|+|b| := by
  have hp := halfTrace_bound (spatialWord V p)
  have hq := halfTrace_bound (spatialWord V q)
  unfold pair plaquette
  calc
    _ ≤ |a*halfTrace (spatialWord V p)|+|b*halfTrace (spatialWord V q)| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul, abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]

/-- A uniform lower bound for the true conditional centered fibers integrates
to the ORIGINAL augmented energy, with its partition-weighted exterior law. -/
theorem energy_lower_of_fiber (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : State → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M)
    (L : ℝ) (hL : ∀ r : PeriodicLinkDisintegration.Rest e,
      L ≤ ∫ A, (f ((PeriodicLinkDisintegration.split e).symm (r,A)).1-
        conditionalMean e β U W (fun z => f z.1) r)^2
          ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) :
    L ≤ energy e β f U W := by
  letI := PeriodicLinkDisintegration.marginal_probability e β U W
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  let F : PeriodicLinkDisintegration.Rest e × SU2 → ℝ := fun z =>
    (f ((PeriodicLinkDisintegration.split e).symm z).1-
      conditionalMean e β U W (fun z => f z.1) z.1)^2
  have hm : Measurable F :=
    (((hf.comp measurable_fst).comp (PeriodicLinkDisintegration.split e).symm.measurable).sub
      ((conditionalMean_measurable e β U W (fun z => f z.1) (hf.comp measurable_fst)).comp measurable_fst)).pow_const 2
  have hbF (z : PeriodicLinkDisintegration.Rest e × SU2) : |F z| ≤ 4*M^2 := by
    have h1 := hb ((PeriodicLinkDisintegration.split e).symm z).1
    have h2 := conditionalMean_bound e β U W (fun z => f z.1) M (fun z => hb z.1) z.1
    have hd := abs_sub (f ((PeriodicLinkDisintegration.split e).symm z).1)
      (conditionalMean e β U W (fun z => f z.1) z.1)
    dsimp only [F]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (f ((PeriodicLinkDisintegration.split e).symm z).1-
      conditionalMean e β U W (fun z => f z.1) z.1), abs_nonneg (f ((PeriodicLinkDisintegration.split e).symm z).1-
      conditionalMean e β U W (fun z => f z.1) z.1)]
  have hi : Integrable F ((PeriodicLinkDisintegration.marginal e β U W) ⊗ₘ
      PeriodicLinkDisintegration.conditionalKernel e β U W) :=
    Integrable.of_bound hm.aestronglyMeasurable (4*M^2)
      (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hbF z))
  have h := integral_mono (integrable_const L) hi.integral_compProd hL
  simp only [integral_const, probReal_univ, one_smul] at h
  simp only [Kernel.prodMkLeft_apply, Kernel.const_apply] at h
  have hs : MeasurePreserving (PeriodicLinkDisintegration.split e) (PeriodicAugmentedBridge.law β U W)
      ((PeriodicLinkDisintegration.marginal e β U W) ⊗ₘ PeriodicLinkDisintegration.conditionalKernel e β U W) :=
    ⟨(PeriodicLinkDisintegration.split e).measurable, PeriodicLinkDisintegration.actual_factorization e β U W⟩
  have he := (hs.integral_comp' F).trans (Measure.integral_compProd hi)
  have hx : energy e β f U W = ∫ z, F ((PeriodicLinkDisintegration.split e) z)
      ∂PeriodicAugmentedBridge.law β U W := by
    simp only [energy, rowMean, F, MeasurableEquiv.symm_apply_apply]
  rw [← he, ← hx] at h
  exact h

/-- A private edge observes the entire first coefficient, without erasing
the actual nonlinear coupling to the other face in the conditional law. -/
theorem private_edge_lower (p q : SpatialFace) (k : Fin 4)
    (hq : q ∉ incidentFaces (faceEdge p k)) (β : ℝ) (hβ : 0 ≤ β)
    (U W : State) (a b : ℝ) :
    a^2*(6/(49*(1+6*β)^2)) ≤ energy (faceEdge p k) β (pair p q a b) U W := by
  apply energy_lower_of_fiber (faceEdge p k) β U W (pair p q a b) (pair_measurable p q a b)
    (|a|+|b|) (by positivity) (pair_bound p q a b)
  intro r
  let C := faceRemainder (PeriodicLinkDisintegration.baseField (faceEdge p k) r) p k
  have he (A : SU2) : pair p q a b ((PeriodicLinkDisintegration.split (faceEdge p k)).symm (r,A)).1 =
      a*halfTrace (C*A)+b*plaquette q (PeriodicLinkDisintegration.baseField (faceEdge p k) r) := by
    rw [PeriodicLinkDisintegration.assemble]
    unfold pair plaquette
    rw [spatial_trace_at_slot, spatial_word_nonincident _ _ q hq, SU2WilsonConvolution.halfTrace_mul_comm]
  letI := PeriodicLinkDisintegration.kernel_markov (faceEdge p k) β U W
  have hm : Measurable (fun A : SU2 => pair p q a b
      ((PeriodicLinkDisintegration.split (faceEdge p k)).symm (r,A)).1) :=
    (pair_measurable p q a b).comp (measurable_fst.comp
      ((PeriodicLinkDisintegration.split (faceEdge p k)).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  change a^2*(6/(49*(1+6*β)^2)) ≤ ∫ A,
    (pair p q a b ((PeriodicLinkDisintegration.split (faceEdge p k)).symm (r,A)).1-
      ∫ B, pair p q a b ((PeriodicLinkDisintegration.split (faceEdge p k)).symm (r,B)).1
        ∂PeriodicLinkDisintegration.conditionalKernel (faceEdge p k) β U W r)^2
          ∂PeriodicLinkDisintegration.conditionalKernel (faceEdge p k) β U W r
  rw [← variance_eq_integral hm.aemeasurable]
  rw [show (fun A : SU2 => pair p q a b ((PeriodicLinkDisintegration.split (faceEdge p k)).symm (r,A)).1) =
      (fun A => a*halfTrace (C*A)+b*plaquette q (PeriodicLinkDisintegration.baseField (faceEdge p k) r)) from funext he]
  have htm : Measurable (fun A : SU2 => halfTrace (C*A)) :=
    halfTrace_measurable.comp (measurable_const_mul C)
  have ham : Measurable (fun A : SU2 => a*halfTrace (C*A)) := htm.const_mul a
  rw [variance_add_const ham.aestronglyMeasurable, variance_const_mul]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
  rw [variance_eq_integral htm.aemeasurable]
  exact PeriodicPlaquetteVarianceLower.centered_fiber (faceEdge p k) β hβ U W r C _

theorem pair_swap (p q : SpatialFace) (a b : ℝ) : pair q p b a = pair p q a b := by
  funext V
  exact add_comm _ _

theorem pair_gauge (p q : SpatialFace) (a b : ℝ) (g : Gauge) (V : State) :
    pair p q a b (PeriodicSlabGauge.gaugeAction g V) = pair p q a b V := by
  unfold pair plaquette
  rw [PeriodicSlabGauge.spatial_word_covariant, PeriodicSlabGauge.spatial_word_covariant,
    halfTrace_conjugate, halfTrace_conjugate]

theorem pair_center_even (p q : SpatialFace) (a b : ℝ) (i : Fin 3) (V : State) :
    pair p q a b (PeriodicCenterSeam.flip i V) = pair p q a b V := by
  unfold pair plaquette
  rw [PeriodicCenterSeam.spatial_word, PeriodicCenterSeam.spatial_word]

variable {β : ℝ} (d : GroundData β)
private instance stationary_probability : IsProbabilityMeasure d.stationary := d.stationary_probability
private instance transition_markov : IsMarkovKernel d.transition := d.transition_markov

theorem pair_memLp (p q : SpatialFace) (a b : ℝ) : MemLp (pair p q a b) 2 d.stationary :=
  ((plaquette_memLp d p).const_mul a).add ((plaquette_memLp d q).const_mul b)

theorem averaged_private_lower (p q : SpatialFace) (k : Fin 4)
    (hq : q ∉ incidentFaces (faceEdge p k)) (hβ : 0 ≤ β) (a b : ℝ) :
    a^2*(6/(49*(1+6*β)^2)) ≤ averagedEnergy d (faceEdge p k) (pair p q a b) := by
  obtain ⟨hi,hr⟩ := averagedEnergy_integrable d (faceEdge p k) (pair p q a b)
    (pair_measurable p q a b) (|a|+|b|) (by positivity) (pair_bound p q a b)
  have hrow (U : State) : a^2*(6/(49*(1+6*β)^2)) ≤
      ∫ W, energy (faceEdge p k) β (pair p q a b) U W ∂((d.transition ∘ₖ d.transition) U) := by
    have h := integral_mono (integrable_const (a^2*(6/(49*(1+6*β)^2)))) (hr U)
      (fun W => private_edge_lower p q k hq β hβ U W a b)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have h := integral_mono (integrable_const (a^2*(6/(49*(1+6*β)^2)))) hi hrow
  simpa only [integral_const, probReal_univ, one_smul,
    PeriodicBridgeInnovation.averagedEnergy, PeriodicBridgeInnovation.average] using h

/-- True covariance is retained through the add/subtract variance identities.
No orthogonality, independence or diagonal covariance matrix is assumed. -/
theorem pair_variance_upper (p q : SpatialFace) (a b : ℝ) :
    variance (pair p q a b) d.stationary ≤
      2*a^2*variance (plaquette p) d.stationary+2*b^2*variance (plaquette q) d.stationary := by
  have hx : MemLp (fun V => a*plaquette p V) 2 d.stationary := (plaquette_memLp d p).const_mul a
  have hy : MemLp (fun V => b*plaquette q V) 2 d.stationary := (plaquette_memLp d q).const_mul b
  have ha := variance_fun_add hx hy
  have hs := variance_fun_sub hx hy
  simp only [variance_const_mul] at ha hs
  change variance (pair p q a b) d.stationary = _ at ha
  nlinarith [variance_nonneg (fun V => a*plaquette p V-b*plaquette q V) d.stationary]

theorem pair_variance_scale (p q : SpatialFace) (a b : ℝ) (hβ : 16777216 ≤ β) :
    variance (pair p q a b) d.stationary ≤
      (64*PeriodicGaugeSaturatedGround.ratioConstant/β^2)*(a^2+b^2) := by
  have h := pair_variance_upper d p q a b
  have hp := mul_le_mul_of_nonneg_left
    (PeriodicGaugeSaturatedGround.plaquette_variance_uniform_upper β hβ d p)
    (by positivity : 0 ≤ 2*a^2)
  have hq := mul_le_mul_of_nonneg_left
    (PeriodicGaugeSaturatedGround.plaquette_variance_uniform_upper β hβ d q)
    (by positivity : 0 ≤ 2*b^2)
  calc
    _ ≤ 2*a^2*variance (plaquette p) d.stationary+2*b^2*variance (plaquette q) d.stationary := h
    _ ≤ 2*a^2*(32*PeriodicGaugeSaturatedGround.ratioConstant/β^2)+
        2*b^2*(32*PeriodicGaugeSaturatedGround.ratioConstant/β^2) := add_le_add hp hq
    _ = _ := by ring

private theorem row_floor_scale (hβ : 1 ≤ β) :
    6/(2401*β^2) ≤ 6/(49*(1+6*β)^2) := by
  have hs : (1+6*β)^2 ≤ 49*β^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ β-1) (by linarith : 0 ≤ 13*β+1)]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 2401*β^2)
    (by positivity : (0:ℝ) < 49*(1+6*β)^2)).mpr
  nlinarith

/-- A coupling-uniform native frame on the entire TWO-plaquette span,
under explicit private-edge hypotheses in the original nonlinear model. -/
theorem span_frame (p q : SpatialFace) (k l : Fin 4)
    (hq : q ∉ incidentFaces (faceEdge p k)) (hp : p ∉ incidentFaces (faceEdge q l))
    (hβ : 16777216 ≤ β) (a b : ℝ) :
    PeriodicGaugeSaturatedGround.uniformFloor*variance (pair p q a b) d.stationary ≤
      averagedEnergy d (faceEdge p k) (pair p q a b)+
        averagedEnergy d (faceEdge q l) (pair p q a b) := by
  have hb : 0 ≤ β := by linarith
  have h1 := averaged_private_lower d p q k hq hb a b
  have h2 := averaged_private_lower d q p l hp hb b a
  rw [pair_swap] at h2
  have hv := mul_le_mul_of_nonneg_left (pair_variance_scale d p q a b hβ)
    PeriodicGaugeSaturatedGround.uniformFloor_pos.le
  have hs := mul_le_mul_of_nonneg_left (row_floor_scale (by linarith : 1 ≤ β))
    (by positivity : 0 ≤ a^2+b^2)
  have hid : PeriodicGaugeSaturatedGround.uniformFloor*
      (64*PeriodicGaugeSaturatedGround.ratioConstant/β^2) = 6/(2401*β^2) := by
    unfold PeriodicGaugeSaturatedGround.uniformFloor
    field_simp [PeriodicGaugeSaturatedGround.ratioConstant_pos.ne', (by linarith : β ≠ 0)]
    <;> ring
  rw [← mul_assoc, hid] at hv
  nlinarith

/-- Positive relative PHYSICAL Dirichlet form on the centered local span.
No invariance of that span under the temporal operator is asserted. -/
theorem physical_form_lower (p q : SpatialFace) (k l : Fin 4)
    (hq : q ∉ incidentFaces (faceEdge p k)) (hp : p ∉ incidentFaces (faceEdge q l))
    (hβ : 16777216 ≤ β) (a b : ℝ) :
    (PeriodicGaugeSaturatedGround.uniformFloor/4)*variance (pair p q a b) d.stationary ≤
      SelfAdjointContractionIteration.dissipation (PeriodicSlabL2.operator d) ((pair_memLp d p q a b).toLp _) := by
  have h := span_frame d p q k l hq hp hβ a b
  have h1 := averagedEnergy_le_physical d (faceEdge p k) (pair p q a b) (pair_measurable p q a b)
    (|a|+|b|) (by positivity) (pair_bound p q a b) (pair_memLp d p q a b)
  have h2 := averagedEnergy_le_physical d (faceEdge q l) (pair p q a b) (pair_measurable p q a b)
    (|a|+|b|) (by positivity) (pair_bound p q a b) (pair_memLp d p q a b)
  linarith

def firstFace : SpatialFace := ⟨((fun _ => 0),(0,1)), by decide⟩
def secondFace : SpatialFace := ⟨((fun _ => 0),(0,2)), by decide⟩

theorem faces_share_edge : faceEdge firstFace 0 = faceEdge secondFace 0 := rfl

theorem first_private : secondFace ∉ incidentFaces (faceEdge firstFace 3) := by
  intro h
  obtain ⟨k,hk⟩ := (mem_incidentFaces (faceEdge firstFace 3) secondFace).mp h
  have hd := congrArg Prod.snd hk
  fin_cases k <;> norm_num [faceEdge, firstFace, secondFace] at hd

theorem second_private : firstFace ∉ incidentFaces (faceEdge secondFace 3) := by
  intro h
  obtain ⟨k,hk⟩ := (mem_incidentFaces (faceEdge secondFace 3) firstFace).mp h
  have hd := congrArg Prod.snd hk
  fin_cases k <;> norm_num [faceEdge, firstFace, secondFace] at hd

theorem adjacent_span_frame (hβ : 16777216 ≤ β) (a b : ℝ) :
    PeriodicGaugeSaturatedGround.uniformFloor*variance (pair firstFace secondFace a b) d.stationary ≤
      averagedEnergy d (faceEdge firstFace 3) (pair firstFace secondFace a b)+
        averagedEnergy d (faceEdge secondFace 3) (pair firstFace secondFace a b) :=
  span_frame d firstFace secondFace 3 3 first_private second_private hβ a b

/-- Sharper actual bridge comparison: predict by the original one-sided
conditional mean, and obtain native physical NORM loss, not just dissipation. -/
theorem averagedEnergy_le_norm_loss (e : SpatialEdge) (f : State → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) (hm : MemLp f 2 d.stationary) :
    averagedEnergy d e f ≤ ‖hm.toLp f‖^2-‖PeriodicSlabL2.operator d (hm.toLp f)‖^2 := by
  let m := PeriodicSlabL2.transfer d f
  have hmM (U : State) : |m U| ≤ M := PeriodicSlabL2.transfer_bound d f M hb U
  have hb2 (V : State) : |f V^2| ≤ M^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hb V, sq_abs (f V), abs_nonneg (f V)]
  have hF2 : Integrable (fun U => ∫ V, f V^2 ∂d.transition U) d.stationary := by
    apply Integrable.of_bound
      ((hf.pow_const 2).stronglyMeasurable.integral_kernel (κ := d.transition)).aestronglyMeasurable (M^2)
    filter_upwards with U
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := d.transition U) (f := fun V => f V^2) (C := M^2)
        (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using hb2 V))
  have hM2 : Integrable (fun U => m U^2) d.stationary :=
    (PeriodicSlabL2.transfer_memLp d f hf M hb).integrable_sq
  obtain ⟨hi,hr⟩ := averagedEnergy_integrable d e f hf M hM hb
  have hrow (U : State) :
      (∫ W, energy e β f U W ∂((d.transition ∘ₖ d.transition) U)) ≤
        (∫ V, f V^2 ∂d.transition U)-m U^2 := by
    let F : State → ℝ := fun V => (f V-m U)^2
    have hFm : Measurable F := (hf.sub measurable_const).pow_const 2
    have hFb (V : State) : |F V| ≤ 4*M^2 := by
      have hdiff := abs_sub (f V) (m U)
      dsimp only [F]
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hb V, hmM U, sq_abs (f V-m U), abs_nonneg (f V-m U)]
    have hH : Measurable (fun W => ∫ V, F V ∂PeriodicGroundBridge.law β U W) := by
      simpa only [PeriodicGroundBridge.bridgeKernel_apply, Function.comp_def, id_eq] using
        ((hFm.stronglyMeasurable.integral_kernel (κ := PeriodicGroundBridge.bridgeKernel β)).measurable.comp
          (measurable_const.prodMk measurable_id))
    have hHi : Integrable (fun W => ∫ V, F V ∂PeriodicGroundBridge.law β U W)
        ((d.transition ∘ₖ d.transition) U) := by
      apply Integrable.of_bound hH.aestronglyMeasurable (4*M^2)
      filter_upwards with W
      simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := PeriodicGroundBridge.law β U W) (f := F) (C := 4*M^2)
          (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using hFb V))
    have h := integral_mono (hr U) hHi (fun W => energy_le_reference e β U W f hf M hM hb (m U))
    rw [PeriodicGroundBridge.bridge_average d U F hFm (4*M^2) hFb] at h
    have hv : MemLp f 2 (d.transition U) := MemLp.of_bound hf.aestronglyMeasurable M
      (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using hb V))
    have hvar := variance_eq_integral (μ := d.transition U) hf.aemeasurable
    change variance f (d.transition U) = ∫ V, F V ∂d.transition U at hvar
    rw [← hvar, variance_eq_sub hv] at h
    exact h
  have h := integral_mono hi (hF2.sub hM2) hrow
  simp only [Pi.sub_apply] at h
  rw [integral_sub hF2 hM2, d.transition_stationary (fun V => f V^2) (hf.pow_const 2) (M^2) hb2] at h
  have hP : ‖PeriodicSlabL2.operator d (hm.toLp f)‖^2 = ∫ U, m U^2 ∂d.stationary := by
    rw [PeriodicSlabL2.operator_toLp d f hm hf M hb, PeriodicTransferVariation.state_norm_square]
  have hF := PeriodicTransferVariation.state_norm_square d f hm
  rw [← hP, ← hF] at h
  exact h

theorem energy_sub_const (e : SpatialEdge) (U W : State) (p q : SpatialFace) (a b c : ℝ) :
    energy e β (fun V => pair p q a b V-c) U W = energy e β (pair p q a b) U W := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  have hrow (z : PeriodicAugmentedBridge.Space) : rowMean e β (fun V => pair p q a b V-c) ((U,W),z) =
      rowMean e β (pair p q a b) ((U,W),z)-c := by
    let r := ((PeriodicLinkDisintegration.split e) z).1
    have hi : Integrable (fun A => pair p q a b ((PeriodicLinkDisintegration.split e).symm (r,A)).1)
        (PeriodicLinkDisintegration.conditionalKernel e β U W r) :=
      Integrable.of_bound ((pair_measurable p q a b).comp (measurable_fst.comp
        ((PeriodicLinkDisintegration.split e).symm.measurable.comp (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
        (|a|+|b|) (ae_of_all _ (fun A => by simpa only [Real.norm_eq_abs] using pair_bound p q a b _))
    change (∫ A, (pair p q a b ((PeriodicLinkDisintegration.split e).symm (r,A)).1-c)
        ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) = _
    rw [integral_sub hi (integrable_const c), integral_const, probReal_univ, one_smul]
    rfl
  unfold energy
  simp_rw [hrow]
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  ring

def centeredPair (p q : SpatialFace) (a b : ℝ) (V : State) : ℝ :=
  pair p q a b V-(∫ Z, pair p q a b Z ∂d.stationary)

theorem centeredPair_linear (p q : SpatialFace) (a b : ℝ) (V : State) :
    centeredPair d p q a b V = a*PeriodicCurvatureTransfer.centered d p V+
      b*PeriodicCurvatureTransfer.centered d q V := by
  have hmean : (∫ Z, pair p q a b Z ∂d.stationary) =
      a*(∫ Z, plaquette p Z ∂d.stationary)+b*(∫ Z, plaquette q Z ∂d.stationary) := by
    unfold pair
    rw [integral_add (((plaquette_memLp d p).integrable (by norm_num)).const_mul a)
      (((plaquette_memLp d q).integrable (by norm_num)).const_mul b), integral_const_mul, integral_const_mul]
  unfold centeredPair PeriodicCurvatureTransfer.centered
  rw [hmean]
  unfold pair
  ring

theorem centeredPair_memLp (p q : SpatialFace) (a b : ℝ) :
    MemLp (centeredPair d p q a b) 2 d.stationary := (pair_memLp d p q a b).sub (memLp_const _)

def vector (p q : SpatialFace) (a b : ℝ) : PeriodicSlabL2.StateL2 d :=
  (centeredPair_memLp d p q a b).toLp (centeredPair d p q a b)

theorem vector_norm_square (p q : SpatialFace) (a b : ℝ) :
    ‖vector d p q a b‖^2 = variance (pair p q a b) d.stationary := by
  rw [vector, PeriodicTransferVariation.state_norm_square]
  exact (variance_eq_integral (pair_measurable p q a b).aemeasurable).symm

/-- Actual one-step native norm loss on the complete centered two-plaquette span.
No all-time contraction or invariant-subspace assertion is made. -/
theorem span_norm_loss (p q : SpatialFace) (k l : Fin 4)
    (hq : q ∉ incidentFaces (faceEdge p k)) (hp : p ∉ incidentFaces (faceEdge q l))
    (hβ : 16777216 ≤ β) (a b : ℝ) :
    ‖PeriodicSlabL2.operator d (vector d p q a b)‖^2+
      (PeriodicGaugeSaturatedGround.uniformFloor/2)*‖vector d p q a b‖^2 ≤ ‖vector d p q a b‖^2 := by
  let c := ∫ Z, pair p q a b Z ∂d.stationary
  have hm : Measurable (centeredPair d p q a b) := (pair_measurable p q a b).sub measurable_const
  have hb (V : State) : |centeredPair d p q a b V| ≤ |a|+|b|+|c| := by
    have h := abs_sub (pair p q a b V) c
    change |pair p q a b V-c| ≤ _
    linarith [pair_bound p q a b V]
  have h := span_frame d p q k l hq hp hβ a b
  have he (e : SpatialEdge) : averagedEnergy d e (centeredPair d p q a b) =
      averagedEnergy d e (pair p q a b) := by
    unfold averagedEnergy PeriodicBridgeInnovation.average centeredPair
    simp_rw [energy_sub_const]
  have h1 := averagedEnergy_le_norm_loss d (faceEdge p k) _ hm (|a|+|b|+|c|)
    (by positivity) hb (centeredPair_memLp d p q a b)
  have h2 := averagedEnergy_le_norm_loss d (faceEdge q l) _ hm (|a|+|b|+|c|)
    (by positivity) hb (centeredPair_memLp d p q a b)
  rw [he] at h1 h2
  change _ ≤ ‖vector d p q a b‖^2-‖PeriodicSlabL2.operator d (vector d p q a b)‖^2 at h1 h2
  rw [← vector_norm_square d p q a b] at h
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicPlaquetteSpanFrame
