import Foundation.PeriodicPhysicalBridgeScore
import Foundation.PeriodicPhysicalKineticReduction
import Foundation.PeriodicCenteredHolonomy
import Mathlib.Probability.Independence.Basic
/-! A concrete off-diagonal boundary-response test using physical winding.
Actual Wilson bridge kernels and normalizers are retained throughout. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Quaternion
namespace OperatorDerivativeRewrite.Foundation.PeriodicWindingEndpointResponse
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicEndpointScore PeriodicEndpointFibreWitness PeriodicSpatialHolonomy
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar kernel
private abbrev vertexDecidable : DecidableEq SpatialVertex := fun a b => Fintype.decidablePiFintype a b
attribute [local instance] vertexDecidable

/-- The explicit rough endpoints are gauge related, although the prescribed
endpoint TANGENTS transform with opposite signs. -/
theorem endpoint_flip : PeriodicEndpointWard.field PeriodicEndpointWard.flip leftEndpoint =
    rightEndpoint := by
  funext e
  by_cases he : e = PeriodicCancellingBoundaryResponse.edge
  · subst e
    simp only [PeriodicEndpointWard.field, gaugeAction, leftEndpoint, rightEndpoint,
      Function.update_self]
    rw [PeriodicEndpointWard.flip_axis]
    congr 1
    ring
  · simp only [PeriodicEndpointWard.field, gaugeAction, leftEndpoint, rightEndpoint,
      Function.update_of_ne he, Pi.one_apply, mul_one, mul_inv_cancel]

/-- Exact full-kernel square. This is not a fixed-rest or kinetic replacement. -/
theorem bridge_square (β h : ℝ) (V : State) :
    PeriodicGroundBridge.bridgeWeight β (left h leftEndpoint) (right h rightEndpoint) V =
      (kernel β (right (-h) leftEndpoint) V)^2 := by
  unfold PeriodicGroundBridge.bridgeWeight
  rw [PeriodicPhysicalBridgeScore.kernel_left_right,
    kernel_symmetric β V (right h rightEndpoint), ← endpoint_flip,
    PeriodicEndpointWard.right_flip]
  change kernel β (right (-h) leftEndpoint) V *
    kernel β (gaugeAction (fun _ => PeriodicEndpointWard.flip) (right (-h) leftEndpoint)) V = _
  rw [kernel_left_invariant, pow_two]

/-- Both endpoints move in the SAME direction after gauge reduction. Thus this
identity does not invoke the previous opposite-direction diagonal cancellation. -/
theorem bridge_law (β h : ℝ) :
    PeriodicGroundBridge.law β (left h leftEndpoint) (right h rightEndpoint) =
      PeriodicGroundBridge.law β (right (-h) leftEndpoint) (right (-h) leftEndpoint) := by
  have he : PeriodicGroundBridge.bridgeWeight β (left h leftEndpoint) (right h rightEndpoint) =
      PeriodicGroundBridge.bridgeWeight β (right (-h) leftEndpoint) (right (-h) leftEndpoint) := by
    funext V
    rw [bridge_square]
    unfold PeriodicGroundBridge.bridgeWeight
    rw [kernel_symmetric β V (right (-h) leftEndpoint), pow_two]
  unfold PeriodicGroundBridge.law
  rw [he]

private theorem axis_add (s t : ℝ) :
    SU2JointPlaquetteCubic.axis 0 s * SU2JointPlaquetteCubic.axis 0 t =
      SU2JointPlaquetteCubic.axis 0 (s+t) := by
  unfold SU2JointPlaquetteCubic.axis
  rw [← map_mul]
  apply congrArg hom
  apply Subtype.ext
  change SU2JointPlaquetteCubic.axisRaw 0 s * SU2JointPlaquetteCubic.axisRaw 0 t = _
  ext <;> simp [SU2JointPlaquetteCubic.axisRaw, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, Real.cos_add, Real.sin_add] <;> ring

/-- The genuine gauge-invariant winding test sees this endpoint movement. -/
theorem winding_curve (h : ℝ) :
    PeriodicCenteredHolonomy.first (right (-h) leftEndpoint) = Real.sin (4*h) := by
  have h1 : (shift PeriodicCenteredHolonomy.origin 0,0) ≠ PeriodicCancellingBoundaryResponse.edge := by decide
  have h2 : (twice PeriodicCenteredHolonomy.origin 0,0) ≠ PeriodicCancellingBoundaryResponse.edge := by decide
  have h3 : (thrice PeriodicCenteredHolonomy.origin 0,0) ≠ PeriodicCancellingBoundaryResponse.edge := by decide
  unfold PeriodicCenteredHolonomy.first winding right
  simp only [neg_neg, leftEndpoint, show (PeriodicCenteredHolonomy.origin,0) =
    PeriodicCancellingBoundaryResponse.edge from rfl, Function.update_self,
    Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
    Pi.one_apply, one_mul]
  simp only [axis_add]
  rw [show -Real.pi/2+h+h+h+h = 4*h-Real.pi/2 by ring]
  rw [FourCubeWilsonCubic.axis_trace]
  simp [Real.cos_sub]


open BoundedExponentialTiltResponse

def noise (β : ℝ) : Measure State := Measure.pi (fun _ => SU2WilsonConvolution.increment β)

private theorem singleDensity_integrable (β : ℝ) :
    Integrable (density law halfTrace β) law :=
  (exponential_integrable law halfTrace halfTrace_measurable halfTrace_bound β).div_const _

private theorem singleDensity_nonneg (β : ℝ) (A : SU2) : 0 ≤ density law halfTrace β A :=
  density_nonneg law halfTrace halfTrace_measurable halfTrace_bound β A

private theorem singleDensity_measurable (β : ℝ) : Measurable (density law halfTrace β) :=
  (halfTrace_measurable.const_mul β).exp.div_const _

def noiseDensity (β : ℝ) (X : State) : ℝ := ∏ e, density law halfTrace β (X e)

private theorem noiseDensity_integrable (β : ℝ) : Integrable (noiseDensity β) boundaryHaar := by
  unfold noiseDensity boundaryHaar
  exact Integrable.fintype_prod (fun _ => singleDensity_integrable β)

private theorem noiseDensity_nonneg (β : ℝ) (X : State) : 0 ≤ noiseDensity β X :=
  Finset.prod_nonneg (fun _ _ => singleDensity_nonneg β _)

private theorem noiseDensity_measurable (β : ℝ) : Measurable (noiseDensity β) := by
  unfold noiseDensity
  exact Finset.measurable_prod _ (fun e _ => (singleDensity_measurable β).comp (measurable_pi_apply e))

private theorem density_rectangle (β : ℝ) (S : SpatialEdge → Set SU2)
    (hS : ∀ e, MeasurableSet (S e)) :
    (∫ X in Set.univ.pi S, noiseDensity β X ∂boundaryHaar) =
      ∏ e, ∫ A in S e, density law halfTrace β A ∂law := by
  have he : (Set.univ.pi S).indicator (noiseDensity β) =
      (fun X : State => ∏ e, (S e).indicator (density law halfTrace β) (X e)) := by
    funext X
    by_cases hX : X ∈ Set.univ.pi S
    · have hx : ∀ e, X e ∈ S e := by simpa only [Set.mem_pi, Set.mem_univ, true_implies] using hX
      rw [Set.indicator_of_mem hX]
      exact Finset.prod_congr rfl (fun e _ => (Set.indicator_of_mem (hx e) _).symm)
    · rw [Set.indicator_of_notMem hX]
      have hx : ¬∀ e, X e ∈ S e := by simpa only [Set.mem_pi, Set.mem_univ, true_implies] using hX
      push_neg at hx
      obtain ⟨e, he⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ e) (Set.indicator_of_notMem he _)).symm
  rw [← integral_indicator (MeasurableSet.univ_pi hS), he]
  unfold boundaryHaar
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl (fun e _ => integral_indicator (hS e))

/-- Actual full192-link product law, with the original Haar density. -/
theorem noise_density (β : ℝ) :
    noise β = boundaryHaar.withDensity (fun X => ENNReal.ofReal (noiseDensity β X)) := by
  letI := SU2WilsonConvolution.increment_probability β
  unfold noise
  apply Measure.pi_eq
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS),
    ← ofReal_integral_eq_lintegral_ofReal (noiseDensity_integrable β).integrableOn
      (ae_of_all _ (noiseDensity_nonneg β)), density_rectangle β S hS,
    ENNReal.ofReal_prod_of_nonneg (fun e _ => integral_nonneg (fun A => singleDensity_nonneg β A))]
  apply Finset.prod_congr rfl
  intro e _
  unfold SU2WilsonConvolution.increment tiltedMeasure
  rw [withDensity_apply _ (hS e)]
  exact (ofReal_integral_eq_lintegral_ofReal (singleDensity_integrable β).integrableOn
    (ae_of_all _ (singleDensity_nonneg β)))

theorem noise_integral (β : ℝ) (f : State → ℝ) :
    (∫ X, f X ∂noise β) = ∫ X, noiseDensity β X * f X ∂boundaryHaar := by
  rw [noise_density, integral_withDensity_eq_integral_toReal_smul
    (noiseDensity_measurable β).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (noiseDensity_nonneg β _), smul_eq_mul]


private theorem laplace_partition (β : ℝ) :
    CubeHaarUpper.laplace β = Real.exp (-β) * partition law halfTrace β := by
  have he (A : SU2) : Real.exp (-β * FourCubePinnedCoercivity.defect A) =
      Real.exp (-β) * Real.exp (β * halfTrace A) := by
    rw [← Real.exp_add]
    congr 1
    unfold FourCubePinnedCoercivity.defect
    ring
  unfold CubeHaarUpper.laplace
  simp_rw [he]
  rw [integral_const_mul]
  simp only [partition, BoundedExponentialTiltResponse.weighted, one_mul]

private theorem singleDensity_laplace (β : ℝ) (A : SU2) :
    density law halfTrace β A = Real.exp (-β * FourCubePinnedCoercivity.defect A) /
      CubeHaarUpper.laplace β := by
  rw [laplace_partition]
  have he : -β * FourCubePinnedCoercivity.defect A = -β + β * halfTrace A := by
    unfold FourCubePinnedCoercivity.defect
    ring
  rw [he, Real.exp_add]
  unfold density
  field_simp [Real.exp_ne_zero (-β)]

private theorem noiseDensity_formula (β : ℝ) (X : State) :
    noiseDensity β X = Real.exp (-β * ∑ e, FourCubePinnedCoercivity.defect (X e)) /
      CubeHaarUpper.laplace β ^ 192 := by
  unfold noiseDensity
  simp_rw [singleDensity_laplace]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, edge_count,
    ← Real.exp_sum, ← Finset.mul_sum]

private theorem kineticDensity_noise (β : ℝ) (U X : State) :
    PeriodicPhysicalKineticReduction.kineticDensity β U (U*X) = noiseDensity β X := by
  have ht : temporalAction U (U*X) 1 = ∑ e, FourCubePinnedCoercivity.defect (X e) := by
    unfold temporalAction
    apply Finset.sum_congr rfl
    intro e _
    have he : temporalWord U (U*X) 1 e = U e * (X e)⁻¹ * (U e)⁻¹ := by
      unfold temporalWord
      simp only [Pi.mul_apply, Pi.one_apply, inv_one, mul_one, one_mul, mul_inv_rev]
      group
    rw [he, halfTrace_conjugate, SU2WilsonConvolution.halfTrace_inv]
    rfl
  rw [PeriodicPhysicalKineticReduction.kineticDensity, ht, noiseDensity_formula]

/-- Exact identification of the full192-link kinetic integral. This does not
remove the spatial multipliers or dressed ground from the native Wilson ratio. -/
theorem kinetic_noise (β : ℝ) (U : State) (f : State → ℝ) :
    PeriodicPhysicalKineticReduction.kinetic β f U = ∫ X, f (U*X) ∂noise β := by
  have mp : MeasurePreserving (fun X : State => U*X) boundaryHaar boundaryHaar := by
    unfold boundaryHaar
    exact measurePreserving_pi (fun _ => law) (fun _ => law)
      (fun e => measurePreserving_mul_left law (U e))
  have h := mp.integral_comp (MeasurableEquiv.mulLeft U).measurableEmbedding
    (fun V => PeriodicPhysicalKineticReduction.kineticDensity β U V * f V)
  change (∫ X, PeriodicPhysicalKineticReduction.kineticDensity β U (U*X) * f (U*X)
    ∂boundaryHaar) = PeriodicPhysicalKineticReduction.kinetic β f U at h
  rw [← h, noise_integral]
  simp_rw [kineticDensity_noise]


private def cycleEdge : Fin 4 → SpatialEdge := ![
  (PeriodicCenteredHolonomy.origin,0), (shift PeriodicCenteredHolonomy.origin 0,0),
  (twice PeriodicCenteredHolonomy.origin 0,0), (thrice PeriodicCenteredHolonomy.origin 0,0)]

private theorem cycleEdge_injective : Function.Injective cycleEdge := by decide

private theorem select_cycle_preserving (β : ℝ) :
    MeasurePreserving (fun X : State => fun j => X (cycleEdge j)) (noise β)
      (Measure.pi (fun _ : Fin 4 => SU2WilsonConvolution.increment β)) := by
  letI := SU2WilsonConvolution.increment_probability β
  have hi := iIndepFun_pi (μ := fun _ : SpatialEdge => SU2WilsonConvolution.increment β)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have hs := hi.precomp cycleEdge_injective
  have hm := hs.map_fun_eq_pi_map (fun j => (measurable_pi_apply (cycleEdge j)).aemeasurable)
  simp only [(measurePreserving_eval (fun _ : SpatialEdge => SU2WilsonConvolution.increment β) _).map_eq] at hm
  exact ⟨measurable_pi_iff.mpr (fun _ => measurable_pi_apply _), hm⟩

private def prepend {n : ℕ} (A : SU2) (X : Fin n → SU2) : Fin (n+1) → SU2 := Fin.cons A X

private theorem head_integral (ν : Measure SU2) [IsProbabilityMeasure ν] (n : ℕ)
    (F : (Fin (n+1) → SU2) → ℝ) (hF : Measurable F) (hb : ∀ X, |F X| ≤ 1) :
    (∫ X, F X ∂Measure.pi (fun _ => ν)) =
      ∫ A, ∫ X : Fin n → SU2, F (prepend A X) ∂Measure.pi (fun _ => ν) ∂ν := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => SU2) 0
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0
  have h := mp.symm.integral_comp e.symm.measurableEmbedding F
  have hi : Integrable (fun p : SU2 × (Fin n → SU2) => F (e.symm p))
      (ν.prod (Measure.pi (fun _ => ν))) := by
    apply Integrable.of_bound (hF.comp e.symm.measurable).aestronglyMeasurable 1
    exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hb (e.symm p))
  rw [← h, integral_prod _ hi]
  congr 1
  funext A
  congr 1
  funext X
  congr 1
  change Fin.insertNth (0 : Fin (n+1)) A X = prepend A X
  exact @Fin.insertNth_zero' n SU2 A X

private theorem cons_measurable {n : ℕ} (A : SU2) :
    Measurable (fun X : Fin n → SU2 => prepend A X) := by
  apply measurable_pi_iff.mpr
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa only [prepend, Fin.cons_zero] using (measurable_const : Measurable (fun _ : Fin n → SU2 => A))
  · simpa only [prepend, Fin.cons_succ] using (measurable_pi_apply k : Measurable (fun X : Fin n → SU2 => X k))

/-- The actual independent-link convolution sees the physical winding sector.
Every one of its four distinct spatial links is integrated exactly once. -/
theorem noise_winding (β : ℝ) (U : State) :
    (∫ X, PeriodicCenteredHolonomy.first (U*X) ∂noise β) =
      SU2WilsonConvolution.coefficient β ^ 4 * PeriodicCenteredHolonomy.first U := by
  letI := SU2WilsonConvolution.increment_probability β
  let F := fun X : Fin 4 → SU2 => halfTrace
    ((U (cycleEdge 0)*X 0)*(U (cycleEdge 1)*X 1)*(U (cycleEdge 2)*X 2)*(U (cycleEdge 3)*X 3))
  have hF : Measurable F := halfTrace_measurable.comp (by fun_prop)
  have hb (X : Fin 4 → SU2) : |F X| ≤ 1 := halfTrace_bound _
  have h := integral_map (μ := noise β) (select_cycle_preserving β).measurable.aemeasurable hF.aestronglyMeasurable
  rw [(select_cycle_preserving β).map_eq] at h
  change (∫ X, F X ∂Measure.pi (fun _ : Fin 4 => SU2WilsonConvolution.increment β)) = _ at h
  have he : (∫ X, PeriodicCenteredHolonomy.first (U*X) ∂noise β) =
      ∫ X, F X ∂Measure.pi (fun _ : Fin 4 => SU2WilsonConvolution.increment β) := by
    rw [h]
    rfl
  have he4 : (∫ X, F X ∂Measure.pi (fun _ : Fin 4 => SU2WilsonConvolution.increment β)) =
      ∫ A, ∫ B, ∫ C, ∫ D,
        halfTrace ((U (cycleEdge 0)*A)*(U (cycleEdge 1)*B)*
          (U (cycleEdge 2)*C)*(U (cycleEdge 3)*D))
        ∂SU2WilsonConvolution.increment β ∂SU2WilsonConvolution.increment β
        ∂SU2WilsonConvolution.increment β ∂SU2WilsonConvolution.increment β := by
    rw [head_integral _ 3 F hF hb]
    congr 1
    funext A
    rw [head_integral _ 2 (fun X => F (prepend A X))
      (hF.comp (cons_measurable A)) (fun X => hb _)]
    congr 1
    funext B
    rw [head_integral _ 1 (fun X => F (prepend A (prepend B X)))
      (hF.comp ((cons_measurable A).comp (cons_measurable B))) (fun X => hb _)]
    congr 1
    funext C
    rw [head_integral _ 0 (fun X => F (prepend A (prepend B (prepend C X))))
      (hF.comp ((cons_measurable A).comp ((cons_measurable B).comp (cons_measurable C))))
      (fun X => hb _)]
    congr 1
    funext D
    change (∫ _ : Fin 0 → SU2, halfTrace ((U (cycleEdge 0)*A)*(U (cycleEdge 1)*B)*
      (U (cycleEdge 2)*C)*(U (cycleEdge 3)*D))
      ∂Measure.pi (fun _ : Fin 0 => SU2WilsonConvolution.increment β)) = _
    simp only [integral_const, probReal_univ, one_smul]
  rw [he, he4]
  have hw := SU2WilsonConvolution.loop4_average β (U (cycleEdge 0)) (U (cycleEdge 1))
    (U (cycleEdge 2)) (U (cycleEdge 3))
  have hc0 : cycleEdge 0 = (PeriodicCenteredHolonomy.origin,0) := rfl
  have hc1 : cycleEdge 1 = (shift PeriodicCenteredHolonomy.origin 0,0) := rfl
  have hc2 : cycleEdge 2 = (twice PeriodicCenteredHolonomy.origin 0,0) := rfl
  have hc3 : cycleEdge 3 = (thrice PeriodicCenteredHolonomy.origin 0,0) := rfl
  simpa only [SU2WilsonConvolution.wordAverage, SU2WilsonConvolution.loop4, one_mul,
    mul_assoc, PeriodicCenteredHolonomy.first, winding, hc0, hc1, hc2, hc3] using hw

theorem kinetic_winding (β : ℝ) (U : State) :
    PeriodicPhysicalKineticReduction.kinetic β PeriodicCenteredHolonomy.first U =
      SU2WilsonConvolution.coefficient β ^ 4 * PeriodicCenteredHolonomy.first U := by
  rw [kinetic_noise, noise_winding]


/-- A fixed spatial counterweight, with its explicit coupling-dependent bound. -/
def weightedWinding (β : ℝ) (V : State) : ℝ :=
  Real.exp (β * spatialAction V / 2) * PeriodicCenteredHolonomy.first V

theorem weightedWinding_measurable (β : ℝ) : Measurable (weightedWinding β) :=
  (((spatial_action_measurable.const_mul β).div_const 2).exp).mul
    PeriodicCenteredHolonomy.first_measurable

theorem weightedWinding_bound (β : ℝ) (V : State) :
    |weightedWinding β V| ≤ Real.exp (192 * |β|) := by
  have he : β * spatialAction V / 2 ≤ 192 * |β| := by
    have h := mul_le_mul_of_nonneg_right (le_abs_self β) (spatial_action_bounds V).1
    have hh := mul_le_mul_of_nonneg_left (spatial_action_bounds V).2 (abs_nonneg β)
    nlinarith
  change |Real.exp (β * spatialAction V / 2) * PeriodicCenteredHolonomy.first V| ≤ _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_of_le_one_right (Real.exp_pos _).le (halfTrace_bound _)).trans
    (Real.exp_le_exp.mpr he)

theorem weightedWinding_gauge (β : ℝ) (a : Gauge) (V : State) :
    weightedWinding β (gaugeAction a V) = weightedWinding β V := by
  unfold weightedWinding PeriodicCenteredHolonomy.first
  rw [spatial_action_invariant, trace_gauge]

private theorem multiplier_cancel (β : ℝ) (V : State) :
    PeriodicPhysicalKineticReduction.multiplier β V * weightedWinding β V =
      PeriodicCenteredHolonomy.first V := by
  unfold PeriodicPhysicalKineticReduction.multiplier weightedWinding
  rw [← mul_assoc, ← Real.exp_add, show -β * spatialAction V / 2 + β * spatialAction V / 2 = 0 by ring,
    Real.exp_zero, one_mul]

/-- An exact full-Wilson kernel moment. The spatial counterweight is part of the
observable, and is not silently discarded from the operator. -/
theorem kernel_winding (β : ℝ) (hβ : 0 ≤ β) (U : State) :
    (∫ V, kernel β U V * weightedWinding β V ∂boundaryHaar) =
      CubeHaarUpper.laplace β ^ 192 * PeriodicPhysicalKineticReduction.multiplier β U *
        (SU2WilsonConvolution.coefficient β ^ 4 * PeriodicCenteredHolonomy.first U) := by
  have hi : Integrable (weightedWinding β) boundaryHaar :=
    Integrable.of_bound (weightedWinding_measurable β).aestronglyMeasurable _
      (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using weightedWinding_bound β V))
  rw [PeriodicPhysicalKineticReduction.invariant_factorization β hβ U (weightedWinding β)
    (weightedWinding_measurable β) hi (weightedWinding_gauge β)]
  simp_rw [multiplier_cancel]
  rw [kinetic_winding]

/-- Corrected input on the ORIGINAL native stationary space. Its bound depends
on coupling and the actual constructed ground lower bound. -/
def nativeWinding {β : ℝ} (g : PeriodicSlabGround.GroundData β) (V : State) : ℝ :=
  weightedWinding β V / g.function V

theorem nativeWinding_measurable {β : ℝ} (g : PeriodicSlabGround.GroundData β) :
    Measurable (nativeWinding g) := (weightedWinding_measurable β).div g.measurable

theorem nativeWinding_bound {β : ℝ} (g : PeriodicSlabGround.GroundData β) (V : State) :
    |nativeWinding g V| ≤ Real.exp (192 * |β|) / g.lower := by
  change |weightedWinding β V / g.function V| ≤ _
  rw [abs_div, abs_of_pos (g.function_pos V)]
  exact (div_le_div_of_nonneg_right (weightedWinding_bound β V) (g.function_pos V).le).trans
    (div_le_div_of_nonneg_left (Real.exp_pos _).le g.lower_pos (g.bounds V).1)

theorem nativeWinding_gauge {β : ℝ} (g : PeriodicSlabGround.GroundData β) (a : Gauge) (V : State) :
    nativeWinding g (gaugeAction a V) = nativeWinding g V := by
  unfold nativeWinding
  rw [weightedWinding_gauge, g.invariant]

theorem nativeWinding_memLp {β : ℝ} (g : PeriodicSlabGround.GroundData β) :
    MemLp (nativeWinding g) 2 g.stationary := by
  letI := g.stationary_probability
  exact MemLp.of_bound (nativeWinding_measurable g).aestronglyMeasurable _
    (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using nativeWinding_bound g V))

/-- Actual stationary transition response, retaining the eigenvalue, spatial
multiplier and ground denominator. This is NOT a winding eigenfunction claim. -/
theorem native_transition_winding {β : ℝ} (hβ : 0 ≤ β) (g : PeriodicSlabGround.GroundData β)
    (U : State) :
    (∫ V, nativeWinding g V ∂g.transition U) =
      (CubeHaarUpper.laplace β ^ 192 * PeriodicPhysicalKineticReduction.multiplier β U *
        (SU2WilsonConvolution.coefficient β ^ 4 * PeriodicCenteredHolonomy.first U)) /
          (g.value * g.function U) := by
  rw [g.transition_integral]
  have he (V : State) : g.function V * nativeWinding g V = weightedWinding β V := by
    unfold nativeWinding
    field_simp [(g.function_pos V).ne']
  simp_rw [he]
  rw [kernel_winding β hβ]


theorem native_operator_winding {β : ℝ} (hβ : 0 ≤ β) (g : PeriodicSlabGround.GroundData β) :
    (fun U => PeriodicSlabL2.operator g ((nativeWinding_memLp g).toLp (nativeWinding g)) U) =ᵐ[g.stationary]
      (fun U => (CubeHaarUpper.laplace β ^ 192 * PeriodicPhysicalKineticReduction.multiplier β U *
        (SU2WilsonConvolution.coefficient β ^ 4 * PeriodicCenteredHolonomy.first U)) /
          (g.value * g.function U)) := by
  rw [PeriodicSlabL2.operator_toLp g (nativeWinding g) (nativeWinding_memLp g)
    (nativeWinding_measurable g) _ (nativeWinding_bound g)]
  filter_upwards [MemLp.coeFn_toLp (PeriodicSlabL2.transfer_memLp g (nativeWinding g)
    (nativeWinding_measurable g) _ (nativeWinding_bound g))] with U hU
  exact hU.trans (native_transition_winding hβ g U)

/-- The ORIGINAL input norm contains the spatial counterweight; it is not the
unweighted kinetic winding norm. -/
theorem native_input_energy {β : ℝ} (g : PeriodicSlabGround.GroundData β) :
    (∫ U, (nativeWinding g U)^2 ∂g.stationary) =
      (∫ U, Real.exp (β * spatialAction U) * (PeriodicCenteredHolonomy.first U)^2
        ∂boundaryHaar) / g.normalizer := by
  rw [g.stationary_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards with U
  unfold nativeWinding weightedWinding
  have he : Real.exp (β * spatialAction U / 2)^2 = Real.exp (β * spatialAction U) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [div_pow, mul_pow, he]
  field_simp [(g.function_pos U).ne']

/-- Exact stationary correlation for the corrected input. This does not identify
coefficient^4 with a native Rayleigh quotient: compare native_input_energy. -/
theorem native_correlation {β : ℝ} (hβ : 0 ≤ β) (g : PeriodicSlabGround.GroundData β) :
    (∫ U, nativeWinding g U * (∫ V, nativeWinding g V ∂g.transition U) ∂g.stationary) =
      (CubeHaarUpper.laplace β ^ 192 * SU2WilsonConvolution.coefficient β ^ 4 /
        (g.value * g.normalizer)) * (∫ U, (PeriodicCenteredHolonomy.first U)^2 ∂boundaryHaar) := by
  rw [g.stationary_integral]
  have he (U : State) : g.function U^2 *
      (nativeWinding g U * (∫ V, nativeWinding g V ∂g.transition U)) =
        (CubeHaarUpper.laplace β ^ 192 * SU2WilsonConvolution.coefficient β ^ 4 / g.value) *
          (PeriodicCenteredHolonomy.first U)^2 := by
    rw [native_transition_winding hβ g U]
    unfold nativeWinding
    have hc := multiplier_cancel β U
    have hz := (g.function_pos U).ne'
    have hv := g.value_pos.ne'
    field_simp [hz, hv]
    linear_combination (CubeHaarUpper.laplace β ^ 192 *
      SU2WilsonConvolution.coefficient β ^ 4 * PeriodicCenteredHolonomy.first U) * hc
  simp_rw [he]
  rw [integral_const_mul]
  ring

/-- A concrete actual transition response is positive at a moving winding field,
for all sufficiently large coupling and every actual ground. This is not an
estimate for the different normalized TWO-sided physical bridge score. -/
theorem eventual_native_response : ∀ᶠ β : ℝ in atTop,
    ∀ g : PeriodicSlabGround.GroundData β,
      0 < ∫ V, nativeWinding g V ∂g.transition (right (-(Real.pi/8)) leftEndpoint) := by
  have hcoef := (tendsto_order.mp SU2WilsonConvolution.coefficient_tendsto_one).1
    (1/2 : ℝ) (by norm_num)
  filter_upwards [hcoef, eventually_ge_atTop (0 : ℝ)] with β hb hβ g
  rw [native_transition_winding hβ g]
  have hw : PeriodicCenteredHolonomy.first (right (-(Real.pi/8)) leftEndpoint) = 1 := by
    rw [winding_curve, show 4*(Real.pi/8)=Real.pi/2 by ring, Real.sin_pi_div_two]
  rw [hw, mul_one]
  exact div_pos (mul_pos (mul_pos (pow_pos (CubeHaarUpper.laplace_pos β hβ) _)
    (Real.exp_pos _)) (pow_pos (by linarith) _)) (mul_pos g.value_pos (g.function_pos _))


/-- Corrected winding remains centered under every actual ground law. -/
theorem native_mean_zero {β : ℝ} (g : PeriodicSlabGround.GroundData β) :
    (∫ U, nativeWinding g U ∂g.stationary) = 0 := by
  apply PeriodicGroundSeamParity.odd_mean_zero g 0 (nativeWinding g)
  intro U
  unfold nativeWinding weightedWinding
  rw [PeriodicCenterSeam.spatial_action, PeriodicCenteredHolonomy.first_odd,
    PeriodicGroundSeamParity.ground_invariant]
  ring


private theorem winding_continuous : Continuous PeriodicCenteredHolonomy.first :=
  PeriodicLowActionBlock.trace_continuous.comp (by unfold winding; fun_prop)

private theorem winding_square_bound (U : State) : (PeriodicCenteredHolonomy.first U)^2 ≤ 1 := by
  have h := halfTrace_bound (winding U PeriodicCenteredHolonomy.origin 0)
  change |PeriodicCenteredHolonomy.first U| ≤ 1 at h
  nlinarith [sq_abs (PeriodicCenteredHolonomy.first U), abs_nonneg (PeriodicCenteredHolonomy.first U)]

private theorem winding_square_integrable :
    Integrable (fun U => (PeriodicCenteredHolonomy.first U)^2) boundaryHaar := by
  apply Integrable.of_bound (PeriodicCenteredHolonomy.first_measurable.pow_const 2).aestronglyMeasurable 1
  exact ae_of_all _ (fun U => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact winding_square_bound U)

def roughWindingMass : ℝ := ∫ U, PeriodicCancellingRestTail.bad.indicator
  (fun U => (PeriodicCenteredHolonomy.first U)^2) U ∂boundaryHaar

private instance su2_secondCountable : SecondCountableTopology SU2 := by
  letI : SecondCountableTopology (Quaternion ℝ) :=
    Quaternion.linearIsometryEquivTuple.toHomeomorph.secondCountableTopology
  exact QuaternionSU2Representation.homeomorph.symm.secondCountableTopology

/-- A fixed positive Haar winding mass in the ACTUAL rough event. -/
theorem roughWindingMass_positive : 0 < roughWindingMass := by
  let F := PeriodicCancellingRestTail.bad.indicator
    (fun U => (PeriodicCenteredHolonomy.first U)^2)
  let O := PeriodicCancellingRestTail.bad ∩ {U | PeriodicCenteredHolonomy.first U ≠ 0}
  have ho : IsOpen O := PeriodicCancellingRestTail.bad_open.inter
    ((isClosed_eq winding_continuous continuous_const).isOpen_compl)
  have hf : PeriodicCenteredHolonomy.first PeriodicCancellingBoundaryResponse.flux = 1 := by
    simp [PeriodicCenteredHolonomy.first, winding, PeriodicCancellingBoundaryResponse.flux,
      SU2OpenLinkGaugeObstruction.halfTrace_one]
  have hex : O.Nonempty := ⟨PeriodicCancellingBoundaryResponse.flux,
    PeriodicCancellingRestTail.flux_bad, by
      change PeriodicCenteredHolonomy.first PeriodicCancellingBoundaryResponse.flux ≠ 0
      rw [hf]
      norm_num⟩
  letI : boundaryHaar.IsOpenPosMeasure := by unfold boundaryHaar; infer_instance
  have hp : 0 < boundaryHaar O := IsOpen.measure_pos _ ho hex
  have hi : Integrable F boundaryHaar :=
    winding_square_integrable.indicator PeriodicCancellingRestTail.bad_measurable
  have hn (U : State) : 0 ≤ F U := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hs : O ⊆ Function.support F := by
    intro U hU
    change F U ≠ 0
    dsimp only [F]
    rw [Set.indicator_of_mem hU.1]
    exact pow_ne_zero _ hU.2
  exact (integral_pos_iff_support_of_nonneg hn hi).mpr (hp.trans_le (measure_mono hs))

def weightedMass (β : ℝ) : ℝ :=
  ∫ U, Real.exp (β * spatialAction U) * (PeriodicCenteredHolonomy.first U)^2 ∂boundaryHaar

private theorem weighted_square (β : ℝ) (U : State) :
    (weightedWinding β U)^2 = Real.exp (β * spatialAction U) * (PeriodicCenteredHolonomy.first U)^2 := by
  unfold weightedWinding
  rw [mul_pow, sq, ← Real.exp_add]
  congr 2
  ring

private theorem weighted_integrable (β : ℝ) :
    Integrable (fun U => Real.exp (β * spatialAction U) * (PeriodicCenteredHolonomy.first U)^2) boundaryHaar := by
  have hm : MemLp (weightedWinding β) 2 boundaryHaar :=
    MemLp.of_bound (weightedWinding_measurable β).aestronglyMeasurable _
      (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using weightedWinding_bound β U))
  simpa only [weighted_square] using hm.integrable_sq

theorem weightedMass_lower (β : ℝ) (hβ : 0 ≤ β) :
    Real.exp β * roughWindingMass ≤ weightedMass β := by
  have hpoint (U : State) : Real.exp β * PeriodicCancellingRestTail.bad.indicator
      (fun U => (PeriodicCenteredHolonomy.first U)^2) U ≤
        Real.exp (β * spatialAction U) * (PeriodicCenteredHolonomy.first U)^2 := by
    by_cases hU : U ∈ PeriodicCancellingRestTail.bad
    · rw [Set.indicator_of_mem hU]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (by nlinarith [PeriodicCancellingRestTail.bad_action U hU])) (sq_nonneg _)
    · rw [Set.indicator_of_notMem hU, mul_zero]
      exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hi := integral_mono
    ((winding_square_integrable.indicator PeriodicCancellingRestTail.bad_measurable).const_mul (Real.exp β))
    (weighted_integrable β) hpoint
  rw [integral_const_mul] at hi
  exact hi

theorem weightedMass_positive (β : ℝ) (hβ : 0 ≤ β) : 0 < weightedMass β :=
  (mul_pos (Real.exp_pos _) roughWindingMass_positive).trans_le (weightedMass_lower β hβ)

def nativeRayleigh {β : ℝ} (g : PeriodicSlabGround.GroundData β) : ℝ :=
  (∫ U, nativeWinding g U * (∫ V, nativeWinding g V ∂g.transition U) ∂g.stationary) /
    (∫ U, (nativeWinding g U)^2 ∂g.stationary)

theorem nativeRayleigh_formula {β : ℝ} (hβ : 0 ≤ β) (g : PeriodicSlabGround.GroundData β) :
    nativeRayleigh g =
      (CubeHaarUpper.laplace β ^ 192 / g.value) * SU2WilsonConvolution.coefficient β ^ 4 *
        (∫ U, (PeriodicCenteredHolonomy.first U)^2 ∂boundaryHaar) / weightedMass β := by
  unfold nativeRayleigh weightedMass
  rw [native_correlation hβ g, native_input_energy g]
  field_simp [g.normalizer_pos.ne']
  <;> ring

private theorem coefficient_power_bound (β : ℝ) : SU2WilsonConvolution.coefficient β ^ 4 ≤ 1 := by
  letI := SU2WilsonConvolution.increment_probability β
  have hb : |SU2WilsonConvolution.coefficient β| ≤ 1 := by
    simpa only [SU2WilsonConvolution.coefficient, Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := SU2WilsonConvolution.increment β) (f := halfTrace)
        (C := 1) (ae_of_all _ (fun A => by simpa only [Real.norm_eq_abs] using halfTrace_bound A))
  have h := pow_le_pow_left₀ (abs_nonneg _) hb 4
  simpa only [← abs_pow, abs_of_nonneg (show 0 ≤ SU2WilsonConvolution.coefficient β ^ 4 by positivity),
    one_pow] using h

theorem nativeRayleigh_nonneg {β : ℝ} (hβ : 0 ≤ β) (g : PeriodicSlabGround.GroundData β) :
    0 ≤ nativeRayleigh g := by
  rw [nativeRayleigh_formula hβ g]
  exact div_nonneg (mul_nonneg (mul_nonneg (div_pos (pow_pos (CubeHaarUpper.laplace_pos β hβ) _) g.value_pos).le
    (by positivity)) (integral_nonneg (fun _ => sq_nonneg _))) (weightedMass_positive β hβ).le

/-- The tempting near-one kinetic factor yields a DECAYING actual native
Rayleigh quotient for this corrected family. The exponential input norm cost
cannot be erased by transport or completion. -/
theorem nativeRayleigh_bound {β : ℝ} (hb : 16777216 ≤ β) (g : PeriodicSlabGround.GroundData β) :
    nativeRayleigh g ≤
      ((PeriodicGroundHaarScale.upperConstant / PeriodicGaugeSaturatedGround.eigenLowerConstant) /
        roughWindingMass) * Real.exp (-β) := by
  have hβ : 0 ≤ β := by linarith
  let R := PeriodicGroundHaarScale.upperConstant / PeriodicGaugeSaturatedGround.eigenLowerConstant
  have hR : 0 < R := div_pos PeriodicGroundHaarScale.upperConstant_pos
    PeriodicGaugeSaturatedGround.eigenLowerConstant_pos
  have hM : (∫ U, (PeriodicCenteredHolonomy.first U)^2 ∂boundaryHaar) ≤ 1 := by
    have h := integral_mono winding_square_integrable (integrable_const (1:ℝ)) winding_square_bound
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hn : (CubeHaarUpper.laplace β ^ 192 / g.value) * SU2WilsonConvolution.coefficient β ^ 4 *
      (∫ U, (PeriodicCenteredHolonomy.first U)^2 ∂boundaryHaar) ≤ R := by
    have hp := mul_le_mul (coefficient_power_bound β) hM
      (integral_nonneg (fun _ => sq_nonneg _)) (by norm_num : (0:ℝ) ≤ 1)
    have h := mul_le_mul (PeriodicHighActionControl.relative_normalization hb g) hp
      (mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))) hR.le
    simpa only [one_mul, mul_one, mul_assoc] using h
  rw [nativeRayleigh_formula hβ g]
  calc
    _ ≤ R / weightedMass β := div_le_div_of_nonneg_right hn (weightedMass_positive β hβ).le
    _ ≤ R / (Real.exp β * roughWindingMass) :=
      div_le_div_of_nonneg_left hR.le (mul_pos (Real.exp_pos _) roughWindingMass_positive)
        (weightedMass_lower β hβ)
    _ = _ := by
      rw [Real.exp_neg]
      field_simp [roughWindingMass_positive.ne', Real.exp_ne_zero β]
      rfl

theorem nativeRayleigh_tendsto (g : ∀ β : ℝ, PeriodicSlabGround.GroundData β) :
    Tendsto (fun β => nativeRayleigh (g β)) atTop (𝓝 0) := by
  have hu : Tendsto (fun β : ℝ =>
      ((PeriodicGroundHaarScale.upperConstant / PeriodicGaugeSaturatedGround.eigenLowerConstant) /
        roughWindingMass) * Real.exp (-β)) atTop (𝓝 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
      ((PeriodicGroundHaarScale.upperConstant / PeriodicGaugeSaturatedGround.eigenLowerConstant) / roughWindingMass)
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with β hb
    exact nativeRayleigh_nonneg hb (g β)
  · filter_upwards [eventually_ge_atTop (16777216:ℝ)] with β hb
    exact nativeRayleigh_bound hb (g β)


/-- Identification with the ACTUAL stationary Hilbert operator and ORIGINAL
input norm; neither an output completion nor a different measure is used. -/
theorem nativeRayleigh_hilbert {β : ℝ} (g : PeriodicSlabGround.GroundData β) :
    nativeRayleigh g =
      inner ℝ (PeriodicSlabL2.operator g ((nativeWinding_memLp g).toLp (nativeWinding g)))
        ((nativeWinding_memLp g).toLp (nativeWinding g)) /
          ‖(nativeWinding_memLp g).toLp (nativeWinding g)‖^2 := by
  let Z := (nativeWinding_memLp g).toLp (nativeWinding g)
  have hz : Z =ᵐ[g.stationary] nativeWinding g := (nativeWinding_memLp g).coeFn_toLp
  have hp : PeriodicSlabL2.operator g Z =ᵐ[g.stationary]
      (fun U => ∫ V, nativeWinding g V ∂g.transition U) := by
    have h := PeriodicSlabL2.operator_toLp g (nativeWinding g) (nativeWinding_memLp g)
      (nativeWinding_measurable g) _ (nativeWinding_bound g)
    change (fun U => PeriodicSlabL2.operator g
      ((nativeWinding_memLp g).toLp (nativeWinding g)) U) =ᵐ[g.stationary] _
    rw [h]
    exact (PeriodicSlabL2.transfer_memLp g (nativeWinding g)
      (nativeWinding_measurable g) _ (nativeWinding_bound g)).coeFn_toLp
  have hn : ‖Z‖^2 = ∫ U, (nativeWinding g U)^2 ∂g.stationary := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hz] with U hU
    rw [hU, Real.norm_eq_abs, sq_abs]
  have hc : inner ℝ (PeriodicSlabL2.operator g Z) Z =
      ∫ U, nativeWinding g U * (∫ V, nativeWinding g V ∂g.transition U) ∂g.stationary := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hz, hp] with U hU hP
    rw [hU, hP]
    rfl
  change nativeRayleigh g = inner ℝ (PeriodicSlabL2.operator g Z) Z / ‖Z‖^2
  rw [hc, hn]
  rfl

end OperatorDerivativeRewrite.Foundation.PeriodicWindingEndpointResponse
