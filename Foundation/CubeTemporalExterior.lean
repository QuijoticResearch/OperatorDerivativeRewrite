import Foundation.CubeMatchedGround

/-! Negligible nonlocal relative-temporal contribution to the actual Wilson kernel.
The cutoff is taken AFTER common axial reduction; the free temporal root is integrated.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CubeTemporalExterior
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab CubeSlabGauge
open CubeAxialSlice CubeAxialGauge CubeChordTransfer CubeTemporalRootHaar CubeTemporalConfinement
open FourCubePinnedCoercivity CubeHaarUpper SU2HaarLaplaceUpper
attribute [local irreducible] CubeWilsonSlab.kernel gaugeHaar defect

def localRegion : Set Gauge := {g | ∀ v : RelativeIndex, relative g v ∈ localCut}

theorem localRegion_measurable : MeasurableSet localRegion := by
  have h (v : RelativeIndex) := localCut_measurable.preimage
    ((measurable_pi_apply v).comp relative_measurable)
  simpa only [localRegion, Set.ofPred_forall, Set.preimage, Function.comp_def] using MeasurableSet.iInter h


/-- The cutoff restricts only the seven relatives, never the global Haar root. -/
theorem assemble_mem (c : SU2) (h : Relative) :
    assemble c h ∈ localRegion ↔ ∀ v, h v ∈ localCut := by
  have he (v : RelativeIndex) : relative (assemble c h) v=h v := by
    simp [relative,assemble_root,assemble,anchored,v.property,mul_assoc]
  simp only [localRegion,Set.mem_setOf_eq,he]

/-- One nonlocal relative link forces a fixed energy cost, independently of the root. -/
theorem exterior_energy (g : Gauge) (hg : g ∉ localRegion) :
    1/4 ≤ relativeEnergy (relative g) := by
  classical
  change ¬ (∀ v : RelativeIndex, relative g v ∈ localCut) at hg
  obtain ⟨v,hv⟩ := not_forall.mp hg
  have hd : 1/4 ≤ defect (relative g v) := le_of_not_gt hv
  exact hd.trans (Finset.single_le_sum (fun i _ => defect_nonneg (relative g i))
    (Finset.mem_univ v))

private theorem envelope_integrable (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun g => Real.exp (-s*relativeEnergy (relative g))) gaugeHaar := by
  have hm : Measurable (fun g => relativeEnergy (relative g)) := by
    unfold relativeEnergy
    apply Finset.measurable_sum
    intro v _
    unfold defect
    exact (measurable_const.sub halfTrace_measurable).comp
      ((measurable_pi_apply v).comp relative_measurable)
  apply Integrable.of_bound ((measurable_const.mul hm).exp).aestronglyMeasurable 1
  filter_upwards with g
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs)
    (relativeEnergy_nonnegative _))

/-- Split the confinement exponent, keeping all seven integrable Haar factors. -/
theorem exterior_weight (beta : ℝ) (hb : 0 ≤ beta) (q r : Chords)
    (g : Gauge) (hg : g ∉ localRegion) :
    weight beta (axialState q) (axialState r) g ≤
      (Real.exp (-beta*spatialAction (axialState q)/2)*
       Real.exp (-beta*spatialAction (axialState r)/2)*Real.exp (-beta/504))*
        Real.exp (-(beta/126)*relativeEnergy (relative g)) := by
  have h := weight_bound beta hb q r g
  have he : Real.exp (-(beta/63)*relativeEnergy (relative g)) ≤
      Real.exp (-beta/504)*Real.exp (-(beta/126)*relativeEnergy (relative g)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (exterior_energy g hg) hb
    nlinarith
  exact h.trans (by
    convert mul_le_mul_of_nonneg_left he
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) using 1 <;> ring)

/-- Actual integrated remainder, defined through canonical reduced boundaries.
This does not apply the axial confinement inequality to arbitrary raw representatives. -/
def exterior (beta : ℝ) (U V : State) : ℝ :=
  ∫ g in localRegionᶜ,weight beta (axialState (reduced U)) (axialState (reduced V)) g ∂gaugeHaar

def interior (beta : ℝ) (U V : State) : ℝ :=
  ∫ g in localRegion,weight beta (axialState (reduced U)) (axialState (reduced V)) g ∂gaugeHaar

theorem kernel_split (beta : ℝ) (U V : State) :
    kernel beta U V=interior beta U V+exterior beta U V := by
  rw [kernel_reduced beta U V,CubeWilsonSlab.kernel]
  exact (integral_add_compl localRegion_measurable
    (weight_integrable beta (axialState (reduced U)) (axialState (reduced V)))).symm

theorem exterior_nonnegative (beta : ℝ) (U V : State) : 0 ≤ exterior beta U V :=
  integral_nonneg (fun _ => (Real.exp_pos _).le)

/-- Uniform actual-kernel exterior estimate; all boundary half-weights survive. -/
theorem exterior_upper (beta : ℝ) (hb : 0 ≤ beta) (U V : State) :
    exterior beta U V ≤
      Real.exp (-beta*spatialAction U/2)*Real.exp (-beta*spatialAction V/2)*
        Real.exp (-beta/504)*laplace (beta/126)^7 := by
  let C := Real.exp (-beta*spatialAction (axialState (reduced U))/2)*
    Real.exp (-beta*spatialAction (axialState (reduced V))/2)*Real.exp (-beta/504)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi := (envelope_integrable (beta/126) (by positivity)).const_mul C
  have h := setIntegral_mono_on
    (weight_integrable beta (axialState (reduced U)) (axialState (reduced V))).integrableOn
    hi.integrableOn localRegion_measurable.compl
    (fun g hg => exterior_weight beta hb _ _ g hg)
  have h' := setIntegral_le_integral (s := localRegionᶜ) hi
    (ae_of_all gaugeHaar (fun _ => mul_nonneg hC (Real.exp_pos _).le))
  have hh := h.trans h'
  rw [integral_const_mul,relative_integral] at hh
  simpa only [exterior,C,spatial_reduced] using hh

def remainderConstant : ℝ := upperConstant (1/126)^7

theorem remainderConstant_pos : 0 < remainderConstant :=
  pow_pos (upperConstant_pos (1/126) (by norm_num)) 7

/-- The t^21 normalization does not amplify the discarded temporal region. -/
theorem scaled_exterior_upper (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (U V : State) :
    exterior (1/t^2) U V/t^21 ≤
      Real.exp (-(1/t^2)*spatialAction U/2)*Real.exp (-(1/t^2)*spatialAction V/2)*
        remainderConstant*Real.exp (-(1/t^2)/504) := by
  have hp := pow_le_pow_left₀ (laplace_pos ((1/t^2)/126) (by positivity)).le
    (show laplace ((1/t^2)/126) ≤ upperConstant (1/126)*t^3 by
      rw [show (1/t^2)/126=(1/126)/t^2 by ring]
      exact laplace_scaled_upper (1/126) t (by norm_num) ht h1) 7
  have h := (exterior_upper (1/t^2) (by positivity) U V).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))
  apply (div_le_iff₀ (pow_pos ht 21)).mpr
  convert h using 1 <;> unfold remainderConstant <;> ring

/-- An explicit boundary-independent vanishing modulus for arbitrary moving boundaries. -/
theorem scaled_exterior_polynomial (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (U V : State) :
    exterior (1/t^2) U V/t^21 ≤ (remainderConstant*(64/(1/126 : ℝ)^2))*t^3 := by
  have hw (W : State) : Real.exp (-(1/t^2)*spatialAction W/2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hh := (spatial_action_bounds W).1
    have hb : 0 ≤ 1/t^2 := by positivity
    nlinarith
  have hc : 0 ≤ remainderConstant := remainderConstant_pos.le
  have he : Real.exp (-(1/t^2)/504) ≤ (64/(1/126 : ℝ)^2)*t^3 := by
    convert exterior_scaled_upper (1/126) t (by norm_num) ht h1 using 1 <;> congr 1 <;> ring
  have h := scaled_exterior_upper t ht h1 U V
  have hb := mul_le_mul (hw U) (hw V) (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 1)
  have hh := mul_le_mul_of_nonneg_right hb (mul_nonneg hc (Real.exp_pos (-(1/t^2)/504)).le)
  have hh' : exterior (1/t^2) U V/t^21 ≤ remainderConstant*Real.exp (-(1/t^2)/504) :=
    h.trans (by convert hh using 1 <;> ring)
  exact hh'.trans (by convert mul_le_mul_of_nonneg_left he hc using 1 <;> ring)


/-- Uniform vanishing for arbitrary boundary families, with no boundedness assumption. -/
theorem scaled_exterior_tendsto_zero (U V : ℝ → State) :
    Tendsto (fun t : ℝ => exterior (1/t^2) (U t) (V t)/t^21)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : Continuous (fun t : ℝ => (remainderConstant*(64/(1/126 : ℝ)^2))*t^3) :=
    continuous_const.mul (continuous_id.pow 3)
  have hl : Tendsto (fun t : ℝ => (remainderConstant*(64/(1/126 : ℝ)^2))*t^3)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (3 : ℕ) ≠ 0),mul_zero] using
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hn : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ exterior (1/t^2) (U t) (V t)/t^21 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact div_nonneg (exterior_nonnegative _ _ _) (pow_nonneg (le_of_lt ht) 21)
  apply squeeze_zero' hn ?_ hl
  have hle : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ≤ 1 :=
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hle] with t ht ht1
  exact scaled_exterior_polynomial t ht ht1 (U t) (V t)

/-- The actual kernel and its local relative-Haar integral have the same scaled limit,
if either limit exists. No value of that local limit is assumed. -/
theorem scaled_kernel_error_tendsto_zero (U V : ℝ → State) :
    Tendsto (fun t : ℝ => (kernel (1/t^2) (U t) (V t)-interior (1/t^2) (U t) (V t))/t^21)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa only [kernel_split,add_sub_cancel_left] using scaled_exterior_tendsto_zero U V

end OperatorDerivativeRewrite.Foundation.CubeTemporalExterior
