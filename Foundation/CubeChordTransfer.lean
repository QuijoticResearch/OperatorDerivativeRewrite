import Foundation.CubeReducedHaar
import Foundation.CubeNativeL2Domain

/-! Exact five-chord integration formulas for the actual gauge-averaged Wilson kernel.
The temporal gauge integral remains part of the kernel. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeChordTransfer
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab CubeSlabGauge
open CubeAxialSlice CubeAxialGauge CubeHaarSplit CubeReducedHaar CubeSlabGround
attribute [local irreducible] CubeWilsonSlab.kernel boundaryHaar

/-- The specified axial section is a measurable map into the original state space. -/
theorem axial_measurable : Measurable axialState := by
  apply measurable_pi_iff.mpr
  intro e
  cases h : chordLabel e with
  | none => simpa only [axialState,h,Option.elim_none] using (measurable_const : Measurable (fun _ : Chords => (1:SU2)))
  | some i => simpa only [axialState,h,Option.elim_some] using (measurable_pi_apply i : Measurable (fun q : Chords => q i))

/-- Endpoint reduction applies to the ACTUAL gauge-averaged kernel, not its raw integrand. -/
theorem kernel_reduced (beta : ℝ) (U V : State) :
    kernel beta U V=kernel beta (axialState (reduced U)) (axialState (reduced V)) := by
  have h1 := kernel_left_invariant beta (rootedGauge U) U V
  rw [reconstruction] at h1
  have h2 := kernel_right_invariant beta (rootedGauge V) (axialState (reduced U)) V
  rw [reconstruction] at h2
  exact (h2.trans h1).symm

variable {beta : ℝ} (d : GroundData beta)

/-- Actual positive ground observables factor through the reduced chords. -/
theorem function_reduced (U : State) : d.function U=d.function (axialState (reduced U)) := by
  have h := d.invariant (rootedGauge U) U
  rw [reconstruction] at h
  exact h.symm

/-- Exact ground normalization on five independent Haar chords, with gauge volume one. -/
theorem normalizer_chords : d.normalizer=∫ q,d.function (axialState q)^2 ∂chordHaar := by
  calc
    _ = ∫ U,d.function (axialState (reduced U))^2 ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with U
      rw [function_reduced d U]
    _ = _ := integral_reduced _ ((d.measurable.comp axial_measurable).pow_const 2)

/-- The full native integrability domain for measurable reduced observables. -/
theorem native_integrable_iff (f : Chords → ℝ) (hf : Measurable f) :
    Integrable (fun U => f (reduced U)) d.stationary ↔
      Integrable (fun q => d.function (axialState q)^2*f q) chordHaar := by
  rw [CubeNativeL2Domain.integrable_iff]
  have h := reduced_preserving.integrable_comp
    (((d.measurable.comp axial_measurable).pow_const 2).mul hf).aestronglyMeasurable
  have he : (fun U => d.function U^2*f (reduced U))=
      (fun U => d.function (axialState (reduced U))^2*f (reduced U)) := by
    funext U
    rw [function_reduced d U]
  rw [he]
  exact h

/-- Exact native L2 domain for measurable reduced observables. -/
theorem native_memLp_iff (f : Chords → ℝ) (hf : Measurable f) :
    MemLp (fun U => f (reduced U)) 2 d.stationary ↔
      Integrable (fun q => d.function (axialState q)^2*f q^2) chordHaar := by
  have h := memLp_two_iff_integrable_sq (μ := d.stationary)
    (f := fun U : State => f (reduced U))
    (hf.comp reduced_measurable).aestronglyMeasurable
  exact h.trans (native_integrable_iff d (fun q => f q^2) (hf.pow_const 2))

/-- Native square-ground law, with no spatial Gibbs substitution. -/
theorem native_integral_chords (f : Chords → ℝ) (hf : Measurable f) :
    (∫ U,f (reduced U) ∂d.stationary)=
      (∫ q,d.function (axialState q)^2*f q ∂chordHaar)/d.normalizer := by
  rw [d.stationary_integral]
  congr 1
  calc
    _ = ∫ U,d.function (axialState (reduced U))^2*f (reduced U) ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with U
      rw [function_reduced d U]
    _ = _ := integral_reduced _ (((d.measurable.comp axial_measurable).pow_const 2).mul hf)

/-- The actual positive ground eigen-equation on the reduced Haar domain. -/
theorem eigen_chords (q : Chords) :
    (∫ r,kernel beta (axialState q) (axialState r)*d.function (axialState r) ∂chordHaar)=
      d.value*d.function (axialState q) := by
  have hm : Measurable (fun r : Chords =>
      kernel beta (axialState q) (axialState r)*d.function (axialState r)) :=
    (((kernel_joint_measurable beta).comp (measurable_const.prodMk axial_measurable)).mul
      (d.measurable.comp axial_measurable))
  rw [← integral_reduced _ hm]
  calc
    _ = ∫ V,kernel beta (axialState q) V*d.function V ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with V
      have hk := kernel_right_invariant beta (rootedGauge V) (axialState q) V
      rw [reconstruction] at hk
      rw [hk,← function_reduced d V]
    _ = _ := d.eigen (axialState q)

/-- Actual native transition on reduced observables. Its kernel still integrates
all temporal links. Integrability is an independent domain condition above. -/
theorem transition_chords (f : Chords → ℝ) (hf : Measurable f) (U : State) :
    (∫ V,f (reduced V) ∂d.transition U)=
      (∫ r,kernel beta (axialState (reduced U)) (axialState r)*
        (d.function (axialState r)*f r) ∂chordHaar)/
          (d.value*d.function (axialState (reduced U))) := by
  rw [d.transition_integral,function_reduced d U]
  congr 1
  calc
    _ = ∫ V,kernel beta (axialState (reduced U)) (axialState (reduced V))*
        (d.function (axialState (reduced V))*f (reduced V)) ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with V
      rw [kernel_reduced beta U V,function_reduced d V]
    _ = _ := integral_reduced _
      (((kernel_joint_measurable beta).comp
        (measurable_const.prodMk axial_measurable)).mul
          ((d.measurable.comp axial_measurable).mul hf))

end OperatorDerivativeRewrite.Foundation.CubeChordTransfer
