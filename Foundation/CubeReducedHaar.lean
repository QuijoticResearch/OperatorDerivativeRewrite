import Foundation.CubeHaarSplit

/-! Exact Haar law of the reduced chords, with the original tree variables retained. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeReducedHaar
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab CubeAxialSlice CubeAxialGauge CubeHaarSplit

private theorem rooted_measurable (v : SpatialVertex) :
    Measurable (fun U : State => rootedGauge U v) := by
  unfold rootedGauge
  split_ifs <;> fun_prop

theorem reduced_measurable : Measurable reduced := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((rooted_measurable (chordEdge i).val.1).mul (measurable_pi_apply (chordEdge i))).mul
    (rooted_measurable (shift (chordEdge i).val.1 (chordEdge i).val.2)).inv

private def frame (t : TreeState) : Gauge := rootedGauge (rawState t 1)

private theorem conditional_formula (t : TreeState) (c : RawChords) (i : Fin 5) :
    reduced (rawState t c) i=frame t (chordEdge i).val.1*readChords c i*
      (frame t (shift (chordEdge i).val.1 (chordEdge i).val.2))⁻¹ := by
  unfold reduced gaugeAction frame
  rw [rooted_tree_only t c 1,rooted_tree_only t c 1,rawState_chord]

/-- Conditioning on the original tree, all five reduced chords remain independent Haar. -/
theorem conditional_preserving (t : TreeState) :
    MeasurePreserving (fun c : RawChords => reduced (rawState t c)) rawChordHaar chordHaar := by
  have h : MeasurePreserving
      (fun q : Chords => fun i => frame t (chordEdge i).val.1*q i*
        (frame t (shift (chordEdge i).val.1 (chordEdge i).val.2))⁻¹) chordHaar chordHaar := by
    unfold chordHaar
    apply measurePreserving_pi (fun _ : Fin 5 => law) (fun _ : Fin 5 => law)
      (f := fun i x => frame t (chordEdge i).val.1*x*
        (frame t (shift (chordEdge i).val.1 (chordEdge i).val.2))⁻¹)
    intro i
    exact (measurePreserving_mul_right law
      ((frame t (shift (chordEdge i).val.1 (chordEdge i).val.2))⁻¹)).comp
      (measurePreserving_mul_left law (frame t (chordEdge i).val.1))
  convert h.comp readChords_preserving using 1
  funext c i
  exact conditional_formula t c i

/-- The actual joint pushforward is the product of original-tree Haar and five-chord Haar.
No field-dependent gauge transformation is assumed to preserve the original measure. -/
theorem joint_preserving :
    MeasurePreserving (fun U : State => ((split U).1,reduced U)) boundaryHaar
      (treeHaar.prod chordHaar) := by
  have hm : Measurable (Function.uncurry (fun t c => reduced (rawState t c))) :=
    reduced_measurable.comp split.symm.measurable
  have h := (MeasurePreserving.id treeHaar).skew_product hm
    (ae_of_all treeHaar (fun t => (conditional_preserving t).map_eq))
  convert h.comp split_preserving using 1
  funext U
  change ((split U).1,reduced U)=((split U).1,reduced (split.symm (split U)))
  rw [MeasurableEquiv.symm_apply_apply]

/-- Exact marginal Haar law of the five actual reduced coordinates. -/
theorem reduced_preserving : MeasurePreserving reduced boundaryHaar chordHaar :=
  (measurePreserving_snd (μ := treeHaar) (ν := chordHaar)).comp joint_preserving

/-- Change of variables for arbitrary measurable real chord observables, including
integrable unbounded observables; Bochner integrals retain their usual total convention. -/
theorem integral_reduced (f : Chords → ℝ) (hf : Measurable f) :
    (∫ U,f (reduced U) ∂boundaryHaar)=∫ q,f q ∂chordHaar := by
  have h := integral_map reduced_preserving.measurable.aemeasurable
    (μ := boundaryHaar) (f := f)
  rw [reduced_preserving.map_eq] at h
  exact (h hf.aestronglyMeasurable).symm

end OperatorDerivativeRewrite.Foundation.CubeReducedHaar
