import Foundation.CubeTemporalConfinement

/-! Actual Haar-factor upper bounds for the Wilson slab and its positive ground. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeHaarUpper
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab CubeSlabGauge CubeSlabGround
open CubeAxialSlice CubeAxialGauge CubeChordTransfer CubeReducedHaar CubeHaarSplit
open CubeTemporalRootHaar CubeTemporalConfinement FourCubePinnedCoercivity
attribute [local irreducible] CubeWilsonSlab.kernel boundaryHaar gaugeHaar defect

private theorem defect_measurable : Measurable defect := by
  unfold defect
  exact measurable_const.sub halfTrace_measurable

private theorem energy_measurable {ι : Type} [Fintype ι] :
    Measurable (fun h : ι → SU2 => ∑ i,defect (h i)) :=
  Finset.measurable_sum _ (fun i _ => defect_measurable.comp (measurable_pi_apply i))

private theorem energy_integrable {ι : Type} [Fintype ι] (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun h : ι → SU2 => Real.exp (-s*(∑ i,defect (h i)))) (Measure.pi (fun _ => law)) := by
  apply Integrable.of_bound ((measurable_const.mul energy_measurable).exp).aestronglyMeasurable 1
  filter_upwards with h
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs)
    (Finset.sum_nonneg (fun _ _ => defect_nonneg _)))

def laplace (s : ℝ) : ℝ := ∫ U,Real.exp (-s*defect U) ∂law

theorem laplace_integrable (s : ℝ) (hs : 0 ≤ s) : Integrable (fun U => Real.exp (-s*defect U)) law := by
  apply Integrable.of_bound ((measurable_const.mul defect_measurable).exp).aestronglyMeasurable 1
  filter_upwards with U
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (defect_nonneg U))

theorem laplace_pos (s : ℝ) (hs : 0 ≤ s) : 0 < laplace s := integral_exp_pos (laplace_integrable s hs)

theorem laplace_le_one (s : ℝ) (hs : 0 ≤ s) : laplace s ≤ 1 := by
  have h := integral_mono (laplace_integrable s hs) (integrable_const (1:ℝ))
    (fun U => Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (defect_nonneg U)))
  simpa only [laplace,integral_const,probReal_univ,one_smul] using h

private theorem product_integral {ι : Type} [Fintype ι] (s : ℝ) :
    (∫ h : ι → SU2,Real.exp (-s*(∑ i,defect (h i))) ∂Measure.pi (fun _ => law))=
      laplace s^(Fintype.card ι) := by
  have he : (fun h : ι → SU2 => Real.exp (-s*(∑ i,defect (h i))))=
      (fun h => ∏ i,Real.exp (-s*defect (h i))) := by
    funext h
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
  rw [he]
  simpa only [laplace] using (integral_fintype_prod_eq_pow (ι := ι) (μ := law)
    (fun U : SU2 => Real.exp (-s*defect U)))

/-- Exact seven-relative-variable Haar integral, with no pointwise root fixing. -/
theorem relative_integral (s : ℝ) :
    (∫ g,Real.exp (-s*relativeEnergy (relative g)) ∂gaugeHaar)=laplace s^7 := by
  have hm : Measurable (fun h : Relative => Real.exp (-s*relativeEnergy h)) :=
    (measurable_const.mul energy_measurable).exp
  have h := integral_map (μ := gaugeHaar) relative_preserving.measurable.aemeasurable hm.aestronglyMeasurable
  rw [relative_preserving.map_eq] at h
  rw [← h]
  exact product_integral (ι := RelativeIndex) s |>.trans (by rw [relative_count])

/-- Global actual kernel domination from the common axial tree. -/
theorem kernel_axial_upper (beta : ℝ) (hb : 0 ≤ beta) (q r : Chords) :
    kernel beta (axialState q) (axialState r) ≤
      Real.exp (-beta*spatialAction (axialState q)/2)*
      Real.exp (-beta*spatialAction (axialState r)/2)*laplace (beta/63)^7 := by
  have hi : Integrable (fun h : Relative => Real.exp (-(beta/63)*relativeEnergy h)) relativeHaar :=
    energy_integrable (beta/63) (by positivity)
  have hg := relative_preserving.integrable_comp_of_integrable hi
  have h := integral_mono (weight_integrable beta (axialState q) (axialState r))
    (hg.const_mul (Real.exp (-beta*spatialAction (axialState q)/2)*
      Real.exp (-beta*spatialAction (axialState r)/2))) (weight_bound beta hb q r)
  simp only [Function.comp_def] at h
  rw [integral_const_mul,relative_integral] at h
  rw [CubeWilsonSlab.kernel]
  exact h

theorem spatial_reduced (U : State) : spatialAction (axialState (reduced U))=spatialAction U := by
  rw [← reconstruction,spatial_action_invariant]

/-- The original boundary fields are arbitrary, not required to lie on a slice. -/
theorem kernel_upper (beta : ℝ) (hb : 0 ≤ beta) (U V : State) :
    kernel beta U V ≤ Real.exp (-beta*spatialAction U/2)*
      Real.exp (-beta*spatialAction V/2)*laplace (beta/63)^7 := by
  rw [kernel_reduced beta U V]
  simpa only [spatial_reduced] using kernel_axial_upper beta hb (reduced U) (reduced V)

private theorem spatial_integrable (beta : ℝ) (hb : 0 ≤ beta) :
    Integrable (fun U => Real.exp (-beta*spatialAction U/2)) boundaryHaar := by
  apply Integrable.of_bound ((spatial_action_measurable.const_mul (-beta)).div_const 2).exp.aestronglyMeasurable 1
  filter_upwards with U
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have h := (spatial_action_bounds U).1
  nlinarith

/-- Five actual independent reduced chords control the remaining boundary integral. -/
theorem boundary_integral_upper (beta : ℝ) (hb : 0 ≤ beta) :
    (∫ U,Real.exp (-beta*spatialAction U/2) ∂boundaryHaar) ≤ laplace (beta/8)^5 := by
  have hi : Integrable (fun q : Chords => Real.exp (-(beta/8)*chordEnergy q)) chordHaar :=
    energy_integrable (beta/8) (by positivity)
  have h := integral_mono (spatial_integrable beta hb)
    (reduced_preserving.integrable_comp_of_integrable hi) (fun U => by
      apply Real.exp_le_exp.mpr
      have hc := mul_le_mul_of_nonneg_left (coercive_mod_gauge U) hb
      nlinarith)
  have hm : Measurable (fun q : Chords => Real.exp (-(beta/8)*chordEnergy q)) :=
    (measurable_const.mul energy_measurable).exp
  simp only [Function.comp_def] at h
  rw [integral_reduced _ hm] at h
  exact h.trans_eq (product_integral (ι := Fin 5) (beta/8) |>.trans (by norm_num))

variable {beta : ℝ} (d : GroundData beta)

/-- A genuine all-coupling actual ground upper bound, reduced to ONE scalar Haar
Laplace integral. Polynomial scalar estimates are separate obligations. -/
theorem eigenvalue_upper (hb : 0 ≤ beta) :
    d.value ≤ laplace (beta/63)^7*laplace (beta/8)^5 := by
  have hf : Integrable d.function boundaryHaar := by
    apply Integrable.of_bound d.measurable.aestronglyMeasurable d.upper
    filter_upwards with U
    exact (d.bounds U).2
  let m := ∫ U,d.function U ∂boundaryHaar
  have hm : 0 < m := by
    have h := integral_mono (integrable_const d.lower) hf (fun U => (d.bounds U).1)
    simp only [integral_const,probReal_univ,one_smul] at h
    exact d.lower_pos.trans_le h
  have hp := pow_nonneg (laplace_pos (beta/63) (by positivity)).le 7
  have hrow (U : State) : d.value*d.function U ≤
      (laplace (beta/63)^7*m)*Real.exp (-beta*spatialAction U/2) := by
    have hw : Integrable (fun V => kernel beta U V*d.function V) boundaryHaar := by
      convert (d.density_integrable U).mul_const (d.value*d.function U) using 1
      funext V
      unfold GroundData.density
      exact (div_mul_cancel₀ _ (mul_pos d.value_pos (d.function_pos U)).ne').symm
    have hk (V : State) : kernel beta U V ≤ Real.exp (-beta*spatialAction U/2)*laplace (beta/63)^7 := by
      have he : Real.exp (-beta*spatialAction V/2) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have hA := (spatial_action_bounds V).1
        nlinarith
      have h := mul_le_mul_of_nonneg_left he
        (mul_nonneg (Real.exp_pos (-beta*spatialAction U/2)).le hp)
      have h' := (kernel_upper beta hb U V).trans (by convert h using 1 <;> ring)
      simpa only [mul_one] using h'
    have h := integral_mono hw (hf.const_mul (Real.exp (-beta*spatialAction U/2)*laplace (beta/63)^7))
      (fun V => mul_le_mul_of_nonneg_right (hk V) (d.function_pos V).le)
    rw [d.eigen,integral_const_mul] at h
    convert h using 1 <;> ring
  have h := integral_mono (hf.const_mul d.value)
    ((spatial_integrable beta hb).const_mul (laplace (beta/63)^7*m)) hrow
  rw [integral_const_mul,integral_const_mul] at h
  have hl : d.value ≤ laplace (beta/63)^7*(∫ U,Real.exp (-beta*spatialAction U/2) ∂boundaryHaar) := by
    apply (mul_le_mul_iff_right₀ hm).mp
    convert h using 1 <;> ring
  exact hl.trans (mul_le_mul_of_nonneg_left (boundary_integral_upper beta hb) hp)

end OperatorDerivativeRewrite.Foundation.CubeHaarUpper
