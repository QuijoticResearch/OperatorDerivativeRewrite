import Foundation.SPDEWickModes
import Foundation.GaussianWickConditionalProjection

/-! Exact full-past prediction of countable Brownian Wick responses. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.SPDEWickBrownianPrediction
open InfiniteGaussian GaussianTimeSpaceHermite GaussianConditionalGraph GaussianWickConditionalProjection
open SPDEWickModes

theorem sourceProjection_eq_of_pairings {I : Type*} (h : I → CoefficientSpace)
    (u v : CoefficientSpace) (hv : v∈sourceSpan h)
    (hc : ∀ i, inner ℝ u (h i)=inner ℝ v (h i)) : sourceProjection h u=v := by
  let r := u-v
  have hs : Submodule.span ℝ (Set.range h)≤(innerSL ℝ r).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change inner ℝ (u-v) (h i)=0
    rw [inner_sub_left,hc i,sub_self]
  have hcl := (Submodule.span ℝ (Set.range h)).topologicalClosure_minimal hs (innerSL ℝ r).isClosed_ker
  have ho : r∈(sourceSpan h)ᗮ := by
    apply (sourceSpan h).mem_orthogonal r |>.mpr
    intro f hf
    have hi := hcl hf
    change inner ℝ r f=0 at hi
    simpa only [real_inner_comm] using hi
  exact (sourceSpan h).eq_starProjection_of_mem_orthogonal hv ho

theorem brownianDirection_inner (i j : ℕ) (s t : ℝ≥0) :
    inner ℝ (brownianDirection i s) (brownianDirection j t)=
      if i=j then (min s t : ℝ≥0) else 0 := by
  rw [brownianDirection,brownianDirection,modeDirection,modeDirection,
    LinearIsometry.inner_map_map,SPDECountableModes.modeVector_inner,GaussianTimeHilbert.timeVector_inner]
  split_ifs <;> simp

def pastDirections (t : ℝ≥0) (p : ℕ × Set.Iic t) : CoefficientSpace := brownianDirection p.1 p.2

theorem mode_source_projection (t : ℝ≥0) (ht : t≤1) (i : ℕ) :
    sourceProjection (pastDirections t) (brownianDirection i 1)=brownianDirection i t := by
  apply sourceProjection_eq_of_pairings
  · exact (Submodule.span ℝ (Set.range (pastDirections t))).le_topologicalClosure
      (Submodule.subset_span ⟨(i,⟨t,by simp⟩),rfl⟩)
  · intro p
    rw [pastDirections,brownianDirection_inner,brownianDirection_inner]
    have hp : (p.2 : ℝ≥0)≤t := p.2.property
    simp only [min_eq_right hp,min_eq_right (hp.trans ht)]

def response (t : ℝ≥0) (d : ℕ) (c : ℕ → ℝ) : GaussianL2 :=
  wickResponse (fun i => brownianDirection i t) d c

theorem response_hasSum (t : ℝ≥0) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2)) :
    HasSum (fun i => c i • (wick (brownianDirection i t) d : GaussianL2)) (response t d c) := by
  apply wickResponse_hasSum (fun i => brownianDirection i t) (modeDirections_orthogonal (fun _ => GaussianTimeHilbert.timeVector t)) d hd c
  simpa only [brownianDirection_energy,mul_assoc] using hs.mul_right ((d.factorial : ℝ)*(t : ℝ)^d)

theorem full_past_prediction (t : ℝ≥0) (ht : t≤1) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2)) :
    conditionalProjection (pastDirections t) (response 1 d c)=response t d c := by
  have hp := (conditionalProjection (pastDirections t)).hasSum (response_hasSum 1 d hd c hs)
  simp only [map_smul,conditional_wick_projection,mode_source_projection t ht] at hp
  exact hp.unique (response_hasSum t d hd c hs)

theorem response_energy_hasSum (t : ℝ≥0) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2)) :
    HasSum (fun i => (c i)^2*(d.factorial : ℝ)*(t : ℝ)^d) (‖response t d c‖^2) := by
  have hsum : Summable (fun i => (c i)^2*(d.factorial : ℝ)*(‖brownianDirection i t‖^2)^d) := by
    simpa only [brownianDirection_energy,mul_assoc] using hs.mul_right ((d.factorial : ℝ)*(t : ℝ)^d)
  have he := wickResponse_energy (fun i => brownianDirection i t)
    (modeDirections_orthogonal (fun _ => GaussianTimeHilbert.timeVector t)) d hd c hsum
  simpa only [brownianDirection_energy,response] using he
theorem full_past_prediction_energy (t : ℝ≥0) (ht : t≤1) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2)) :
    ‖conditionalProjection (pastDirections t) (response 1 d c)‖^2=
      (t : ℝ)^d*‖response 1 d c‖^2 := by
  rw [full_past_prediction t ht d hd c hs]
  have h1 := (response_energy_hasSum 1 d hd c hs).mul_left ((t : ℝ)^d)
  have he (i : ℕ) : (t : ℝ)^d*((c i)^2*(d.factorial : ℝ)*(1 : ℝ≥0)^d)=
      (c i)^2*(d.factorial : ℝ)*(t : ℝ)^d := by simp; ring
  simp_rw [he] at h1
  exact (response_energy_hasSum t d hd c hs).unique h1

theorem harmonic_square_prediction_energy (t : ℝ≥0) (ht : t≤1) :
    ‖conditionalProjection (pastDirections t) (response 1 2 harmonicCoefficient)‖^2=
      (t : ℝ)^2*‖response 1 2 harmonicCoefficient‖^2 :=
  full_past_prediction_energy t ht 2 (by norm_num) harmonicCoefficient harmonic_square_summable

end OperatorDerivativeRewrite.Foundation.SPDEWickBrownianPrediction



