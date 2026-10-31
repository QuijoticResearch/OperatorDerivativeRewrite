import Foundation.SU2WilsonConvolution
import Foundation.SU2HaarSmallCap
/-! Genuine Haar small-cap convolution lower bounds for the SU(2) Wilson
kinetic weight. Inverse pairing cancels the odd trace increment uniformly in
the external group element. No ground comparison or spectral gap is asserted. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.SU2CapConvolutionLower
open QuaternionSU2Representation FourCubePinnedCoercivity SU2HaarSmallCap

private theorem exp_midpoint (x y : ℝ) : 2*Real.exp ((x+y)/2) ≤ Real.exp x+Real.exp y := by
  have hx : Real.exp (x/2)^2=Real.exp x := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hy : Real.exp (y/2)^2=Real.exp y := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hxy : Real.exp (x/2)*Real.exp (y/2)=Real.exp ((x+y)/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith [sq_nonneg (Real.exp (x/2)-Real.exp (y/2))]

theorem cap_pair_lower (β t : ℝ) (hb : 0 ≤ β) (C h : SU2) (hh : h∈cap t) :
    Real.exp (-β*(defect C+3*t^2)) ≤
      (Real.exp (-β*defect (C*h))+Real.exp (-β*defect (C*h⁻¹)))/2 := by
  have hd : defect h≤3*t^2 := hh
  have ht := SU2WilsonConvolution.trace_pair C h
  have hc := (abs_le.mp (halfTrace_bound C)).2
  have hm := mul_le_mul_of_nonneg_right hc (defect_nonneg h)
  have hs : defect (C*h)+defect (C*h⁻¹)≤2*defect C+6*t^2 := by
    unfold defect at *
    nlinarith
  have he : Real.exp (-β*(defect C+3*t^2)) ≤
      Real.exp ((-β*defect (C*h)+ -β*defect (C*h⁻¹))/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hs)]
  have hp := exp_midpoint (-β*defect (C*h)) (-β*defect (C*h⁻¹))
  linarith

private theorem inv_preserving : MeasurePreserving (fun A : SU2 => A⁻¹) law law := by
  letI : IsProbabilityMeasure law.inv := by
    change IsProbabilityMeasure (law.map (fun A : SU2 => A⁻¹))
    infer_instance
  letI : law.inv.IsHaarMeasure :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior law.inv Set.univ isCompact_univ
      (by simp) (by simp) (by simp)
  have h : law.inv=law := (law_eq_probability_haar law.inv).symm
  exact ⟨measurable_inv,h⟩

private theorem weight_integrable (β : ℝ) (hb : 0 ≤ β) (F : SU2 → SU2) (hf : Measurable F) :
    Integrable (fun h => Real.exp (-β*defect (F h))) law := by
  have hm : Measurable (fun h => defect (F h)) := by
    unfold defect
    exact measurable_const.sub (halfTrace_measurable.comp hf)
  apply Integrable.of_bound (hm.const_mul (-β) |>.exp).aestronglyMeasurable 1
  filter_upwards with h
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (defect_nonneg _))

theorem cap_integral_lower (β t : ℝ) (hb : 0 ≤ β) (C : SU2) :
    law.real (cap t)*Real.exp (-β*(defect C+3*t^2)) ≤
      ∫ h in cap t,Real.exp (-β*defect (C*h)) ∂law := by
  have hcap := cap_measurable t
  have hInv (h : SU2) : h⁻¹∈cap t ↔ h∈cap t := by
    unfold cap defect
    simp only [Set.mem_ofPred_eq,SU2WilsonConvolution.halfTrace_inv]
  have hmap := inv_preserving.integral_comp (MeasurableEquiv.inv SU2).measurableEmbedding
    ((cap t).indicator (fun h => Real.exp (-β*defect (C*h))))
  have he : (fun h : SU2 => ((cap t).indicator (fun h => Real.exp (-β*defect (C*h)))) h⁻¹)=
      (cap t).indicator (fun h => Real.exp (-β*defect (C*h⁻¹))) := by
    funext h
    by_cases hh : h∈cap t
    · rw [Set.indicator_of_mem ((hInv h).mpr hh),Set.indicator_of_mem hh]
    · rw [Set.indicator_of_notMem (mt (hInv h).mp hh),Set.indicator_of_notMem hh]
  change (∫ h,((cap t).indicator (fun h => Real.exp (-β*defect (C*h)))) h⁻¹ ∂law)=_ at hmap
  rw [he,integral_indicator hcap,integral_indicator hcap] at hmap
  have hi := weight_integrable β hb (fun h => C*h) (measurable_const_mul C)
  have hj := weight_integrable β hb (fun h => C*h⁻¹) ((measurable_const_mul C).comp measurable_inv)
  have hle := setIntegral_mono_on (integrableOn_const (C := Real.exp (-β*(defect C+3*t^2))))
    ((hi.add hj).div_const 2).integrableOn hcap (fun h hh => cap_pair_lower β t hb C h hh)
  rw [setIntegral_const,smul_eq_mul,integral_div] at hle
  change law.real (cap t)*Real.exp (-β*(defect C+3*t^2)) ≤
    (∫ h in cap t,Real.exp (-β*defect (C*h))+Real.exp (-β*defect (C*h⁻¹)) ∂law)/2 at hle
  rw [integral_add hi.integrableOn hj.integrableOn,hmap] at hle
  linarith
/-- Polynomial cap mass retained in the actual shifted Haar integral. -/
theorem cap_integral_power_lower (β t : ℝ) (hb : 0 ≤ β) (ht : 0 ≤ t) (h1 : t ≤ 1) (C : SU2) :
    (1/(4*Real.pi^2))*t^3*Real.exp (-β*(defect C+3*t^2)) ≤
      ∫ h in cap t,Real.exp (-β*defect (C*h)) ∂law :=
  (mul_le_mul_of_nonneg_right (mass_lower t ht h1) (Real.exp_pos _).le).trans
    (cap_integral_lower β t hb C)
end OperatorDerivativeRewrite.Foundation.SU2CapConvolutionLower
