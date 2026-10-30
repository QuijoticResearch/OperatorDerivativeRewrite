import Foundation.FourCubeHaarProductCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Quantitative small-cap mass for the actual SU(2) Haar law, via its verified chart. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.SU2HaarSmallCap
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open FourCubePinnedCoercivity FourCubeHemisphereCoercivity FourCubeHaarProductCoordinates

def cap (t : ℝ) : Set SU2 := {U | defect U ≤ 3*t^2}
def box (t : ℝ) : Set Triple := Icc (fun _ => -t) (fun _ => t)

theorem cap_measurable (t : ℝ) : MeasurableSet (cap t) :=
  measurableSet_le (measurable_const.sub halfTrace_measurable) measurable_const

private theorem box_squares (t : ℝ) (ht : 0 ≤ t) (y : Triple) (hy : y ∈ box t) (i : Fin 3) :
    (y i)^2 ≤ t^2 := by
  have h := pow_le_pow_left₀ (abs_nonneg (y i)) (abs_le.mpr ⟨hy.1 i,hy.2 i⟩) 2
  simpa only [sq_abs] using h

/-- A global chart bound, with no asymptotic approximation. -/
theorem chart_defect_upper (y : Triple) : defect (hemisphereChart y) ≤ chartRate y-1 := by
  have hp := radius_positive y
  have hs := radius_sq y
  have h1 : 1 ≤ radius y := by nlinarith [chartRate_ge_one y]
  have hn : 0 ≤ chartRate y-1 := sub_nonneg.mpr (chartRate_ge_one y)
  have he : defect (hemisphereChart y)=(chartRate y-1)/(radius y*(radius y+1)) := by
    rw [defect,chart_halfTrace]
    field_simp
    nlinarith
  rw [he]
  exact div_le_self hn (by nlinarith : 1 ≤ radius y*(radius y+1))

theorem box_chart_subset (t : ℝ) (ht : 0 ≤ t) : box t ⊆ hemisphereChart ⁻¹' cap t := by
  intro y hy
  have h0 := box_squares t ht y hy 0
  have h1 := box_squares t ht y hy 1
  have h2 := box_squares t ht y hy 2
  have h := chart_defect_upper y
  change defect (hemisphereChart y) ≤ 3*t^2
  unfold chartRate at h
  linarith

private theorem density_lower (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) (y : Triple) (hy : y ∈ box t) :
    1/(32*Real.pi^2) ≤ chartDensity y := by
  have h0 := box_squares t ht y hy 0
  have hy1 := box_squares t ht y hy 1
  have h2 := box_squares t ht y hy 2
  have hr : chartRate y ≤ 4 := by unfold chartRate; nlinarith
  have hs : (chartRate y)^2 ≤ 16 := by nlinarith [chartRate_positive y]
  have hd : 2*Real.pi^2*(chartRate y)^2 ≤ 32*Real.pi^2 := by nlinarith [Real.pi_pos]
  have hp := chartRate_positive y
  have hpi := Real.pi_pos
  exact one_div_le_one_div_of_le (by positivity) hd

private theorem volume_box (t : ℝ) (ht : 0 ≤ t) : (volume : Measure Triple).real (box t)=8*t^3 := by
  change ((volume : Measure Triple) (Icc (fun _ => -t) (fun _ => t))).toReal=_
  rw [Real.volume_Icc_pi_toReal (fun _ => by linarith : (fun _ : Fin 3 => -t) ≤ fun _ => t)]
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
  ring

/-- Genuine polynomial Haar mass, not a pointwise or Gaussian-model statement. -/
theorem mass_lower (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) :
    (1/(4*Real.pi^2))*t^3 ≤ law.real (cap t) := by
  have hbox : MeasurableSet (box t) := measurableSet_Icc
  have hfinite : (volume : Measure Triple) (box t) ≠ ⊤ := by
    rw [box,Real.volume_Icc_pi]
    simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hi := setIntegral_mono_on
    (integrableOn_const (μ := (volume : Measure Triple)) (s := box t)
      (C := (1/(32*Real.pi^2) : ℝ)) hfinite)
    chartDensity_integrable.integrableOn hbox (density_lower t ht h1)
  rw [setIntegral_const,smul_eq_mul,volume_box t ht] at hi
  have he : coordinateLaw.real (box t)=∫ y in box t,chartDensity y := by
    change (coordinateLaw (box t)).toReal=_
    rw [coordinateLaw_apply_integral _ hbox,ENNReal.toReal_ofReal]
    exact integral_nonneg (fun _ => chartDensity_nonneg _)
  rw [← he] at hi
  have hmass : coordinateLaw (box t) ≤ law (cap t) := by
    have h := measure_mono (box_chart_subset t ht) (μ := coordinateLaw)
    rw [← Measure.map_apply chart_measurable (cap_measurable t),chart_map_coordinateLaw] at h
    exact h.trans (Measure.restrict_apply_le _ _)
  have hr := ENNReal.toReal_mono (measure_ne_top law (cap t)) hmass
  change coordinateLaw.real (box t) ≤ law.real (cap t) at hr
  have h := hi.trans hr
  convert h using 1 <;> field_simp <;> ring

end OperatorDerivativeRewrite.Foundation.SU2HaarSmallCap
