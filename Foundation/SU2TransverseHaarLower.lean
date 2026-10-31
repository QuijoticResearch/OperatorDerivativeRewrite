import Foundation.SU2TransverseHaar
/-! Positive actual Haar mass in a transverse tube with a fixed neutral
interval and two shrinking coordinates. The existing hemisphere density
proves a genuine quadratic lower mass bound, without a null-slice argument
or an assumed exact transverse distribution. -/
noncomputable section
open MeasureTheory Set
open scoped Quaternion
namespace OperatorDerivativeRewrite.Foundation.SU2TransverseHaarLower
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open FourCubeHaarProductCoordinates PeriodicLoopVariation

private def width (t : ℝ) (i : Fin 3) : ℝ := if i=0 then 1 else t
private def box (t : ℝ) : Set Triple := Icc (fun i => -width t i) (width t)
def tube (t : ℝ) : Set SU2 := {c | SU2TransverseHaar.transverse c≤2*t^2}

theorem tube_measurable (t : ℝ) : MeasurableSet (tube t) :=
  measurableSet_le SU2TransverseHaar.transverse_continuous.measurable measurable_const

private theorem coord_sq (t : ℝ) (y : Triple) (hy : y∈box t) (i : Fin 3) :
    (y i)^2≤(width t i)^2 := by
  have hh := pow_le_pow_left₀ (abs_nonneg (y i)) (abs_le.mpr ⟨hy.1 i,hy.2 i⟩) 2
  simpa only [sq_abs] using hh

private theorem density_lower (t : ℝ) (ht : 0≤t) (h1 : t≤1) (y : Triple) (hy : y∈box t) :
    1/(32*Real.pi^2)≤chartDensity y := by
  have h0 := coord_sq t y hy 0
  have hy1 := coord_sq t y hy 1
  have h2 := coord_sq t y hy 2
  norm_num [width] at h0 hy1 h2
  have h0sq : (y 0)^2≤1 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (y 0)) h0 2
    simpa only [sq_abs,one_pow] using hh
  have ht2 : t^2≤1 := by nlinarith [pow_le_pow_left₀ ht h1 2]
  have hr : chartRate y≤4 := by unfold chartRate; nlinarith
  have hs : chartRate y^2≤16 := by nlinarith [chartRate_positive y]
  have hd : 2*Real.pi^2*chartRate y^2≤32*Real.pi^2 := by nlinarith [Real.pi_pos]
  have hp := chartRate_positive y
  have hpi := Real.pi_pos
  exact one_div_le_one_div_of_le (by positivity) hd

private theorem volume_box (t : ℝ) (ht : 0≤t) : (volume : Measure Triple).real (box t)=8*t^2 := by
  have hw (i : Fin 3) : 0≤width t i := by unfold width; split_ifs <;> positivity
  change ((volume : Measure Triple) (Icc (fun i => -width t i) (width t))).toReal=_
  rw [Real.volume_Icc_pi_toReal (fun i => by have hh := hw i; linarith)]
  norm_num [width,Fin.prod_univ_three]
  ring

private theorem lift_recover (c : SU2) : lift c=recover (c : SU2TraceHessianModel.M2) := by
  obtain ⟨u,rfl⟩ := hom_surjective c
  change ((equiv.symm (equiv u) : QuaternionAngularHaar.Group) : ℍ)=recover (repr (u : ℍ))
  rw [equiv.symm_apply_apply,recover_repr]

private theorem transverse_chart (y : Triple) :
    SU2TransverseHaar.transverse (hemisphereChart y)*(radius y)^2=(y 1)^2+(y 2)^2 := by
  unfold SU2TransverseHaar.transverse
  rw [lift_recover,recover_chart]
  simp [rawPoint]
  field_simp [(radius_positive y).ne']

private theorem box_subset (t : ℝ) (y : Triple) (hy : y∈box t) : hemisphereChart y∈tube t := by
  have h1 := coord_sq t y hy 1
  have h2 := coord_sq t y hy 2
  norm_num [width] at h1 h2
  have hq := transverse_chart y
  have hr : 1≤(radius y)^2 := by
    rw [radius,Real.sq_sqrt (chartRate_positive y).le]
    unfold chartRate
    nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2)]
  have hn := SU2TransverseHaar.transverse_nonneg (hemisphereChart y)
  have hh := mul_nonneg (sub_nonneg.mpr hr) hn
  change SU2TransverseHaar.transverse (hemisphereChart y)≤2*t^2
  nlinarith

theorem tube_mass_lower (t : ℝ) (ht : 0≤t) (h1 : t≤1) :
    (1/(4*Real.pi^2))*t^2≤law.real (tube t) := by
  have hbox : MeasurableSet (box t) := measurableSet_Icc
  have hfinite : (volume : Measure Triple) (box t)≠⊤ := by
    rw [box,Real.volume_Icc_pi]
    simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hi := setIntegral_mono_on
    (integrableOn_const (μ := (volume : Measure Triple)) (s := box t) (C := (1/(32*Real.pi^2) : ℝ)) hfinite)
    chartDensity_integrable.integrableOn hbox (density_lower t ht h1)
  rw [setIntegral_const,smul_eq_mul,volume_box t ht] at hi
  have he : coordinateLaw.real (box t)=∫ y in box t,chartDensity y := by
    change (coordinateLaw (box t)).toReal=_
    rw [coordinateLaw_apply_integral _ hbox,ENNReal.toReal_ofReal]
    exact integral_nonneg (fun _ => chartDensity_nonneg _)
  rw [← he] at hi
  have hmass : coordinateLaw (box t)≤law (tube t) := by
    have hh := measure_mono (box_subset t) (μ := coordinateLaw)
    change coordinateLaw (box t)≤coordinateLaw (hemisphereChart ⁻¹' tube t) at hh
    rw [← Measure.map_apply chart_measurable (tube_measurable t),chart_map_coordinateLaw] at hh
    exact hh.trans (Measure.restrict_apply_le _ _)
  have hr := ENNReal.toReal_mono (measure_ne_top law (tube t)) hmass
  change coordinateLaw.real (box t)≤law.real (tube t) at hr
  have hh := hi.trans hr
  convert hh using 1 <;> field_simp <;> ring

end OperatorDerivativeRewrite.Foundation.SU2TransverseHaarLower
