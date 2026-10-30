import Foundation.CubeHaarUpper
import Foundation.FourCubeHaarLaplaceDensity

/-! Quantitative actual SU(2) Haar Laplace upper bound, with a genuine chart/exterior split. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.SU2HaarLaplaceUpper
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open FourCubePinnedCoercivity FourCubeHemisphereCoercivity FourCubeHaarProductCoordinates
open FourCubeHaarLaplaceDensity CubeHaarUpper
attribute [local irreducible] defect

def localCut : Set SU2 := {U | defect U < 1/4}

private theorem defect_measurable : Measurable defect := by
  unfold defect
  exact measurable_const.sub halfTrace_measurable

theorem localCut_measurable : MeasurableSet localCut :=
  measurableSet_lt defect_measurable measurable_const

theorem localCut_subset : localCut ⊆ hemisphere := by
  intro U hU
  change defect U < 1/4 at hU
  unfold defect at hU
  change 0 < halfTrace U
  linarith

def gaussianMass (a : ℝ) : ℝ := ∫ y : Triple,Real.exp (-a*(chartRate y-1)/4)

theorem gaussian_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (fun y : Triple => Real.exp (-a*(chartRate y-1)/4)) := by
  have hh := Integrable.fintype_prod (fun _ : Fin 3 =>
    integrable_exp_neg_mul_sq (b := a/4) (by positivity))
  rw [volume_pi]
  convert hh using 1
  funext y
  rw [← Real.exp_sum]
  congr 1
  simp [chartRate,Fin.sum_univ_three]
  ring

theorem gaussianMass_pos (a : ℝ) (ha : 0 < a) : 0 < gaussianMass a :=
  integral_exp_pos (gaussian_integrable a ha)

private theorem triple_rescale (f : Triple → ℝ) (t : ℝ) (ht : 0 < t) :
    (∫ y : Triple,f y)=t^3*(∫ y : Triple,f (t • y)) := by
  have hh := Measure.integral_comp_smul (volume : Measure Triple) f t
  rw [show Module.finrank ℝ Triple=3 by exact Module.finrank_fin_fun ℝ,
    smul_eq_mul,abs_inv,abs_pow,abs_of_pos ht] at hh
  rw [hh]
  field_simp [ht.ne']

theorem gaussian_rescale (a t : ℝ) (ht : 0 < t) :
    gaussianMass (a/t^2)=t^3*gaussianMass a := by
  unfold gaussianMass
  rw [triple_rescale _ t ht]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [chartRate_smul]
  congr 1
  field_simp [ht.ne'] <;> ring

/-- Exact local Bochner integral transported by the actual restricted-Haar chart. -/
theorem local_integral (s : ℝ) :
    (∫ U in localCut,Real.exp (-s*defect U) ∂law)=
      ∫ y : Triple,chartDensity y*
        localCut.indicator (fun U => Real.exp (-s*defect U)) (hemisphereChart y) := by
  classical
  have hm : Measurable (localCut.indicator (fun U => Real.exp (-s*defect U))) :=
    ((measurable_const.mul defect_measurable).exp).indicator localCut_measurable
  have h := integral_map (μ := coordinateLaw) chart_measurable.aemeasurable hm.aestronglyMeasurable
  rw [chart_map_coordinateLaw,integral_indicator localCut_measurable,
    Measure.restrict_restrict_of_subset localCut_subset] at h
  rw [coordinateLaw,integral_withDensity_eq_integral_toReal_smul
    chartDensity_measurable.ennreal_ofReal (ae_of_all volume (fun _ => ENNReal.ofReal_lt_top))] at h
  simpa only [ENNReal.toReal_ofReal (chartDensity_nonneg _),smul_eq_mul] using h

private theorem local_weight_nonnegative (s : ℝ) (y : Triple) :
    0 ≤ chartDensity y*localCut.indicator (fun U => Real.exp (-s*defect U)) (hemisphereChart y) := by
  exact mul_nonneg (chartDensity_nonneg y) (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)

/-- The Gaussian domination is used only on the verified small-defect cutoff. -/
theorem local_weight_bound (s : ℝ) (hs : 0 ≤ s) (y : Triple) :
    chartDensity y*localCut.indicator (fun U => Real.exp (-s*defect U)) (hemisphereChart y) ≤
      chartDensity 0*Real.exp (-s*(chartRate y-1)/4) := by
  classical
  by_cases hy : hemisphereChart y ∈ localCut
  · rw [Set.indicator_of_mem hy]
    have hr := small_defect_chartRate (hemisphereChart y) hy
    rw [coordinates_chart] at hr
    have hd := mul_le_mul_of_nonneg_left (local_defect_lower y hr) hs
    have he : Real.exp (-s*defect (hemisphereChart y)) ≤ Real.exp (-s*(chartRate y-1)/4) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul (chartDensity_le_zero y) he (Real.exp_pos _).le (chartDensity_nonneg _)
  · rw [Set.indicator_of_notMem hy,mul_zero]
    exact mul_nonneg (chartDensity_nonneg _) (Real.exp_pos _).le

theorem local_integral_upper (s : ℝ) (hs : 0 < s) :
    (∫ U in localCut,Real.exp (-s*defect U) ∂law) ≤ chartDensity 0*gaussianMass s := by
  classical
  have hm : Measurable (fun y : Triple => chartDensity y*
      localCut.indicator (fun U => Real.exp (-s*defect U)) (hemisphereChart y)) :=
    chartDensity_measurable.mul ((((measurable_const.mul defect_measurable).exp).indicator
      localCut_measurable).comp chart_measurable)
  have hi := ((gaussian_integrable s hs).const_mul (chartDensity 0)).mono' hm.aestronglyMeasurable
    (ae_of_all volume (fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (local_weight_nonnegative s y)]
      exact local_weight_bound s hs.le y))
  have h := integral_mono hi ((gaussian_integrable s hs).const_mul (chartDensity 0))
    (local_weight_bound s hs.le)
  rw [integral_const_mul] at h
  rw [local_integral]
  exact h

/-- Actual Haar probability outside the local cutoff controls its entire contribution. -/
theorem exterior_integral_upper (s : ℝ) (hs : 0 ≤ s) :
    (∫ U in localCutᶜ,Real.exp (-s*defect U) ∂law) ≤ Real.exp (-s/4) := by
  have h := setIntegral_mono_on (laplace_integrable s hs).integrableOn
    (integrable_const (Real.exp (-s/4))).integrableOn localCut_measurable.compl
    (fun U hU => by
      have hd : 1/4 ≤ defect U := le_of_not_gt hU
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hd hs])
  have hc := setIntegral_le_integral (s := localCutᶜ) (integrable_const (Real.exp (-s/4)))
    (ae_of_all law (fun _ => (Real.exp_pos _).le))
  have h' := h.trans hc
  simpa only [integral_const,probReal_univ,one_smul] using h'

theorem laplace_split_upper (s : ℝ) (hs : 0 < s) :
    laplace s ≤ chartDensity 0*gaussianMass s+Real.exp (-s/4) := by
  have he := integral_add_compl localCut_measurable (laplace_integrable s hs.le)
  unfold laplace
  rw [← he]
  exact add_le_add (local_integral_upper s hs) (exterior_integral_upper s hs.le)

/-- Polynomially bounded exterior, with a nonsharp elementary constant. -/
theorem exterior_scaled_upper (a t : ℝ) (ha : 0 < a) (ht : 0 < t) (h1 : t ≤ 1) :
    Real.exp (-(a/t^2)/4) ≤ (64/a^2)*t^3 := by
  let x := a/(4*t^2)
  have hx : 0 < x := by dsimp [x]; positivity
  have he := Real.add_one_le_exp (x/2)
  have hs : x^2/4 ≤ Real.exp x := by
    have hh : Real.exp (x/2)^2=Real.exp x := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    nlinarith [Real.exp_pos (x/2)]
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-x)).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hm
  have hb : Real.exp (-x) ≤ 4/x^2 := (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith)
  have heq : 4/x^2=(64/a^2)*t^4 := by dsimp [x]; field_simp [ha.ne',ht.ne'] <;> ring
  have ht4 : t^4 ≤ t^3 := by nlinarith [pow_nonneg ht.le 3,mul_le_mul_of_nonneg_left h1 (pow_nonneg ht.le 3)]
  have h := hb.trans (heq.trans_le (mul_le_mul_of_nonneg_left ht4 (by positivity : 0 ≤ 64/a^2)))
  convert h using 1 <;> dsimp [x] <;> congr 1 <;> field_simp <;> ring

def upperConstant (a : ℝ) : ℝ := chartDensity 0*gaussianMass a+64/a^2

theorem upperConstant_pos (a : ℝ) (ha : 0 < a) : 0 < upperConstant a := by
  unfold upperConstant
  have hg := gaussianMass_pos a ha
  have hd := chartDensity_positive (0:Triple)
  positivity

/-- Quantitative actual SU(2) Haar bound, with every chart and exterior obligation proved. -/
theorem laplace_scaled_upper (a t : ℝ) (ha : 0 < a) (ht : 0 < t) (h1 : t ≤ 1) :
    laplace (a/t^2) ≤ upperConstant a*t^3 := by
  have h := laplace_split_upper (a/t^2) (by positivity)
  rw [gaussian_rescale a t ht] at h
  have he := exterior_scaled_upper a t ha ht h1
  have h' := h.trans (add_le_add (le_refl (chartDensity 0*(t^3*gaussianMass a))) he)
  convert h' using 1 <;> unfold upperConstant <;> ring

end OperatorDerivativeRewrite.Foundation.SU2HaarLaplaceUpper
