import Foundation.PeriodicRootHaarControl
import Foundation.SU2HaarLaplaceUpper
/-! Quantitative integration transverse to a common-axis root centralizer,
for the actual normalized SU(2) Haar law. Four Haar-translated hemisphere
patches and two Gaussian coordinates give an explicit inverse-parameter
upper bound. No exact transverse-pair law or stationary spectrum is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped Quaternion Topology
namespace OperatorDerivativeRewrite.Foundation.SU2TransverseHaar
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart PeriodicLoopVariation
open FourCubeHaarProductCoordinates

private theorem lift_mul (A B : SU2) : lift (A*B)=lift A*lift B :=
  congrArg (fun u : QuaternionAngularHaar.Group => (u : ℍ)) (equiv.symm.map_mul A B)
private theorem lift_hom (c : QuaternionAngularHaar.Group) : lift (hom c)=(c : ℍ) := by
  change ((equiv.symm (equiv c) : QuaternionAngularHaar.Group) : ℍ)=_
  rw [equiv.symm_apply_apply]
private theorem lift_recover (c : SU2) : lift c=recover (c : SU2TraceHessianModel.M2) := by
  obtain ⟨u,rfl⟩ := hom_surjective c
  rw [lift_hom]
  exact (recover_repr _).symm
private theorem lift_continuous : Continuous lift :=
  continuous_subtype_val.comp homeomorph.symm.continuous

def transverse (c : SU2) : ℝ := (lift c).imJ^2+(lift c).imK^2

theorem transverse_nonneg (c : SU2) : 0≤transverse c := by unfold transverse; positivity

theorem transverse_continuous : Continuous transverse :=
  ((Quaternion.continuous_imJ.comp lift_continuous).pow 2).add
    ((Quaternion.continuous_imK.comp lift_continuous).pow 2)

private theorem unit_coordinates (c : SU2) : (lift c).re^2+(lift c).imI^2+transverse c=1 := by
  have hn : ‖lift c‖=1 := CStarRing.norm_coe_unitary _
  have h : Quaternion.normSq (lift c)=1 := by rw [Quaternion.normSq_eq_norm_mul_self,hn,one_mul]
  norm_num [Quaternion.normSq_def'] at h
  unfold transverse
  linarith

private def negative : SU2 := SU2JointPlaquetteCubic.axis 0 Real.pi
private def quarter : SU2 := SU2JointPlaquetteCubic.axis 0 (Real.pi/2)
private theorem lift_negative : lift negative=⟨-1,0,0,0⟩ := by
  unfold negative SU2JointPlaquetteCubic.axis
  rw [lift_hom]
  norm_num [SU2JointPlaquetteCubic.axisRaw]
private theorem lift_quarter : lift quarter=⟨0,1,0,0⟩ := by
  unfold quarter SU2JointPlaquetteCubic.axis
  rw [lift_hom]
  norm_num [SU2JointPlaquetteCubic.axisRaw]
private theorem negative_re (c : SU2) : (lift (negative*c)).re= -(lift c).re := by
  rw [lift_mul,lift_negative]
  simp [Quaternion.re_mul]
private theorem quarter_re (c : SU2) : (lift (quarter*c)).re= -(lift c).imI := by
  rw [lift_mul,lift_quarter]
  simp [Quaternion.re_mul]
private theorem negative_transverse (c : SU2) : transverse (negative*c)=transverse c := by
  unfold transverse
  rw [lift_mul,lift_negative]
  simp [Quaternion.imJ_mul,Quaternion.imK_mul]
private theorem quarter_transverse (c : SU2) : transverse (quarter*c)=transverse c := by
  unfold transverse
  rw [lift_mul,lift_quarter]
  simp [Quaternion.imJ_mul,Quaternion.imK_mul]
  ring

private def patch : Set SU2 := {c | (1 : ℝ)/2≤(lift c).re}
private theorem patch_measurable : MeasurableSet patch :=
  measurableSet_le measurable_const (Quaternion.continuous_re.comp lift_continuous).measurable
private theorem patch_subset : patch ⊆ hemisphere := by
  intro c hc
  change 0<halfTrace c
  rw [halfTrace_recover,← lift_recover]
  exact lt_of_lt_of_le (by norm_num) hc

def gaussian (s : ℝ) (c : SU2) : ℝ := Real.exp (-s*transverse c)
def mass (s : ℝ) : ℝ := ∫ c,gaussian s c ∂law
private def patchWeight (s : ℝ) : SU2 → ℝ := patch.indicator (gaussian s)

theorem gaussian_integrable (s : ℝ) (hs : 0≤s) : Integrable (gaussian s) law := by
  apply Integrable.of_bound ((measurable_const.mul transverse_continuous.measurable).exp).aestronglyMeasurable 1
  filter_upwards [] with c
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  change Real.exp (-s*transverse c)≤1
  exact Real.exp_le_one_iff.mpr (by nlinarith [transverse_nonneg c])

private theorem patchWeight_integrable (s : ℝ) (hs : 0≤s) : Integrable (patchWeight s) law :=
  (gaussian_integrable s hs).indicator patch_measurable
private theorem patchWeight_nonneg (s : ℝ) (c : SU2) : 0≤patchWeight s c :=
  Set.indicator_nonneg (fun c _ => (Real.exp_pos (-s*transverse c)).le) c

private theorem four_cover (c : SU2) (hc : transverse c≤1/2) :
    c∈patch ∨ negative*c∈patch ∨ quarter*c∈patch ∨ negative*(quarter*c)∈patch := by
  simp only [patch,Set.mem_setOf_eq,negative_re,quarter_re]
  by_contra hh
  push_neg at hh
  obtain ⟨h0,h1,h2,h3⟩ := hh
  have hr : 0<((1 : ℝ)/2-(lift c).re)*(1/2+(lift c).re) := mul_pos (by linarith) (by linarith)
  have hi : 0<((1 : ℝ)/2-(lift c).imI)*(1/2+(lift c).imI) := mul_pos (by linarith) (by linarith)
  nlinarith [unit_coordinates c]

private theorem gaussian_four_bound (s : ℝ) (hs : 0≤s) (c : SU2) :
    gaussian s c≤patchWeight s c+patchWeight s (negative*c)+patchWeight s (quarter*c)+
      patchWeight s (negative*(quarter*c))+Real.exp (-s/2) := by
  have h0 := patchWeight_nonneg s c
  have h1 := patchWeight_nonneg s (negative*c)
  have h2 := patchWeight_nonneg s (quarter*c)
  have h3 := patchWeight_nonneg s (negative*(quarter*c))
  have he := (Real.exp_pos (-s/2)).le
  by_cases hc : transverse c≤1/2
  · rcases four_cover c hc with hc|hc|hc|hc
    · have hh : patchWeight s c=gaussian s c := Set.indicator_of_mem hc _
      linarith
    · have hh : patchWeight s (negative*c)=gaussian s c := by
        rw [patchWeight,Set.indicator_of_mem hc]
        simp only [gaussian,negative_transverse]
      linarith
    · have hh : patchWeight s (quarter*c)=gaussian s c := by
        rw [patchWeight,Set.indicator_of_mem hc]
        simp only [gaussian,quarter_transverse]
      linarith
    · have hh : patchWeight s (negative*(quarter*c))=gaussian s c := by
        rw [patchWeight,Set.indicator_of_mem hc]
        simp only [gaussian,negative_transverse,quarter_transverse]
      linarith
  · have hh : gaussian s c≤Real.exp (-s/2) := Real.exp_le_exp.mpr (by nlinarith)
    linarith

private theorem integral_patch_translate (s : ℝ) (a : SU2) :
    (∫ c,patchWeight s (a*c) ∂law)=∫ c,patchWeight s c ∂law :=
  (measurePreserving_mul_left law a).integral_comp (MeasurableEquiv.mulLeft a).measurableEmbedding _

private theorem mass_four_upper (s : ℝ) (hs : 0≤s) :
    mass s≤4*(∫ c,patchWeight s c ∂law)+Real.exp (-s/2) := by
  have hi := patchWeight_integrable s hs
  have hi1 := (measurePreserving_mul_left law negative).integrable_comp_of_integrable hi
  have hi2 := (measurePreserving_mul_left law quarter).integrable_comp_of_integrable hi
  have hi3 := (measurePreserving_mul_left law quarter).integrable_comp_of_integrable hi1
  have hh := integral_mono (gaussian_integrable s hs) ((((hi.add hi1).add hi2).add hi3).add (integrable_const _))
    (gaussian_four_bound s hs)
  simp only [Pi.add_apply,Function.comp_apply] at hh
  have he0 := integral_add (((hi.add hi1).add hi2).add hi3) (integrable_const (Real.exp (-s/2)))
  have he1 := integral_add ((hi.add hi1).add hi2) hi3
  have he2 := integral_add (hi.add hi1) hi2
  have he3 := integral_add hi hi1
  simp only [Pi.add_apply,Function.comp_apply] at he0 he1 he2 he3
  rw [he0,he1,he2,he3] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  rw [integral_patch_translate,integral_patch_translate] at hh
  have hlast : (∫ c,patchWeight s (negative*(quarter*c)) ∂law)=∫ c,patchWeight s c ∂law := by
    simp_rw [← mul_assoc]
    exact integral_patch_translate s (negative*quarter)
  rw [hlast] at hh
  unfold mass
  linarith


private def stripFactor (s : ℝ) (i : Fin 3) (x : ℝ) : ℝ :=
  if i=0 then (Icc (-2 : ℝ) 2).indicator (fun _ => 1) x else Real.exp (-(s/4)*x^2)
private def strip (s : ℝ) (y : Triple) : ℝ := ∏ i : Fin 3,stripFactor s i (y i)

private theorem strip_formula (s : ℝ) (y : Triple) :
    strip s y=(Icc (-2 : ℝ) 2).indicator (fun _ => 1) (y 0)*Real.exp (-s*((y 1)^2+(y 2)^2)/4) := by
  norm_num [strip,stripFactor,Fin.prod_univ_three]
  rw [mul_assoc,← Real.exp_add]
  congr 1
  congr 1
  ring

private theorem stripFactor_integrable (s : ℝ) (hs : 0<s) (i : Fin 3) : Integrable (stripFactor s i) := by
  change Integrable (fun x : ℝ => if i=0 then (Icc (-2 : ℝ) 2).indicator (fun _ => 1) x else Real.exp (-(s/4)*x^2))
  by_cases hi : i=0
  · simp only [if_pos hi]
    exact (integrableOn_const (μ := (volume : Measure ℝ)) (s := Icc (-2 : ℝ) 2) (C := (1 : ℝ)) (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  · simp only [if_neg hi]
    exact integrable_exp_neg_mul_sq (b := s/4) (by positivity)

private theorem strip_integrable (s : ℝ) (hs : 0<s) : Integrable (strip s) := by
  rw [show strip s=(fun y : Triple => ∏ i,stripFactor s i (y i)) from rfl,volume_pi]
  exact Integrable.fintype_prod (stripFactor_integrable s hs)

private theorem strip_integral (s : ℝ) (hs : 0<s) : (∫ y : Triple,strip s y)=16*Real.pi/s := by
  unfold strip
  rw [volume_pi,integral_fintype_prod_eq_prod,Fin.prod_univ_three]
  have h0 : (∫ x : ℝ,stripFactor s 0 x)=4 := by
    norm_num [stripFactor,integral_indicator measurableSet_Icc,integral_const]
  have h1 : (∫ x : ℝ,stripFactor s 1 x)=Real.sqrt (Real.pi/(s/4)) := by
    simpa only [stripFactor,show (1 : Fin 3)≠0 by decide,if_false,neg_mul] using integral_gaussian (s/4)
  have h2 : (∫ x : ℝ,stripFactor s 2 x)=Real.sqrt (Real.pi/(s/4)) := by
    simpa only [stripFactor,show (2 : Fin 3)≠0 by decide,if_false,neg_mul] using integral_gaussian (s/4)
  rw [h0,h1,h2]
  have hh := Real.sq_sqrt (show 0≤Real.pi/(s/4) by positivity)
  calc
    _ = 4*(Real.sqrt (Real.pi/(s/4)))^2 := by ring
    _ = _ := by rw [hh]; field_simp; ring

private theorem transverse_chart (y : Triple) :
    transverse (hemisphereChart y)*(radius y)^2=(y 1)^2+(y 2)^2 := by
  unfold transverse
  rw [lift_recover,recover_chart]
  simp [rawPoint]
  field_simp [(radius_positive y).ne']

private theorem patch_density_bound (s : ℝ) (hs : 0<s) (y : Triple) :
    chartDensity y*patchWeight s (hemisphereChart y)≤chartDensity 0*strip s y := by
  by_cases hy : hemisphereChart y∈patch
  · have hp : (1 : ℝ)/2≤halfTrace (hemisphereChart y) := by
      rw [halfTrace_recover,← lift_recover]
      exact hy
    rw [chart_halfTrace] at hp
    have hr := radius_positive y
    have hh := mul_le_mul_of_nonneg_right hp hr.le
    rw [inv_mul_cancel₀ hr.ne'] at hh
    have hrad : radius y≤2 := by linarith
    have hsqr : (radius y)^2=1+(y 0)^2+(y 1)^2+(y 2)^2 := by
      rw [radius,Real.sq_sqrt (chartRate_positive y).le]
      rfl
    have hy0 : y 0∈Icc (-2 : ℝ) 2 := by
      constructor <;> nlinarith [sq_nonneg (y 0+2),sq_nonneg (y 0-2),sq_nonneg (y 1),sq_nonneg (y 2)]
    have hq : ((y 1)^2+(y 2)^2)/4≤transverse (hemisphereChart y) := by
      have ht := transverse_chart y
      have hn := transverse_nonneg (hemisphereChart y)
      have h4 : (radius y)^2≤4 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.mpr h4) hn]
    have he : gaussian s (hemisphereChart y)≤Real.exp (-s*((y 1)^2+(y 2)^2)/4) :=
      Real.exp_le_exp.mpr (by have hb := mul_le_mul_of_nonneg_left hq hs.le; nlinarith)
    rw [patchWeight,Set.indicator_of_mem hy,strip_formula,Set.indicator_of_mem hy0,one_mul]
    exact mul_le_mul (FourCubeHaarLaplaceDensity.chartDensity_le_zero y) he
      (Real.exp_pos _).le (chartDensity_nonneg _)
  · rw [patchWeight,Set.indicator_of_notMem hy,mul_zero]
    apply mul_nonneg (chartDensity_nonneg _)
    unfold strip
    apply Finset.prod_nonneg
    intro i _
    unfold stripFactor
    split_ifs
    · exact Set.indicator_nonneg (fun _ _ => (by norm_num : (0 : ℝ)≤1)) _
    · exact (Real.exp_pos _).le

private theorem patch_integral (s : ℝ) :
    (∫ c,patchWeight s c ∂law)=∫ y : Triple,chartDensity y*patchWeight s (hemisphereChart y) := by
  have hm : Measurable (patchWeight s) :=
    ((measurable_const.mul transverse_continuous.measurable).exp).indicator patch_measurable
  have h := integral_map (μ := coordinateLaw) chart_measurable.aemeasurable hm.aestronglyMeasurable
  unfold patchWeight at h
  rw [chart_map_coordinateLaw,integral_indicator patch_measurable,
    Measure.restrict_restrict_of_subset patch_subset,← integral_indicator patch_measurable] at h
  rw [coordinateLaw,integral_withDensity_eq_integral_toReal_smul
    chartDensity_measurable.ennreal_ofReal (ae_of_all volume (fun _ => ENNReal.ofReal_lt_top))] at h
  simpa only [patchWeight,ENNReal.toReal_ofReal (chartDensity_nonneg _),smul_eq_mul] using h

private theorem patch_integral_upper (s : ℝ) (hs : 0<s) :
    (∫ c,patchWeight s c ∂law)≤chartDensity 0*(16*Real.pi/s) := by
  have hm : Measurable (fun y : Triple => chartDensity y*patchWeight s (hemisphereChart y)) :=
    chartDensity_measurable.mul ((((measurable_const.mul transverse_continuous.measurable).exp).indicator
      patch_measurable).comp chart_measurable)
  have hi := ((strip_integrable s hs).const_mul (chartDensity 0)).mono' hm.aestronglyMeasurable
    (ae_of_all volume (fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (chartDensity_nonneg _) (patchWeight_nonneg s _))]
      exact patch_density_bound s hs y))
  have hh := integral_mono hi ((strip_integrable s hs).const_mul (chartDensity 0)) (patch_density_bound s hs)
  rw [integral_const_mul,strip_integral s hs] at hh
  rw [patch_integral]
  exact hh

theorem mass_upper (s : ℝ) (hs : 0<s) : mass s≤32/(Real.pi*s)+Real.exp (-s/2) := by
  have hh := mass_four_upper s hs.le
  have hp := patch_integral_upper s hs
  have he : 4*(chartDensity (0 : Triple)*(16*Real.pi/s))=32/(Real.pi*s) := by
    norm_num [chartDensity,chartRate]
    field_simp
    ring
  rw [← he]
  linarith

end OperatorDerivativeRewrite.Foundation.SU2TransverseHaar
