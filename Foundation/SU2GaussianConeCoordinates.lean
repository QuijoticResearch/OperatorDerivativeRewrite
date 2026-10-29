import Foundation.QuaternionSU2Representation
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Gaussian cone coordinates for the actual angular-Haar construction.
The positive-real-coordinate cone is kept explicit; it covers only one hemisphere. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Matrix
namespace OperatorDerivativeRewrite.Foundation.SU2GaussianConeCoordinates
abbrev Raw := Fin 4 → ℝ

def positive : Set Raw := {x | 0 < x 0}
def cone (x : Raw) : Raw := ![x 0,x 0*x 1,x 0*x 2,x 0*x 3]
def inverseCone (x : Raw) : Raw := ![x 0,x 1/x 0,x 2/x 0,x 3/x 0]

def jacobian (x : Raw) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,0; x 1,x 0,0,0; x 2,0,x 0,0; x 3,0,0,x 0]

def coneDeriv (x : Raw) : Raw →L[ℝ] Raw :=
  (Matrix.toLin' (jacobian x)).toContinuousLinearMap

theorem coneDeriv_apply (x v : Raw) : coneDeriv x v=
    ![v 0,v 0*x 1+x 0*v 1,v 0*x 2+x 0*v 2,v 0*x 3+x 0*v 3] := by
  ext i
  fin_cases i <;> simp [coneDeriv,jacobian,Matrix.toLin'_apply,Matrix.mulVec,
    dotProduct,Fin.sum_univ_succ] <;> ring

theorem cone_hasFDerivAt (x : Raw) : HasFDerivAt cone (coneDeriv x) x := by
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) x using 1
    · funext v; simp [cone]
    · ext v; simp [coneDeriv_apply]
  · convert (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) x).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) x) using 1
    · funext v; simp [cone]
    · ext v; simp [coneDeriv_apply]; ring
  · convert (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) x).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) x) using 1
    · funext v; simp [cone]
    · ext v; simp [coneDeriv_apply]; ring
  · convert (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) x).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) x) using 1
    · funext v; simp [cone]
    · ext v; simp [coneDeriv_apply]; ring

theorem jacobian_det (x : Raw) : (jacobian x).det=(x 0)^3 := by
  have ht : (jacobian x).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> norm_num [jacobian] at *
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp [jacobian,Fin.prod_univ_succ,pow_succ]
  ring

theorem coneDeriv_det (x : Raw) : (coneDeriv x).det=(x 0)^3 := by
  change LinearMap.det (Matrix.toLin' (jacobian x))=_
  rw [← LinearMap.det_toMatrix',LinearMap.toMatrix'_toLin',jacobian_det]

theorem positive_measurable : MeasurableSet positive :=
  (isOpen_lt continuous_const (continuous_apply 0)).measurableSet

theorem inverseCone_cone (x : Raw) (hx : x 0 ≠ 0) : inverseCone (cone x)=x := by
  ext i
  fin_cases i <;> simp [inverseCone,cone,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,hx]

theorem cone_inverseCone (x : Raw) (hx : x 0 ≠ 0) : cone (inverseCone x)=x := by
  ext i
  fin_cases i <;> simp [inverseCone,cone,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,hx]

theorem cone_injOn : InjOn cone positive := by
  intro x hx y hy he
  have hh := congrArg inverseCone he
  simpa only [inverseCone_cone x (ne_of_gt hx),inverseCone_cone y (ne_of_gt hy)] using hh

theorem cone_image_positive : cone '' positive=positive := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simpa [positive,cone] using hx
  · intro hy
    refine ⟨inverseCone y,?_,cone_inverseCone y (ne_of_gt hy)⟩
    simpa [positive,inverseCone] using hy

theorem lintegral_positive_cone (g : Raw → ℝ≥0∞) :
    (∫⁻ x in positive,g x)=∫⁻ x in positive,ENNReal.ofReal ((x 0)^3)*g (cone x) := by
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure Raw) positive_measurable
    (fun x _ => (cone_hasFDerivAt x).hasFDerivWithinAt) cone_injOn g
  rw [cone_image_positive] at hh
  refine hh.trans (lintegral_congr_ae ?_)
  filter_upwards [ae_restrict_mem positive_measurable] with x hx
  rw [coneDeriv_det,abs_of_pos (pow_pos hx 3)]

open ProbabilityTheory QuaternionSU2Representation

def gaussianDirection (x : Raw) : SU2 :=
  hom (QuaternionAngularHaar.direction (WithLp.toLp 2 x))

theorem gaussianDirection_measurable : Measurable gaussianDirection :=
  hom_continuous.measurable.comp (QuaternionAngularHaar.direction_measurable.comp
    (WithLp.measurable_toLp 2 Raw))

theorem gaussianDirection_law :
    (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)).map gaussianDirection=
      QuaternionSU2Representation.law := by
  unfold gaussianDirection QuaternionSU2Representation.law QuaternionAngularHaar.law
    GaussianAngularSphere.gaussian
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map QuaternionAngularHaar.direction_measurable (WithLp.measurable_toLp 2 Raw),
    Measure.map_map hom_continuous.measurable
      (QuaternionAngularHaar.direction_measurable.comp (WithLp.measurable_toLp 2 Raw))]
  rfl

theorem lintegral_haar_gaussian (f : SU2 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ U,f U ∂QuaternionSU2Representation.law)=
      ∫⁻ x,f (gaussianDirection x) ∂Measure.pi (fun _ : Fin 4 => gaussianReal 0 1) := by
  rw [← gaussianDirection_law]
  exact lintegral_map hf gaussianDirection_measurable

def sectionPoint (x : Raw) : Raw := ![1,x 1,x 2,x 3]

theorem cone_smul_section (x : Raw) : cone x=x 0 • sectionPoint x := by
  ext i
  fin_cases i <;> simp [cone,sectionPoint]

theorem direction_smul_pos (r : ℝ) (hr : 0 < r) (x : GaussianAngularSphere.Space) :
    QuaternionAngularHaar.direction (r • x)=QuaternionAngularHaar.direction x := by
  by_cases hx : x=0
  · subst x
    simp
  · apply Subtype.ext
    change QuaternionAngularHaar.rawDirection (r • x)=QuaternionAngularHaar.rawDirection x
    rw [QuaternionAngularHaar.rawDirection,if_neg (smul_ne_zero hr.ne' hx),
      QuaternionAngularHaar.rawDirection,if_neg hx,NormedSpace.normalize_smul_of_pos hr]

theorem gaussianDirection_cone (x : Raw) (hx : x ∈ positive) :
    gaussianDirection (cone x)=gaussianDirection (sectionPoint x) := by
  rw [cone_smul_section]
  unfold gaussianDirection
  congr 1
  exact direction_smul_pos (x 0) hx (WithLp.toLp 2 (sectionPoint x))

def gaussianDensity (x : Raw) : ℝ := ∏ i : Fin 4,gaussianPDFReal 0 1 (x i)

theorem gaussianDensity_nonneg (x : Raw) : 0 ≤ gaussianDensity x :=
  Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (x i))

theorem gaussianDensity_measurable : Measurable gaussianDensity := by
  unfold gaussianDensity
  fun_prop

theorem rawGaussian_density :
    Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)=
      (volume : Measure Raw).withDensity (fun x => ENNReal.ofReal (gaussianDensity x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hi : Integrable gaussianDensity ((volume : Measure Raw).restrict (Set.univ.pi s)) := by
    rw [volume_pi,Measure.restrict_pi_pi]
    exact Integrable.fintype_prod (fun i => (integrable_gaussianPDFReal 0 1).integrableOn)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ gaussianDensity_nonneg)]
  change ENNReal.ofReal (∫ x,∏ i : Fin 4,gaussianPDFReal 0 1 (x i)
    ∂(volume : Measure Raw).restrict (Set.univ.pi s))=_
  rw [volume_pi,Measure.restrict_pi_pi,integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num),withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_gaussianPDFReal 0 1).integrableOn
    (ae_of_all _ (gaussianPDFReal_nonneg 0 1))

theorem gaussianDirection_halfTrace (x : Raw) (hx : x ≠ 0) :
    halfTrace (gaussianDirection x)=x 0/‖WithLp.toLp 2 x‖ := by
  have hlp : WithLp.toLp 2 x ≠ 0 := by simpa using hx
  unfold gaussianDirection
  rw [halfTrace_map]
  change (QuaternionAngularHaar.rawDirection (WithLp.toLp 2 x)).re=_
  simp only [QuaternionAngularHaar.rawDirection,if_neg hlp]
  change (NormedSpace.normalize (WithLp.toLp 2 x)) 0=_
  simp [NormedSpace.normalize,div_eq_mul_inv,mul_comm]

theorem gaussianDirection_positive_iff (x : Raw) (hx : x ≠ 0) :
    0 < halfTrace (gaussianDirection x) ↔ x ∈ positive := by
  rw [gaussianDirection_halfTrace x hx]
  exact div_pos_iff_of_pos_right (norm_pos_iff.mpr (by simpa using hx))

theorem rawGaussian_ae_ne_zero :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin 4 => gaussianReal 0 1),x ≠ 0 := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  rw [ae_iff]
  simpa using (measure_singleton (0 : Raw) :
    (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)) {0}=0)

def hemisphere : Set SU2 := {U | 0 < halfTrace U}

theorem hemisphere_measurable : MeasurableSet hemisphere :=
  halfTrace_measurable measurableSet_Ioi

theorem lintegral_haar_hemisphere_cone (f : SU2 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ U in hemisphere,f U ∂QuaternionSU2Representation.law)=
      ∫⁻ x in positive,ENNReal.ofReal ((x 0)^3)*
        (ENNReal.ofReal (gaussianDensity (cone x))*f (gaussianDirection (sectionPoint x))) := by
  rw [← gaussianDirection_law,setLIntegral_map hemisphere_measurable hf gaussianDirection_measurable]
  have hs : gaussianDirection ⁻¹' hemisphere =ᵐ[Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)] positive := by
    filter_upwards [rawGaussian_ae_ne_zero] with x hx
    exact propext (gaussianDirection_positive_iff x hx)
  rw [Measure.restrict_congr_set hs,rawGaussian_density]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul (volume : Measure Raw)
    (g := fun x => f (gaussianDirection x)) gaussianDensity_measurable.ennreal_ofReal
    (hf.comp gaussianDirection_measurable) positive_measurable]
  rw [lintegral_positive_cone]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem positive_measurable] with x hx
  simp only [Pi.mul_apply,gaussianDirection_cone x hx]

def radialRate (x : Raw) : ℝ := 1+(x 1)^2+(x 2)^2+(x 3)^2

theorem radialRate_positive (x : Raw) : 0 < radialRate x := by
  unfold radialRate
  positivity

theorem gaussianDensity_cone (x : Raw) :
    gaussianDensity (cone x)=(Real.sqrt (2*Real.pi))⁻¹^4*
      Real.exp (-(x 0)^2*radialRate x/2) := by
  unfold gaussianDensity
  simp only [Fin.prod_univ_succ,Finset.prod_empty,mul_one,gaussianPDFReal,
    NNReal.coe_one,mul_one,sub_zero,cone,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_succ]
  have he : -(x 0)^2*radialRate x/2=
      (-(x 0)^2/2)+(-(x 0*x 1)^2/2)+(-(x 0*x 2)^2/2)+(-(x 0*x 3)^2/2) := by
    unfold radialRate
    ring
  rw [he]
  simp only [Real.exp_add]
  ring

theorem radial_gaussian_integral (a : ℝ) (ha : 0 < a) :
    (∫ r : ℝ in Ioi 0,r^3*Real.exp (-a*r^2/2))=2/a^2 := by
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a/2)
    (by norm_num) (by positivity)
  have hgamma : Real.Gamma (2 : ℝ)=1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  norm_num [hgamma,Real.rpow_two] at hg
  have hc := integral_comp_rpow_Ioi_of_pos
    (g := fun r : ℝ => r*Real.exp (-(a/2*r))) (p := 2) (by norm_num)
  norm_num [Real.rpow_two,smul_eq_mul] at hc
  have he : (fun r : ℝ => (2*r)*(r^2*Real.exp (-(a/2*r^2))))=
      (fun r : ℝ => 2*(r^3*Real.exp (-a*r^2/2))) := by
    funext r
    have hex : -(a/2*r^2)= -a*r^2/2 := by ring
    rw [hex]
    ring
  rw [he,integral_const_mul,hg] at hc
  calc
    _ = (2/a)^2/2 := by linarith [hc]
    _ = 2/a^2 := by field_simp

theorem radial_gaussian_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r^3*Real.exp (-a*r^2/2)) (Ioi 0) := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_sq (b := a/2) (by positivity)
    (s := (3 : ℝ)) (by norm_num)
  simpa [Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh

theorem radial_gaussian_lintegral (a : ℝ) (ha : 0 < a) :
    (∫⁻ r : ℝ in Ioi 0,ENNReal.ofReal (r^3*Real.exp (-a*r^2/2)))=
      ENNReal.ofReal (2/a^2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (radial_gaussian_integrable a ha)]
  · rw [radial_gaussian_integral a ha]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (pow_nonneg hr.le 3) (Real.exp_pos _).le

abbrev Triple := Fin 3 → ℝ

def hemisphereChart (y : Triple) : SU2 := gaussianDirection (Fin.cons 1 y)
def chartRate (y : Triple) : ℝ := 1+(y 0)^2+(y 1)^2+(y 2)^2
def chartDensity (y : Triple) : ℝ := 1/(2*Real.pi^2*(chartRate y)^2)

theorem chartRate_positive (y : Triple) : 0 < chartRate y := by
  unfold chartRate
  positivity

theorem cone_density_normalization : (Real.sqrt (2*Real.pi))⁻¹^4*2=1/(2*Real.pi^2) := by
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hf : (Real.sqrt (2*Real.pi))^4=4*Real.pi^2 := by
    calc
      _ = ((Real.sqrt (2*Real.pi))^2)^2 := by ring
      _ = _ := by rw [hs]; ring
  rw [inv_pow,hf]
  field_simp
  norm_num

theorem cone_radial_density (y : Triple) :
    (∫⁻ r : ℝ in Ioi 0,ENNReal.ofReal (r^3)*
      ENNReal.ofReal (gaussianDensity (cone (Fin.cons r y))))=
        ENNReal.ofReal (chartDensity y) := by
  have hc : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹^4 := by positivity
  have he : (∫⁻ r : ℝ in Ioi 0,ENNReal.ofReal (r^3)*
      ENNReal.ofReal (gaussianDensity (cone (Fin.cons r y))))=
      ∫⁻ r : ℝ in Ioi 0,ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹^4)*
        ENNReal.ofReal (r^3*Real.exp (-chartRate y*r^2/2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [gaussianDensity_cone]
    have hrate : radialRate (Fin.cons r y)=chartRate y := rfl
    rw [hrate]
    simp only [Fin.cons_zero]
    have hex : -r^2*chartRate y/2= -chartRate y*r^2/2 := by ring
    rw [hex,ENNReal.ofReal_mul hc,ENNReal.ofReal_mul (pow_nonneg hr.le 3)]
    simp only [mul_assoc,mul_left_comm,mul_comm]
  rw [he,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    radial_gaussian_lintegral _ (chartRate_positive y),← ENNReal.ofReal_mul hc]
  congr 1
  unfold chartDensity
  rw [← mul_div_assoc,cone_density_normalization]
  field_simp

private theorem cone_measurable : Measurable cone :=
  (continuous_iff_continuousAt.mpr (fun x => (cone_hasFDerivAt x).continuousAt)).measurable

private theorem sectionPoint_measurable : Measurable sectionPoint := by
  unfold sectionPoint
  fun_prop

theorem lintegral_haar_hemisphere_chart (f : SU2 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ U in hemisphere,f U ∂QuaternionSU2Representation.law)=
      ∫⁻ y : Triple,ENNReal.ofReal (chartDensity y)*f (hemisphereChart y) := by
  rw [lintegral_haar_hemisphere_cone f hf]
  let K : Raw → ℝ≥0∞ := fun x => ENNReal.ofReal ((x 0)^3)*
    (ENNReal.ofReal (gaussianDensity (cone x))*f (gaussianDirection (sectionPoint x)))
  have hK : Measurable K := by
    exact (by fun_prop : Measurable (fun x : Raw => ENNReal.ofReal ((x 0)^3))).mul
      ((gaussianDensity_measurable.comp cone_measurable).ennreal_ofReal.mul
        (hf.comp (gaussianDirection_measurable.comp sectionPoint_measurable)))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm
  have hh := hp.setLIntegral_comp_preimage positive_measurable hK
  have he : (e.symm : ℝ × Triple → Raw)=(fun p => Fin.cons p.1 p.2) := by
    funext p
    ext i
    fin_cases i <;> rfl
  change (∫⁻ p in e.symm ⁻¹' positive,K (e.symm p)
    ∂(volume : Measure ℝ).prod (volume : Measure Triple))=(∫⁻ x in positive,K x) at hh
  have hpre : e.symm ⁻¹' positive=(Ioi (0 : ℝ)) ×ˢ (univ : Set Triple) := by
    ext p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNth_zero,positive]
  change (∫⁻ x in positive,K x)=_
  calc
    _ = ∫⁻ p : ℝ × Triple in (Ioi 0) ×ˢ univ,K (Fin.cons p.1 p.2) := by
      rw [hpre,he] at hh
      exact hh.symm
    _ = ∫⁻ y : Triple,∫⁻ r : ℝ in Ioi 0,K (Fin.cons r y) := by
      have hm : Measurable (fun p : ℝ × Triple => K (Fin.cons p.1 p.2)) :=
        hK.comp (by fun_prop)
      simpa only [Measure.restrict_univ,Measure.volume_eq_prod] using
        setLIntegral_prod_symm (μ := (volume : Measure ℝ)) (ν := (volume : Measure Triple))
          (s := Ioi 0) (t := univ) (fun p : ℝ × Triple => K (Fin.cons p.1 p.2)) hm.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards with y
      have hm : Measurable (fun r : ℝ => ENNReal.ofReal (r^3)*
          ENNReal.ofReal (gaussianDensity (cone (Fin.cons r y)))) := by
        exact (by fun_prop : Measurable (fun r : ℝ => ENNReal.ofReal (r^3))).mul
          ((gaussianDensity_measurable.comp cone_measurable).comp
          (by fun_prop)).ennreal_ofReal
      have hs (r : ℝ) : sectionPoint (Fin.cons r y)=Fin.cons 1 y := by
        ext i
        fin_cases i <;> rfl
      simp only [K,hs,Fin.cons_zero,← mul_assoc]
      rw [lintegral_mul_const _ hm,cone_radial_density]
      rfl

end OperatorDerivativeRewrite.Foundation.SU2GaussianConeCoordinates
