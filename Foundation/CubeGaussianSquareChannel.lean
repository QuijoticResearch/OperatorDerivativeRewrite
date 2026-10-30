import Foundation.CubeRadialStationaryQuasimode

/-! Actual squared channel integrals for the Hilbert-Schmidt complement test. -/
noncomputable section
open MeasureTheory
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianSquareChannel
open CubeGaussianModes CubeGaussianChannelGround CubeGaussianTripleMoment
open SU2GaussianConeCoordinates SU2HemisphereJets QuaternionSU2Representation
attribute [local irreducible] SU2RootAdjoint.rotate

def residualPrecision (i : Fin 5) : ℝ := 2*precision i-(weights i)^2/(2*precision i)

theorem residualPrecision_product (i : Fin 5) :
    (2*precision i)*residualPrecision i = (2*width i)^2 := by
  have ha := (precision_positive i).ne'
  unfold residualPrecision
  field_simp [ha]
  nlinarith [width_relation i]

theorem residualPrecision_positive (i : Fin 5) : 0 < residualPrecision i := by
  have h := residualPrecision_product i
  have ha := precision_positive i
  have hs := width_positive i
  nlinarith [sq_pos_of_pos (mul_pos (by norm_num : (0:ℝ)<2) hs)]

theorem gaussianMass_formula (b : ℝ) : gaussianMass b = (Real.sqrt (Real.pi/b))^3 := by
  rw [gaussianMass_product,integral_gaussian]

theorem gaussianMass_sq (b : ℝ) (hb : 0 < b) :
    (gaussianMass b)^2 = (Real.pi/b)^3 := by
  rw [gaussianMass_formula,← pow_mul,show (3:ℕ)*2=2*3 from rfl,pow_mul,
    Real.sq_sqrt (div_nonneg Real.pi_pos.le hb.le)]

theorem gaussianMass_pair (i : Fin 5) :
    gaussianMass (2*precision i)*gaussianMass (residualPrecision i) =
      (gaussianMass (precision i+width i))^2*((precision i+width i)/(2*width i))^3 := by
  have ha := precision_positive i
  have hs := width_positive i
  have hd := residualPrecision_positive i
  have hq := add_pos ha hs
  have hp := residualPrecision_product i
  have hf : (Real.pi/(2*precision i))*(Real.pi/residualPrecision i)=
      (Real.pi/(2*width i))^2 := by
    rw [div_mul_div_comm,hp,div_pow]
    ring
  rw [gaussianMass_formula,gaussianMass_formula,← mul_pow,
    ← Real.sqrt_mul (div_nonneg Real.pi_pos.le (mul_pos (by norm_num) ha).le),hf,
    Real.sqrt_sq (div_nonneg Real.pi_pos.le (mul_pos (by norm_num) hs).le),gaussianMass_sq _ hq,
    ← mul_pow]
  congr 1
  field_simp

private theorem squared_completed (i : Fin 5) (x y : Triple) (c : SU2) :
    (Real.exp (-channel i x y c))^2 =
      Real.exp (-residualPrecision i*sizeSq x)*
        Real.exp (-(2*precision i)*sizeSq (SU2RootAdjoint.rotate c y-
          (weights i/(2*precision i)) • x)) := by
  have ha := (precision_positive i).ne'
  rw [pow_two,← Real.exp_add,← Real.exp_add]
  congr 1
  rw [channel_gaussian]
  change -(precision i*(sizeSq x+sizeSq y)-weights i*dotProduct x (SU2RootAdjoint.rotate c y))+
    -(precision i*(sizeSq x+sizeSq y)-weights i*dotProduct x (SU2RootAdjoint.rotate c y))=_
  rw [← SU2RootAdjoint.rotate_sizeSq c y]
  unfold residualPrecision sizeSq dotProduct
  simp only [Fin.sum_univ_three,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  field_simp [ha]
  <;> ring

theorem squared_row_integral (i : Fin 5) (x : Triple) (c : SU2) :
    (∫ y : Triple,(Real.exp (-channel i x y c))^2)=
      Real.exp (-residualPrecision i*sizeSq x)*gaussianMass (2*precision i) := by
  simp_rw [squared_completed]
  rw [integral_const_mul,SU2RootEuclideanMeasure.rotate_integral c
    (fun z : Triple => Real.exp (-(2*precision i)*sizeSq (z-(weights i/(2*precision i)) • x))),
    integral_sub_right_eq_self (fun z : Triple => Real.exp (-(2*precision i)*sizeSq z))]
  rfl

theorem squared_row_integrable (i : Fin 5) (x : Triple) (c : SU2) :
    Integrable (fun y : Triple => (Real.exp (-channel i x y c))^2) := by
  by_contra hn
  have h := squared_row_integral i x c
  rw [integral_undef hn] at h
  have hp := mul_pos (Real.exp_pos (-residualPrecision i*sizeSq x))
    (gaussianMass_positive _ (mul_pos (by norm_num : (0:ℝ)<2) (precision_positive i)))
  linarith

theorem squared_joint_integrable (i : Fin 5) (c : SU2) :
    Integrable (fun p : Triple × Triple => (Real.exp (-channel i p.1 p.2 c))^2) := by
  have hc : Continuous (fun p : Triple × Triple => (Real.exp (-channel i p.1 p.2 c))^2) := by
    have hr : Continuous (fun p : Triple × Triple => SU2RootAdjoint.rotate c p.2) :=
      SU2RootEuclideanMeasure.rotate_joint_continuous.comp (continuous_const.prodMk continuous_snd)
    unfold channel sizeSq
    fun_prop
  apply (integrable_prod_iff hc.measurable.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun x => squared_row_integrable i x c)
  · have he : (fun x : Triple => ∫ y : Triple,‖(Real.exp (-channel i x y c))^2‖)=
        (fun x : Triple => Real.exp (-residualPrecision i*sizeSq x)*gaussianMass (2*precision i)) := by
      funext x
      have hn (y : Triple) : ‖(Real.exp (-channel i x y c))^2‖=
          (Real.exp (-channel i x y c))^2 := by rw [Real.norm_eq_abs]; exact abs_of_nonneg (sq_nonneg _)
      simp_rw [hn]
      exact squared_row_integral i x c
    rw [he]
    exact (gaussian_integrable _ (residualPrecision_positive i)).mul_const _

theorem squared_joint_integral (i : Fin 5) (c : SU2) :
    (∫ p : Triple × Triple,(Real.exp (-channel i p.1 p.2 c))^2)=
      (gaussianMass (precision i+width i))^2*((precision i+width i)/(2*width i))^3 := by
  change (∫ p : Triple × Triple,(Real.exp (-channel i p.1 p.2 c))^2 ∂(volume.prod volume))=_
  rw [integral_prod _ (squared_joint_integrable i c)]
  simp_rw [squared_row_integral]
  rw [integral_mul_const]
  rw [mul_comm]
  exact gaussianMass_pair i

end OperatorDerivativeRewrite.Foundation.CubeGaussianSquareChannel
