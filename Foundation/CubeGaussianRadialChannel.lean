import Foundation.CubeGaussianTripleMoment

/-! Actual fixed-root radial quadratic channel, with a rigorous shifted moment domain. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianRadialChannel
open CubeGaussianChannelGround CubeGaussianTripleMoment CubeGaussianModes
open SU2GaussianConeCoordinates SU2HemisphereJets QuaternionSU2Representation
attribute [local irreducible] precision width SU2RootAdjoint.rotate

def center (i : Fin 5) : ℝ := 3/(4*width i)

theorem center_positive (i : Fin 5) : 0 < center i :=
  div_pos (by norm_num) (mul_pos (by norm_num) (width_positive i))

theorem ratio_positive (i : Fin 5) : 0 < ratio i :=
  div_pos (weights_positive i)
    (mul_pos (by norm_num) (add_pos (precision_positive i) (width_positive i)))

theorem ratio_lt_one (i : Fin 5) : ratio i < 1 := by
  unfold ratio
  apply (div_lt_one₀ (mul_pos (by norm_num : (0:ℝ)<2)
    (add_pos (precision_positive i) (width_positive i)))).mpr
  have ha : weights i < 2*precision i := by
    unfold precision
    have h := mul_pos (weights_positive i) (orders_positive i)
    nlinarith
  have hs := width_positive i
  linarith

theorem center_balance (i : Fin 5) :
    (ratio i)^2*center i+3/(2*(precision i+width i))=center i := by
  have hs := (width_positive i).ne'
  have hq := (add_pos (precision_positive i) (width_positive i)).ne'
  unfold ratio center
  field_simp [hs,hq]
  nlinarith [width_relation i]

private theorem sizeSq_smul (r : ℝ) (x : Triple) : sizeSq (r • x)=r^2*sizeSq x := by
  simp [sizeSq]
  ring

private theorem exp_completed (i : Fin 5) (x y : Triple) (c : SU2) :
    Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y)=
      Real.exp (-width i*sizeSq x)*Real.exp (-(precision i+width i)*
        sizeSq (SU2RootAdjoint.rotate c y-ratio i • x)) := by
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  have h := channel_completed i x y c
  linarith

theorem channel_second_integral (i : Fin 5) (x : Triple) (c : SU2) :
    (∫ y : Triple,sizeSq y*(Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y)))=
      Real.exp (-width i*sizeSq x)*gaussianMass (precision i+width i)*
        ((ratio i)^2*sizeSq x+3/(2*(precision i+width i))) := by
  have he (y : Triple) : sizeSq y*(Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y))=
      Real.exp (-width i*sizeSq x)*(sizeSq (SU2RootAdjoint.rotate c y)*
        Real.exp (-(precision i+width i)*sizeSq (SU2RootAdjoint.rotate c y-ratio i • x))) := by
    rw [exp_completed,SU2RootAdjoint.rotate_sizeSq]
    ring
  simp_rw [he]
  rw [integral_const_mul,SU2RootEuclideanMeasure.rotate_integral c
    (fun z : Triple => sizeSq z*Real.exp (-(precision i+width i)*sizeSq (z-ratio i • x)))]
  have ht := integral_sub_right_eq_self (μ := (volume : Measure Triple))
    (fun z : Triple => sizeSq (z+ratio i • x)*Real.exp (-(precision i+width i)*sizeSq z))
      (ratio i • x)
  simp only [sub_add_cancel] at ht
  rw [ht,shifted_triple_integral _ (add_pos (precision_positive i) (width_positive i)),sizeSq_smul]
  ring

theorem channel_second_integrable (i : Fin 5) (x : Triple) (c : SU2) :
    Integrable (fun y : Triple => sizeSq y*
      (Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y))) := by
  by_contra hn
  have h := channel_second_integral i x c
  rw [integral_undef hn] at h
  have hq := add_pos (precision_positive i) (width_positive i)
  have hs := sizeSq_nonneg x
  have hp : 0 < Real.exp (-width i*sizeSq x)*gaussianMass (precision i+width i)*
      ((ratio i)^2*sizeSq x+3/(2*(precision i+width i))) := by
    have hm := gaussianMass_positive _ hq
    positivity
  linarith

theorem channel_centered_integrable (i : Fin 5) (x : Triple) (c : SU2) :
    Integrable (fun y : Triple => (sizeSq y-center i)*
      (Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y))) := by
  convert (channel_second_integrable i x c).sub
    ((channel_ground_integrable i x c).const_mul (center i)) using 1
  funext y
  simp only [Pi.sub_apply]
  ring

theorem channel_centered_integral (i : Fin 5) (x : Triple) (c : SU2) :
    (∫ y : Triple,(sizeSq y-center i)*
      (Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y)))=
      (ratio i)^2*(sizeSq x-center i)*
        (Real.exp (-width i*sizeSq x)*gaussianMass (precision i+width i)) := by
  have he (y : Triple) : (sizeSq y-center i)*
      (Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y))=
      sizeSq y*(Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y))-
        center i*(Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y)) := by ring
  simp_rw [he]
  rw [integral_sub (channel_second_integrable i x c)
    ((channel_ground_integrable i x c).const_mul (center i)),integral_const_mul,
    channel_second_integral,channel_ground_integral]
  have hb := center_balance i
  calc
    _ = (Real.exp (-width i*sizeSq x)*gaussianMass (precision i+width i))*
        ((ratio i)^2*sizeSq x+3/(2*(precision i+width i))-center i) := by ring
    _ = (Real.exp (-width i*sizeSq x)*gaussianMass (precision i+width i))*
        ((ratio i)^2*(sizeSq x-center i)) := by congr 1; nlinarith [hb]
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.CubeGaussianRadialChannel
