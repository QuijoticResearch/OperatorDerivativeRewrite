import Foundation.CubeGaussianSecondMoment

/-! True shifted triple Gaussian moments for the actual radial channel observable. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianTripleMoment
open CubeGaussianSecondMoment CubeGaussianChannelGround
open SU2GaussianConeCoordinates SU2HemisphereJets

theorem gaussian_product (b : ℝ) (y : Triple) :
    Real.exp (-b*sizeSq y)=∏ a : Fin 3,Real.exp (-b*(y a)^2) := by
  rw [← Real.exp_sum]
  congr 1
  simp [sizeSq,Fin.sum_univ_three]
  ring

private theorem monomial_product (b : ℝ) (n : Fin 3 → ℕ) (y : Triple) :
    (∏ a,(y a)^(n a))*Real.exp (-b*sizeSq y)=
      ∏ a,(y a)^(n a)*Real.exp (-b*(y a)^2) := by
  rw [Finset.prod_mul_distrib,gaussian_product]

theorem monomial_integrable (b : ℝ) (hb : 0 < b) (n : Fin 3 → ℕ) :
    Integrable (fun y : Triple => (∏ a,(y a)^(n a))*Real.exp (-b*sizeSq y)) := by
  simp_rw [monomial_product]
  rw [volume_pi]
  exact Integrable.fintype_prod (fun a => scalar_pow_integrable b hb (n a))

theorem monomial_integral (b : ℝ) (n : Fin 3 → ℕ) :
    (∫ y : Triple,(∏ a,(y a)^(n a))*Real.exp (-b*sizeSq y))=
      ∏ a,∫ z : ℝ,z^(n a)*Real.exp (-b*z^2) := by
  simp_rw [monomial_product]
  rw [integral_fintype_prod_volume_eq_prod
    (fun (a : Fin 3) (z : ℝ) => z^(n a)*Real.exp (-b*z^2))]

theorem coordinate_integrable (b : ℝ) (hb : 0 < b) (a : Fin 3) (n : ℕ) :
    Integrable (fun y : Triple => (y a)^n*Real.exp (-b*sizeSq y)) := by
  have h := monomial_integrable b hb (fun j => if j=a then n else 0)
  fin_cases a <;> simpa [Fin.prod_univ_three] using h

theorem coordinate_integral (b : ℝ) (a : Fin 3) (n : ℕ) :
    (∫ y : Triple,(y a)^n*Real.exp (-b*sizeSq y))=
      (∫ z : ℝ,z^n*Real.exp (-b*z^2))*(∫ z : ℝ,Real.exp (-b*z^2))^2 := by
  have h := monomial_integral b (fun j => if j=a then n else 0)
  fin_cases a <;>
    simpa [Fin.prod_univ_three,pow_two,mul_assoc,mul_comm,mul_left_comm] using h

theorem gaussianMass_product (b : ℝ) :
    gaussianMass b=(∫ z : ℝ,Real.exp (-b*z^2))^3 := by
  unfold gaussianMass
  simp_rw [gaussian_product]
  rw [integral_fintype_prod_volume_eq_pow (ι := Fin 3) (fun z : ℝ => Real.exp (-b*z^2))]
  norm_num

theorem coordinate_first (b : ℝ) (hb : 0 < b) (a : Fin 3) :
    (∫ y : Triple,y a*Real.exp (-b*sizeSq y))=0 := by
  have h := coordinate_integral b a 1
  simpa only [pow_one,scalar_first_integral b hb,zero_mul] using h

theorem coordinate_second (b : ℝ) (hb : 0 < b) (a : Fin 3) :
    (∫ y : Triple,(y a)^2*Real.exp (-b*sizeSq y))=(2*b)⁻¹*gaussianMass b := by
  rw [coordinate_integral,scalar_second_integral b hb,gaussianMass_product]
  ring

theorem shifted_coordinate_integrable (b : ℝ) (hb : 0 < b) (a : Fin 3) (v : ℝ) :
    Integrable (fun y : Triple => (y a+v)^2*Real.exp (-b*sizeSq y)) := by
  have h2 := coordinate_integrable b hb a 2
  have h1 : Integrable (fun y : Triple => y a*Real.exp (-b*sizeSq y)) := by
    simpa only [pow_one] using coordinate_integrable b hb a 1
  have h0 := CubeGaussianChannelGround.gaussian_integrable b hb
  convert (h2.add (h1.const_mul (2*v))).add (h0.const_mul (v^2)) using 1
  funext y
  simp only [Pi.add_apply]
  ring

theorem shifted_coordinate_integral (b : ℝ) (hb : 0 < b) (a : Fin 3) (v : ℝ) :
    (∫ y : Triple,(y a+v)^2*Real.exp (-b*sizeSq y))=
      ((2*b)⁻¹+v^2)*gaussianMass b := by
  have h2 := coordinate_integrable b hb a 2
  have h1 : Integrable (fun y : Triple => y a*Real.exp (-b*sizeSq y)) := by
    simpa only [pow_one] using coordinate_integrable b hb a 1
  have h0 := CubeGaussianChannelGround.gaussian_integrable b hb
  have he (y : Triple) : (y a+v)^2*Real.exp (-b*sizeSq y)=
      ((y a)^2*Real.exp (-b*sizeSq y)+(2*v)*(y a*Real.exp (-b*sizeSq y)))+
        v^2*Real.exp (-b*sizeSq y) := by ring
  simp_rw [he]
  change (∫ y : Triple,(((fun y : Triple => (y a)^2*Real.exp (-b*sizeSq y))+
    (fun y : Triple => (2*v)*(y a*Real.exp (-b*sizeSq y)))) y+
      v^2*Real.exp (-b*sizeSq y)))=_
  rw [integral_add (h2.add (h1.const_mul (2*v))) (h0.const_mul (v^2))]
  simp only [Pi.add_apply]
  rw [integral_add h2 (h1.const_mul (2*v))]
  simp_rw [integral_const_mul,coordinate_second b hb a,coordinate_first b hb a]
  unfold gaussianMass
  ring

private theorem shifted_product (b : ℝ) (v y : Triple) :
    sizeSq (y+v)*Real.exp (-b*sizeSq y)=
      ∑ a : Fin 3,(y a+v a)^2*Real.exp (-b*sizeSq y) := by
  simp [sizeSq,Fin.sum_univ_three]
  ring

theorem shifted_triple_integrable (b : ℝ) (hb : 0 < b) (v : Triple) :
    Integrable (fun y : Triple => sizeSq (y+v)*Real.exp (-b*sizeSq y)) := by
  simp_rw [shifted_product]
  exact integrable_finset_sum _ (fun a _ => shifted_coordinate_integrable b hb a (v a))

theorem shifted_triple_integral (b : ℝ) (hb : 0 < b) (v : Triple) :
    (∫ y : Triple,sizeSq (y+v)*Real.exp (-b*sizeSq y))=
      (sizeSq v+3/(2*b))*gaussianMass b := by
  simp_rw [shifted_product]
  rw [integral_finset_sum _ (fun a _ => shifted_coordinate_integrable b hb a (v a))]
  simp_rw [shifted_coordinate_integral b hb]
  simp [sizeSq,Fin.sum_univ_three,div_eq_mul_inv]
  ring

end OperatorDerivativeRewrite.Foundation.CubeGaussianTripleMoment
