import Foundation.CubeGaussianRadialChannel

/-! The actual common-root action on the centered radial Gaussian observable. -/
noncomputable section
open MeasureTheory
open scoped Quaternion Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianRadialRoot
open CubeGaussianModes CubeGaussianChannelGround CubeGaussianRootGround CubeChartAction
open CubeGaussianRadialChannel SU2GaussianConeCoordinates SU2HemisphereJets QuaternionSU2Representation
attribute [local irreducible] joint channel gaussianState SU2RootAdjoint.rotate

private theorem select_product (j : Fin 5) (a b : Fin 5 → ℝ) :
    (∏ i,if i=j then a i*b i else b i)=a j*∏ i,b i := by
  have he (i : Fin 5) : (if i=j then a i*b i else b i)=(if i=j then a i else 1)*b i := by
    by_cases h : i=j <;> simp [h]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

private def factor (x : Boundary) (c : SU2) (i : Fin 5) (y : Triple) : ℝ :=
  Real.exp (-channel i (x i) y c)*Real.exp (-width i*sizeSq y)

private theorem prod_factor (x y : Boundary) (c : SU2) :
    (∏ i,factor x c i (y i))=joint x (c,y) := by
  unfold factor joint gaussianState
  rw [Finset.prod_mul_distrib]

theorem fixed_second_integrable (j : Fin 5) (x : Boundary) (c : SU2) :
    Integrable (fun y : Boundary => sizeSq (y j)*joint x (c,y)) := by
  classical
  let f (i : Fin 5) (z : Triple) := if i=j then sizeSq z*factor x c i z else factor x c i z
  have hi (i : Fin 5) : Integrable (f i) := by
    by_cases h : i=j
    · simpa only [f,if_pos h,factor] using channel_second_integrable i (x i) c
    · simpa only [f,if_neg h,factor] using channel_ground_integrable i (x i) c
  have h := Integrable.fintype_prod hi
  rw [← volume_pi] at h
  convert h using 1
  funext y
  change sizeSq (y j)*joint x (c,y)=(∏ i,if i=j then sizeSq (y i)*factor x c i (y i) else factor x c i (y i))
  rw [select_product,prod_factor]

theorem fixed_second_integral (j : Fin 5) (x : Boundary) (c : SU2) :
    (∫ y : Boundary,sizeSq (y j)*joint x (c,y))=
      gaussianState x*stateMass*((ratio j)^2*sizeSq (x j)+3/(2*(precision j+width j))) := by
  classical
  let f (i : Fin 5) (z : Triple) := if i=j then sizeSq z*factor x c i z else factor x c i z
  have he (y : Boundary) : sizeSq (y j)*joint x (c,y)=∏ i,f i (y i) := by
    change _=(∏ i,if i=j then sizeSq (y i)*factor x c i (y i) else factor x c i (y i))
    rw [select_product,prod_factor]
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_prod f]
  have hi (i : Fin 5) : (∫ z : Triple,f i z)=
      if i=j then ((ratio i)^2*sizeSq (x i)+3/(2*(precision i+width i)))*
        (Real.exp (-width i*sizeSq (x i))*gaussianMass (precision i+width i))
      else Real.exp (-width i*sizeSq (x i))*gaussianMass (precision i+width i) := by
    by_cases h : i=j
    · simp only [f,if_pos h,factor]
      rw [channel_second_integral]
      ring
    · simp only [f,if_neg h,factor]
      exact channel_ground_integral i (x i) c
  simp_rw [hi]
  rw [select_product]
  unfold gaussianState stateMass
  rw [Finset.prod_mul_distrib]
  ring

def radial (j : Fin 5) (x : Boundary) : ℝ := (sizeSq (x j)-center j)*gaussianState x

def secondJoint (j : Fin 5) (x : Boundary) (p : SU2 × Boundary) : ℝ :=
  sizeSq (p.2 j)*joint x p

theorem secondJoint_integrable (j : Fin 5) (x : Boundary) :
    Integrable (secondJoint j x) (law.prod (volume : Measure Boundary)) := by
  have hc : Continuous (secondJoint j x) := by
    have hs : Continuous (fun p : SU2 × Boundary => sizeSq (p.2 j)) := by
      unfold sizeSq
      fun_prop
    exact hs.mul (joint_continuous x)
  apply (integrable_prod_iff hc.measurable.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all law (fixed_second_integrable j x)
  · have he : (fun c : SU2 => ∫ y : Boundary,‖secondJoint j x (c,y)‖)=
        (fun _ : SU2 => gaussianState x*stateMass*
          ((ratio j)^2*sizeSq (x j)+3/(2*(precision j+width j)))) := by
      funext c
      have hn (y : Boundary) : 0 ≤ secondJoint j x (c,y) :=
        mul_nonneg (sizeSq_nonneg _) (joint_positive x (c,y)).le
      simp_rw [Real.norm_eq_abs,abs_of_nonneg (hn _)]
      exact fixed_second_integral j x c
    rw [he]
    exact integrable_const _

def centeredJoint (j : Fin 5) (x : Boundary) (p : SU2 × Boundary) : ℝ :=
  (sizeSq (p.2 j)-center j)*joint x p

theorem centeredJoint_integrable (j : Fin 5) (x : Boundary) :
    Integrable (centeredJoint j x) (law.prod (volume : Measure Boundary)) := by
  convert (secondJoint_integrable j x).sub ((joint_integrable x).const_mul (center j)) using 1
  funext p
  simp only [Pi.sub_apply,secondJoint,centeredJoint]
  ring

theorem centered_fixed_integral (j : Fin 5) (x : Boundary) (c : SU2) :
    (∫ y : Boundary,centeredJoint j x (c,y))=(ratio j)^2*radial j x*stateMass := by
  have he (y : Boundary) : centeredJoint j x (c,y)=
      sizeSq (y j)*joint x (c,y)-center j*joint x (c,y) := by unfold centeredJoint; ring
  have hj : Integrable (fun y : Boundary => joint x (c,y)) := by
    unfold joint
    exact fixed_root_ground_integrable x c
  have hji : (∫ y : Boundary,joint x (c,y))=gaussianState x*stateMass := by
    unfold joint
    exact fixed_root_ground_integral x c
  simp_rw [he]
  rw [integral_sub (fixed_second_integrable j x c)
    (hj.const_mul (center j)),integral_const_mul,
    fixed_second_integral]
  rw [hji]
  unfold radial
  have hb := center_balance j
  calc
    _ = (gaussianState x*stateMass)*
      ((ratio j)^2*sizeSq (x j)+3/(2*(precision j+width j))-center j) := by ring
    _ = (gaussianState x*stateMass)*((ratio j)^2*(sizeSq (x j)-center j)) := by
      congr 1
      nlinarith [hb]
    _ = _ := by ring

def averagedRadial (j : Fin 5) (x y : Boundary) : ℝ :=
  (∫ c : SU2,(∏ i : Fin 5,Real.exp (-channel i (x i) (y i) c)) ∂law)*radial j y

private theorem averagedRadial_eq (j : Fin 5) (x y : Boundary) :
    averagedRadial j x y=∫ c : SU2,centeredJoint j x (c,y) ∂law := by
  rw [averagedRadial,← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with c
  unfold centeredJoint radial joint
  ring

theorem averagedRadial_integrable (j : Fin 5) (x : Boundary) : Integrable (averagedRadial j x) := by
  simpa only [← averagedRadial_eq] using (centeredJoint_integrable j x).integral_prod_right

theorem averagedRadial_integral (j : Fin 5) (x : Boundary) :
    (∫ y : Boundary,averagedRadial j x y)=(ratio j)^2*radial j x*stateMass := by
  simp_rw [averagedRadial_eq]
  rw [← integral_integral_swap
    (f := fun c : SU2 => fun y : Boundary => centeredJoint j x (c,y)) (centeredJoint_integrable j x)]
  simp_rw [centered_fixed_integral]
  simp

end OperatorDerivativeRewrite.Foundation.CubeGaussianRadialRoot
