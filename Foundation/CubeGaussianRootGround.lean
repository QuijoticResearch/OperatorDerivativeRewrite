import Foundation.CubeGaussianChannelGround

/-! Joint integrability and the common-root averaged Gaussian ground integral. -/
noncomputable section
open MeasureTheory
open scoped Quaternion Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianRootGround
open CubeGaussianModes CubeGaussianChannelGround CubeChartAction
open SU2GaussianConeCoordinates SU2HemisphereJets QuaternionSU2Representation
attribute [local irreducible] SU2RootAdjoint.rotate channel gaussianState

def joint (x : Boundary) (p : SU2 × Boundary) : ℝ :=
  (∏ i : Fin 5,Real.exp (-channel i (x i) (p.2 i) p.1))*gaussianState p.2

private theorem sizeSq_continuous : Continuous sizeSq := by
  unfold sizeSq
  fun_prop

theorem gaussianState_continuous : Continuous gaussianState := by
  unfold gaussianState sizeSq
  fun_prop

theorem joint_continuous (x : Boundary) : Continuous (joint x) := by
  unfold joint
  apply Continuous.mul ?_ (gaussianState_continuous.comp continuous_snd)
  apply continuous_finset_prod
  intro i _
  have hy : Continuous (fun p : SU2 × Boundary => p.2 i) :=
    (continuous_apply i).comp continuous_snd
  have hr : Continuous (fun p : SU2 × Boundary => SU2RootAdjoint.rotate p.1 (p.2 i)) :=
    SU2RootEuclideanMeasure.rotate_joint_continuous.comp (continuous_fst.prodMk hy)
  have hys : Continuous (fun p : SU2 × Boundary => sizeSq (p.2 i)) :=
    sizeSq_continuous.comp hy
  have hds : Continuous (fun p : SU2 × Boundary =>
      sizeSq (x i-SU2RootAdjoint.rotate p.1 (p.2 i))) :=
    sizeSq_continuous.comp (continuous_const.sub hr)
  unfold channel
  exact Real.continuous_exp.comp (continuous_const.mul
    ((continuous_const.mul (continuous_const.add hys)).add
      (continuous_const.mul hds))).neg

theorem gaussianState_positive (x : Boundary) : 0 < gaussianState x := by
  unfold gaussianState
  exact Finset.prod_pos (fun _ _ => Real.exp_pos _)

theorem stateMass_positive : 0 < stateMass :=
  Finset.prod_pos (fun i _ => gaussianMass_positive _
    (add_pos (precision_positive i) (width_positive i)))

theorem joint_positive (x : Boundary) (p : SU2 × Boundary) : 0 < joint x p :=
  mul_pos (Finset.prod_pos (fun _ _ => Real.exp_pos _)) (gaussianState_positive p.2)

theorem joint_integrable (x : Boundary) :
    Integrable (joint x) (law.prod (volume : Measure Boundary)) := by
  apply (integrable_prod_iff (joint_continuous x).measurable.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all law (fun c => fixed_root_ground_integrable x c)
  · have he : (fun c : SU2 => ∫ y : Boundary,‖joint x (c,y)‖)=
        (fun _ : SU2 => gaussianState x*stateMass) := by
      funext c
      simp_rw [Real.norm_eq_abs,abs_of_pos (joint_positive x (c,_))]
      exact fixed_root_ground_integral x c
    rw [he]
    exact integrable_const _

def averaged (x y : Boundary) : ℝ :=
  (∫ c : SU2,(∏ i : Fin 5,Real.exp (-channel i (x i) (y i) c)) ∂law)*gaussianState y

private theorem averaged_eq (x y : Boundary) :
    averaged x y=∫ c : SU2,joint x (c,y) ∂law := by
  rw [averaged,← integral_mul_const]
  rfl

theorem averaged_integrable (x : Boundary) : Integrable (averaged x) := by
  have h := (joint_integrable x).integral_prod_right
  simpa only [← averaged_eq] using h

theorem averaged_ground_integral (x : Boundary) :
    (∫ y : Boundary,averaged x y)=gaussianState x*stateMass := by
  simp_rw [averaged_eq]
  rw [← integral_integral_swap (f := fun c : SU2 => fun y : Boundary => joint x (c,y))
    (joint_integrable x)]
  change (∫ c : SU2, (∫ y : Boundary,
    (∏ i : Fin 5,Real.exp (-channel i (x i) (y i) c))*gaussianState y) ∂law)=_
  simp_rw [fixed_root_ground_integral]
  simp

end OperatorDerivativeRewrite.Foundation.CubeGaussianRootGround
