import Foundation.FourCubeMovingLaplaceLimit
import Foundation.OneSidedSchurForm

/-! Identify the actual moving-boundary Laplace limit with the existing pinned Schur form. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix
namespace OperatorDerivativeRewrite.Foundation.FourCubeMovingSchurLimit
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex
open OneSidedBoundaryGauge OneSidedEffectiveCurvature OneSidedPinnedInterior OneSidedSchurForm
open FourCubeMovingBoundaryQuadratic FourCubeMovingActionLimit FourCubeMovingLaplaceLimit
open FourCubeHaarQuadraticLimit FourCubeHaarLaplaceDensity FourCubeHaarProductCoordinates
open FourCubePinnedSecondVariation SU2MatrixExponentialBridge

attribute [local irreducible] edges upperFaces innerFaces

abbrev ChartField := FourCubeHemisphereCoercivity.Field

def boundaryComponent (x y z : ℝ) (a : Fin 3) : BoundaryField :=
  fun c => boundaryVector x y z c a

private theorem boundary_zero (c : Boundary) : boundaryVector 0 0 0 c=0 := by
  ext a
  cases c <;> fin_cases a <;>
    simp [boundaryVector,SU2AxisMatrixJets.axisVector] <;> split_ifs <;> rfl

private theorem local_upper (y : FreeField) (p : Upper) :
    localMap y (.inr p)=lift y (ribbonInterior p) := by
  change extend (lift y) p.val.1=_
  exact extend_on (lift y) (ribbonInterior p)

private theorem boundary_inner (eta : BoundaryField) (p : Inner) : boundaryMap eta (.inl p)=0 := by
  change realCurl (extend (interiorPart (injectBoundary eta))) p=0
  simp [interiorPart,injectBoundary,OneSidedBlockRank.extend,realCurl]

private theorem boundary_upper (eta : BoundaryField) (p : Upper) :
    boundaryMap eta (.inr p)=eta (.inl (capHigh p))-eta (.inr p)-eta (.inl (capLow p)) := by
  change 0+eta (.inl (capHigh p))-eta (.inr p)-eta (.inl (capLow p))=_
  ring

theorem scalar_joint_difference (u : FreeField) (eta : BoundaryField) :
    jointEnergy u eta=dotProduct u (localGram.mulVec u)+
      ∑ p : Upper,((lift u (ribbonInterior p)+eta (.inl (capHigh p))-
        eta (.inr p)-eta (.inl (capLow p)))^2-(lift u (ribbonInterior p))^2) := by
  have h0 : jointEnergy u 0=dotProduct u (localGram.mulVec u) := by
    rw [jointEnergy,Matrix.mulVec_zero,add_zero,← Matrix.dotProduct_transpose_mulVec,
      Matrix.mulVec_mulVec]
    rfl
  rw [← h0]
  unfold jointEnergy dotProduct
  simp only [localMatrix_mulVec,boundaryMatrix_mulVec,Matrix.mulVec_zero,add_zero,
    Pi.add_apply,Fintype.sum_sum_type,boundary_inner,local_upper,boundary_upper,Pi.zero_apply,add_zero]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem jointQuadratic_schur_input (Y : ChartField) (x y z : ℝ) :
    jointQuadratic Y x y z=
      (∑ a : Fin 3,jointEnergy (fun e => frameField Y e a) (boundaryComponent x y z a))/4 := by
  simp_rw [scalar_joint_difference]
  rw [Finset.sum_add_distrib,frame_quadraticForm]
  have hr (p : Upper) : ribbonQuadratic Y x y z p-ribbonQuadratic Y 0 0 0 p=
      (∑ a : Fin 3,((lift (fun e => frameField Y e a) (ribbonInterior p)+
        boundaryComponent x y z a (.inl (capHigh p))-boundaryComponent x y z a (.inr p)-
        boundaryComponent x y z a (.inl (capLow p)))^2-
        (lift (fun e => frameField Y e a) (ribbonInterior p))^2))/4 := by
    unfold ribbonQuadratic lengthSq
    simp only [ribbonVectors,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Pi.add_apply,Pi.sub_apply,boundary_zero,Pi.zero_apply,
      add_zero,sub_zero]
    rw [← sub_div,← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    have he := congrFun (frame_lift Y (ribbonInterior p)) a
    change SU2HemisphereJets.frame (liftVelocity Y (ribbonInterior p)) a=
      lift (fun e => frameField Y e a) (ribbonInterior p) at he
    rw [he]
    rfl
  unfold jointQuadratic
  simp_rw [hr]
  rw [← Finset.sum_div,Finset.sum_comm]
  ring

def harmonicShift (x y z : ℝ) : ChartField := fun e =>
  ![response (boundaryComponent x y z 2) e/2,
    response (boundaryComponent x y z 0) e/2,response (boundaryComponent x y z 1) e/2]

def effectiveEnergy (x y z : ℝ) : ℝ :=
  (∑ a : Fin 3,reducedEnergy (boundaryComponent x y z a))/4

theorem frame_harmonicShift (x y z : ℝ) (e : Free) (a : Fin 3) :
    frameField (harmonicShift x y z) e a=response (boundaryComponent x y z a) e := by
  fin_cases a <;> simp [frameField,harmonicShift,SU2HemisphereJets.frame] <;> ring

theorem frame_difference (Y Z : ChartField) (e : Free) (a : Fin 3) :
    frameField (Y-Z) e a=frameField Y e a-frameField Z e a := by
  fin_cases a <;> simp [frameField,SU2HemisphereJets.frame,Pi.sub_apply] <;> ring

theorem actual_completed_square (Y : ChartField) (x y z : ℝ) :
    jointQuadratic Y x y z=effectiveEnergy x y z+quadraticForm (Y-harmonicShift x y z) := by
  rw [jointQuadratic_schur_input]
  simp_rw [completed_square,← localGram_energy]
  rw [Finset.sum_add_distrib]
  have he := frame_quadraticForm (Y-harmonicShift x y z)
  have hf (a : Fin 3) :
      (fun e => frameField Y e a)-response (boundaryComponent x y z a)=
        (fun e => frameField (Y-harmonicShift x y z) e a) := by
    funext e
    rw [frame_difference,frame_harmonicShift]
    rfl
  simp_rw [hf]
  rw [he]
  unfold effectiveEnergy
  ring

theorem effectiveEnergy_nonneg (x y z : ℝ) : 0 ≤ effectiveEnergy x y z :=
  div_nonneg (Finset.sum_nonneg (fun a _ => reducedEnergy_nonnegative _)) (by norm_num)

theorem actual_minimizer (x y z : ℝ) :
    jointQuadratic (harmonicShift x y z) x y z=effectiveEnergy x y z := by
  rw [actual_completed_square,sub_self]
  simp [quadraticForm]

theorem limitingDensity_translate (x y z : ℝ) (Y : ChartField) :
    limitingDensity x y z Y=Real.exp (-effectiveEnergy x y z/2)*
      gaussianDensity (Y-harmonicShift x y z) := by
  rw [limitingDensity,actual_completed_square,gaussianDensity]
  have he : -(effectiveEnergy x y z+quadraticForm (Y-harmonicShift x y z))/2=
      -effectiveEnergy x y z/2+ -quadraticForm (Y-harmonicShift x y z)/2 := by ring
  rw [he,Real.exp_add]
  ring

theorem limitingDensity_integral_schur (x y z : ℝ) :
    (∫ Y : ChartField,limitingDensity x y z Y)=
      Real.exp (-effectiveEnergy x y z/2)*(∫ Y : ChartField,gaussianDensity Y) := by
  simp_rw [limitingDensity_translate]
  rw [integral_const_mul,integral_sub_right_eq_self]

theorem moving_partition_ratio_schur (x y z : ℝ) :
    Tendsto (fun t : ℝ => FourCubeScaledBoundaryControl.normalizedPartition (1/t^2)
      (FourCubeScaledBoundaryControl.movingBoundary t x y z)) (𝓝[≠] 0)
      (𝓝 (Real.exp (-effectiveEnergy x y z/2))) := by
  have hh := moving_partition_ratio_limit x y z
  rw [limitingDensity_integral_schur,mul_div_cancel_right₀ _ gaussianDensity_integral_positive.ne'] at hh
  exact hh

theorem moving_freeEnergy_schur (x y z : ℝ) :
    Tendsto (fun t : ℝ => -Real.log (FourCubeScaledBoundaryControl.normalizedPartition (1/t^2)
      (FourCubeScaledBoundaryControl.movingBoundary t x y z))) (𝓝[≠] 0)
      (𝓝 (effectiveEnergy x y z/2)) := by
  have hh := moving_freeEnergy_difference_limit x y z
  rw [limitingDensity_integral_schur,mul_div_cancel_right₀ _ gaussianDensity_integral_positive.ne',
    Real.log_exp,neg_div,neg_neg] at hh
  exact hh

theorem effectiveEnergy_schur (x y z : ℝ) :
    effectiveEnergy x y z=(∑ a : Fin 3,dotProduct (boundaryComponent x y z a)
      (schur.mulVec (boundaryComponent x y z a)))/4 := by
  simp only [effectiveEnergy,schur_energy]

theorem effectiveEnergy_zero_iff_gauge (x y z : ℝ) :
    effectiveEnergy x y z=0 ↔ ∀ a : Fin 3,
      boundaryComponent x y z a∈LinearMap.range boundaryGradient := by
  rw [effectiveEnergy,div_eq_zero_iff]
  simp only [show (4 : ℝ) ≠ 0 by norm_num,or_false]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => reducedEnergy_nonnegative _)]
  simp only [Finset.mem_univ,true_implies,← schur_energy,schur_energy_zero_iff_gauge]

theorem actual_minimum_bound (Y : ChartField) (x y z : ℝ) :
    effectiveEnergy x y z ≤ jointQuadratic Y x y z := by
  rw [actual_completed_square]
  have hp := jointQuadratic_nonneg (Y-harmonicShift x y z) 0 0 0
  rw [jointQuadratic_zero_amplitudes] at hp
  linarith

theorem actual_unique_minimizer (Y : ChartField) (x y z : ℝ) :
    jointQuadratic Y x y z=effectiveEnergy x y z ↔ Y=harmonicShift x y z := by
  constructor
  · intro he
    by_contra hn
    have hp := ray_second_positive (Y-harmonicShift x y z) (sub_ne_zero.mpr hn)
    rw [ray_second_gram] at hp
    rw [actual_completed_square] at he
    linarith
  · rintro rfl
    exact actual_minimizer x y z

theorem limiting_ratio_le_one (x y z : ℝ) :
    Real.exp (-effectiveEnergy x y z/2) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  linarith [effectiveEnergy_nonneg x y z]
end OperatorDerivativeRewrite.Foundation.FourCubeMovingSchurLimit
