import Foundation.FourCubeColorReflection

/-! Exact eight-sign averaging of the actual full-cell cubic polynomial. -/
noncomputable section
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeCubicSignAverage
open FourCubeMovingOddAction FourCubeColorReflection FourCubeCubicCoordinates
open SU2QuaternionOddWord OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex
open FourCubePinnedSecondVariation
attribute [local irreducible] edges upperFaces innerFaces

def colorMix (s : Signs) (m d : Vector) : Vector :=
  fun a => m a+(if signAt s a then -d a else d a)

theorem triple_sign_sum (u v w du dv dw : Vector) :
    (∑ s : Signs,triple (colorMix s u du) (colorMix s v dv) (colorMix s w dw))=8*triple u v w := by
  simp [Fintype.sum_prod_type,Fintype.sum_bool,colorMix,signAt,triple]
  ring

theorem cubic_sign_sum (m d : Fin 4 → Vector) :
    (∑ s : Signs,cubic (fun i => colorMix s (m i) (d i)))=8*cubic m := by
  unfold cubic weightedCubic
  simp only [one_mul,Finset.sum_add_distrib]
  rw [triple_sign_sum,triple_sign_sum,triple_sign_sum,triple_sign_sum]
  ring

theorem vectorVelocity_affine (s : Signs) (h Y : Coordinates) (x y z : ℝ) (e : FullEdge) :
    vectorVelocity (affine s h Y) x y z e=colorMix s (vectorVelocity h x y z e)
      (vectorVelocity Y x y z e-vectorVelocity h x y z e) := by
  ext a
  cases e with
  | inl e =>
    by_cases hp : e=OneSidedPinnedInterior.pole
    · subst e
      simp [vectorVelocity,liftVelocity_pole,colorMix]
    · have hl (Z : Coordinates) : liftVelocity Z e=Z (⟨e,hp⟩ : OneSidedPinnedInterior.Free) :=
        liftVelocity_free Z ⟨e,hp⟩
      simp only [vectorVelocity,hl,colorMix,affine,reflect,Pi.add_apply,Pi.sub_apply]
  | inr c => simp [vectorVelocity,colorMix]

theorem vectors_affine (s : Signs) (h Y : Coordinates) (x y z : ℝ) (p : FullFace) :
    vectors (affine s h Y) x y z p=(fun i => colorMix s (vectors h x y z p i)
      (vectors Y x y z p i-vectors h x y z p i)) := by
  funext i a
  fin_cases i
  · exact congrFun (vectorVelocity_affine s h Y x y z _) a
  · exact congrFun (vectorVelocity_affine s h Y x y z _) a
  · change (-vectorVelocity (affine s h Y) x y z (OneSidedSourceRows.rowEdges p 2)) a=_
    rw [vectorVelocity_affine]
    simp only [vectors,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,
      colorMix,Pi.neg_apply,Pi.sub_apply]
    cases hs : signAt s a <;> simp [hs] <;> ring
  · change (-vectorVelocity (affine s h Y) x y z (OneSidedSourceRows.rowEdges p 3)) a=_
    rw [vectorVelocity_affine]
    simp only [vectors,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,
      colorMix,Pi.neg_apply,Pi.sub_apply]
    cases hs : signAt s a <;> simp [hs] <;> ring

theorem actual_cubic_sign_sum (h Y : Coordinates) (x y z : ℝ) :
    (∑ s : Signs,cubicCoefficient (affine s h Y) x y z)=8*cubicCoefficient h x y z := by
  simp_rw [cubicCoefficient_vectors]
  rw [Finset.sum_comm]
  have he (p : FullFace) : (∑ s : Signs,cubic (vectors (affine s h Y) x y z p))=
      8*cubic (vectors h x y z p) := by
    simp_rw [vectors_affine]
    exact cubic_sign_sum _ _
  simp_rw [he]
  rw [Finset.mul_sum]

end OperatorDerivativeRewrite.Foundation.FourCubeCubicSignAverage
