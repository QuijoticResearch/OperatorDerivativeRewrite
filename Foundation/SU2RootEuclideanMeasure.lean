import Foundation.SU2RootAdjoint
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The actual SU(2) adjoint rotation preserves triple Lebesgue measure. -/
noncomputable section
open MeasureTheory
open scoped Quaternion Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2RootEuclideanMeasure
open SU2GaussianConeCoordinates QuaternionSU2Representation SU2HemisphereJets

theorem rotate_joint_continuous :
    Continuous (fun p : SU2 × Triple => SU2RootAdjoint.rotate p.1 p.2) := by
  have hr (c : SU2) : recover (c : Matrix (Fin 2) (Fin 2) ℂ)=
      (QuaternionSU2Representation.homeomorph.symm c : Quaternion ℝ) := by
    have h := congrArg (fun z : SU2 => recover (z : Matrix (Fin 2) (Fin 2) ℂ))
      (QuaternionSU2Representation.homeomorph.apply_symm_apply c)
    change recover (repr (QuaternionSU2Representation.homeomorph.symm c : Quaternion ℝ))=
      recover (c : Matrix (Fin 2) (Fin 2) ℂ) at h
    rw [recover_repr] at h
    exact h.symm
  have hc : Continuous (fun c : SU2 => recover (c : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simp_rw [hr]
    exact continuous_subtype_val.comp QuaternionSU2Representation.homeomorph.symm.continuous
  have hp : Continuous (fun y : Triple => (⟨0,y 0,y 1,y 2⟩ : Quaternion ℝ)) := by
    change Continuous (fun y : Triple => Quaternion.linearIsometryEquivTuple.symm
      (WithLp.toLp 2 ![0,y 0,y 1,y 2]))
    apply Quaternion.linearIsometryEquivTuple.symm.continuous.comp
    fun_prop
  let q (p : SU2 × Triple) : Quaternion ℝ :=
    recover (p.1 : Matrix (Fin 2) (Fin 2) ℂ)*
      (⟨0,p.2 0,p.2 1,p.2 2⟩ : Quaternion ℝ)*star (recover (p.1 : Matrix (Fin 2) (Fin 2) ℂ))
  change Continuous (fun p : SU2 × Triple => ![(q p).imI,(q p).imJ,(q p).imK])
  have hq : Continuous q :=
    ((hc.comp continuous_fst).mul (hp.comp continuous_snd)).mul (hc.comp continuous_fst).star
  apply continuous_pi
  intro i
  fin_cases i
  · exact Quaternion.continuous_imI.comp hq
  · exact Quaternion.continuous_imJ.comp hq
  · exact Quaternion.continuous_imK.comp hq

def euclideanRotation (c : SU2) : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin 3) where
  toFun X := WithLp.toLp 2 (SU2RootAdjoint.rotate c (WithLp.ofLp X))
  map_add' X Y := by
    change WithLp.toLp 2 (SU2RootAdjoint.rotate c (WithLp.ofLp X+WithLp.ofLp Y))=_
    rw [SU2RootAdjoint.rotate_add]
    rfl
  map_smul' r X := by
    change WithLp.toLp 2 (SU2RootAdjoint.rotate c (r • WithLp.ofLp X))=_
    rw [SU2RootAdjoint.rotate_smul]
    rfl
  norm_map' X := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    change (∑ i,(SU2RootAdjoint.rotate c (WithLp.ofLp X) i)^2)=
      ∑ i,(WithLp.ofLp X i)^2
    simpa only [Fin.sum_univ_three,sizeSq] using
      SU2RootAdjoint.rotate_sizeSq c (WithLp.ofLp X)

def euclideanEquiv (c : SU2) : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin 3) :=
  LinearIsometryEquiv.ofSurjective (euclideanRotation c)
    (LinearMap.surjective_of_injective (euclideanRotation c).injective)

theorem euclideanEquiv_apply (c : SU2) (X : EuclideanSpace ℝ (Fin 3)) :
    euclideanEquiv c X=WithLp.toLp 2 (SU2RootAdjoint.rotate c (WithLp.ofLp X)) := rfl

theorem rotate_preserving (c : SU2) :
    MeasurePreserving (SU2RootAdjoint.rotate c) (volume : Measure Triple) volume := by
  have h := (PiLp.volume_preserving_ofLp (Fin 3)).comp
    ((euclideanEquiv c).measurePreserving.comp (PiLp.volume_preserving_toLp (Fin 3)))
  convert h using 1
  funext y
  rfl

def rotationEquiv (c : SU2) : Triple ≃ᵐ Triple :=
  (MeasurableEquiv.toLp 2 Triple).trans
    ((euclideanEquiv c).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.trans
      (MeasurableEquiv.toLp 2 Triple).symm)

theorem rotationEquiv_apply (c : SU2) (y : Triple) :
    rotationEquiv c y=SU2RootAdjoint.rotate c y := rfl

theorem rotate_integral (c : SU2) (f : Triple → ℝ) :
    (∫ y : Triple,f (SU2RootAdjoint.rotate c y))=∫ y : Triple,f y := by
  have h : MeasurePreserving (rotationEquiv c) (volume : Measure Triple) volume := by
    change MeasurePreserving (SU2RootAdjoint.rotate c) volume volume
    exact rotate_preserving c
  exact h.integral_comp' f

end OperatorDerivativeRewrite.Foundation.SU2RootEuclideanMeasure
