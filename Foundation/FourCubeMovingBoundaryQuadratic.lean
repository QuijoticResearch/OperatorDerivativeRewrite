import Foundation.SU2AxisMatrixJets
import Foundation.FourCubeMovingBoundaryConcentration

/-! Actual moving-boundary ribbon jets, with the original Haar chart and boundary axes. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator Topology
open Filter Set
namespace OperatorDerivativeRewrite.Foundation.FourCubeMovingBoundaryQuadratic
open QuaternionSU2Representation SU2TraceHessianModel SU2MatrixExponentialBridge
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex
open FourCubeHaarParity (InteriorState)
open FourCubeIntegratedCubic FourCubePinnedHaar FourCubePinnedCoercivity
open FourCubeHemisphereCoercivity FourCubeHaarQuadraticLimit FourCubePinnedSecondVariation
open FourCubeScaledBoundaryControl SU2FourCurveJetTransfer

def boundaryVector (x y z : ℝ) : Boundary → Fin 3 → ℝ
  | .inl c => if c.val=(capHigh chosen).val then SU2AxisMatrixJets.axisVector 0 x else
      if c.val=(capLow chosen).val then SU2AxisMatrixJets.axisVector 2 (-z) else 0
  | .inr p => if p.val=chosen.val then SU2AxisMatrixJets.axisVector 1 (-y) else 0

def boundaryCurve (x y z : ℝ) (c : Boundary) (t : ℝ) : M2 :=
  (movingBoundary t x y z c : M2)

private theorem boundary_alternative (x y z : ℝ) (c : Boundary) :
    (∃ (a : Fin 3) (r : ℝ),boundaryCurve x y z c=SU2AxisMatrixJets.curve a r ∧
      boundaryVector x y z c=SU2AxisMatrixJets.axisVector a r) ∨
    (boundaryCurve x y z c=(fun _ => (1 : M2)) ∧ boundaryVector x y z c=0) := by
  cases c with
  | inl c =>
    by_cases hh : c.val=(capHigh chosen).val
    · left
      exact ⟨0,x,by funext t; simp [boundaryCurve,movingBoundary,boundaryData,hh,SU2AxisMatrixJets.curve],
        by simp [boundaryVector,hh]⟩
    · by_cases hl : c.val=(capLow chosen).val
      · have hhl : (capLow chosen).val ≠ (capHigh chosen).val := by
          intro he
          exact hh (hl.trans he)
        left
        exact ⟨2,-z,by funext t; simp [boundaryCurve,movingBoundary,boundaryData,hh,hl,hhl,
          SU2AxisMatrixJets.curve,SU2AxisMatrixJets.axis_inv,mul_neg],by simp [boundaryVector,hh,hl,hhl]⟩
      · right
        constructor
        · funext t
          simp [boundaryCurve,movingBoundary,boundaryData,hh,hl]
        · simp [boundaryVector,hh,hl]
  | inr p =>
    by_cases hh : p.val=chosen.val
    · left
      exact ⟨1,-y,by funext t; simp [boundaryCurve,movingBoundary,boundaryData,hh,
        SU2AxisMatrixJets.curve,SU2AxisMatrixJets.axis_inv,mul_neg],by simp [boundaryVector,hh]⟩
    · right
      constructor
      · funext t
        simp [boundaryCurve,movingBoundary,boundaryData,hh]
      · simp [boundaryVector,hh]

theorem boundary_jets (x y z : ℝ) (c : Boundary) :
    ContDiff ℝ 2 (boundaryCurve x y z c) ∧ boundaryCurve x y z c 0=1 ∧
      deriv (boundaryCurve x y z c) 0=algebraElement (boundaryVector x y z c) ∧
      deriv (deriv (boundaryCurve x y z c)) 0=(algebraElement (boundaryVector x y z c))^2 := by
  rcases boundary_alternative x y z c with ⟨a,r,he,hv⟩ | ⟨he,hv⟩
  · rw [he,hv]
    exact ⟨SU2AxisMatrixJets.curve_contDiff a r,SU2AxisMatrixJets.curve_zero a r,
      SU2AxisMatrixJets.curve_first_zero a r,SU2AxisMatrixJets.curve_second_zero a r⟩
  · rw [he,hv]
    have hc : (fun _ : ℝ => (1 : M2))=SU2AxisMatrixJets.curve 0 0 := by
      funext t
      rw [SU2AxisMatrixJets.curve,SU2AxisMatrixJets.axis_matrix_formula]
      simp
    have hz : (0 : Fin 3 → ℝ)=SU2AxisMatrixJets.axisVector 0 0 := by
      ext i
      fin_cases i <;> norm_num [SU2AxisMatrixJets.axisVector]
    rw [hc,hz]
    exact ⟨SU2AxisMatrixJets.curve_contDiff 0 0,SU2AxisMatrixJets.curve_zero 0 0,
      SU2AxisMatrixJets.curve_first_zero 0 0,SU2AxisMatrixJets.curve_second_zero 0 0⟩

def ribbonVectors (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) (p : Upper) : Fin 4 → Fin 3 → ℝ :=
  ![SU2HemisphereJets.frame (liftVelocity Y (ribbonInterior p)),
    boundaryVector x y z (.inl (capHigh p)),boundaryVector x y z (.inr p),
    boundaryVector x y z (.inl (capLow p))]

def ribbonPath (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) (p : Upper) (t : ℝ) : WordField :=
  ![ratioPath Y t (ribbonInterior p),boundaryCurve x y z (.inl (capHigh p)) t,
    boundaryCurve x y z (.inr p) t,boundaryCurve x y z (.inl (capLow p)) t]

theorem ribbon_jets (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) (p : Upper) :
    ContDiff ℝ 2 (traceAction ∘ ribbonPath Y x y z p) ∧
      deriv (traceAction ∘ ribbonPath Y x y z p) 0=0 ∧
      deriv (deriv (traceAction ∘ ribbonPath Y x y z p)) 0=
        lengthSq (ribbonVectors Y x y z p 0+ribbonVectors Y x y z p 1-
          ribbonVectors Y x y z p 2-ribbonVectors Y x y z p 3)/4 := by
  apply trace_component_jets (ribbonPath Y x y z p) (ribbonVectors Y x y z p)
  · intro i
    fin_cases i
    · exact (_root_.contDiff_apply ℝ M2 (ribbonInterior p)).comp (ratioPath_contDiff Y)
    · exact (boundary_jets x y z (.inl (capHigh p))).1
    · exact (boundary_jets x y z (.inr p)).1
    · exact (boundary_jets x y z (.inl (capLow p))).1
  · intro i
    fin_cases i
    · exact SU2HemisphereJets.curve_zero (liftVelocity Y (ribbonInterior p))
    · exact (boundary_jets x y z (.inl (capHigh p))).2.1
    · exact (boundary_jets x y z (.inr p)).2.1
    · exact (boundary_jets x y z (.inl (capLow p))).2.1
  · intro i
    fin_cases i
    · exact SU2HemisphereJets.curve_first_zero (liftVelocity Y (ribbonInterior p))
    · exact (boundary_jets x y z (.inl (capHigh p))).2.2.1
    · exact (boundary_jets x y z (.inr p)).2.2.1
    · exact (boundary_jets x y z (.inl (capLow p))).2.2.1
  · intro i
    fin_cases i
    · exact SU2HemisphereJets.curve_second_generator (liftVelocity Y (ribbonInterior p))
    · exact (boundary_jets x y z (.inl (capHigh p))).2.2.2
    · exact (boundary_jets x y z (.inr p)).2.2.2
    · exact (boundary_jets x y z (.inl (capLow p))).2.2.2

theorem ratio_coordinate_actual (Y : FourCubeHemisphereCoercivity.Field) (t : ℝ) (e : Interior) :
    ratioPath Y t e=(fillPole 1 (chartField (t • Y)) e : M2) := by
  by_cases hp : e=OneSidedPinnedInterior.pole
  · subst e
    rw [show ratioPath Y t OneSidedPinnedInterior.pole=SU2HemisphereJets.curve 0 t by
      simp only [ratioPath,liftVelocity_pole]]
    simp only [SU2HemisphereJets.curve,smul_zero,fillPole,dite_true]
    convert! SU2HemisphereJets.curve_zero (0 : SU2GaussianConeCoordinates.Triple) using 1 <;>
      simp only [SU2HemisphereJets.curve,zero_smul]
  · change (SU2GaussianConeCoordinates.hemisphereChart (t • liftVelocity Y (⟨e,hp⟩ : OneSidedPinnedInterior.Free).val) : M2)=_
    rw [liftVelocity_free]
    simp only [fillPole,dif_neg hp,chartField,Pi.smul_apply]

def ribbonAction (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) (p : Upper) (t : ℝ) : ℝ :=
  defect (fillPole 1 (chartField (t • Y)) (ribbonInterior p)*word (movingBoundary t x y z) p)

theorem ribbon_model (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) (p : Upper) (t : ℝ) :
    traceAction (ribbonPath Y x y z p t)=ribbonAction Y x y z p t := by
  unfold traceAction ribbonPath ribbonAction defect word halfTrace
  change 1-traceReal (ratioPath Y t (ribbonInterior p)*
    (movingBoundary t x y z (.inl (capHigh p)) : M2)*
    (movingBoundary t x y z (.inr p) : M2)ᴴ*
    (movingBoundary t x y z (.inl (capLow p)) : M2)ᴴ)/2=_
  rw [ratio_coordinate_actual]
  simp only [← Matrix.star_eq_inv,Submonoid.coe_mul,Matrix.specialUnitaryGroup.coe_star,Matrix.star_eq_conjTranspose,mul_assoc]

def ribbonQuadratic (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) (p : Upper) : ℝ :=
  lengthSq (ribbonVectors Y x y z p 0+ribbonVectors Y x y z p 1-
    ribbonVectors Y x y z p 2-ribbonVectors Y x y z p 3)/4

theorem ribbon_action_jets (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) (p : Upper) :
    ContDiff ℝ 2 (ribbonAction Y x y z p) ∧ deriv (ribbonAction Y x y z p) 0=0 ∧
      deriv (deriv (ribbonAction Y x y z p)) 0=ribbonQuadratic Y x y z p := by
  have he : traceAction ∘ ribbonPath Y x y z p=ribbonAction Y x y z p := funext (ribbon_model Y x y z p)
  simpa only [he,ribbonQuadratic] using ribbon_jets Y x y z p

end OperatorDerivativeRewrite.Foundation.FourCubeMovingBoundaryQuadratic
