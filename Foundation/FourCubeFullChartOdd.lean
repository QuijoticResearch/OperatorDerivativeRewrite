import Foundation.FourCubeCompletedResponse
import Foundation.FourCubeHarmonicCubicValue

/-! Actual full32 Haar-chart paths and their pointwise odd action limit.
No integration/limit exchange or physical mass-gap assertion occurs here. -/
noncomputable section
open Filter Set
open scoped Topology Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullChartOdd
open QuaternionSU2Representation SU2TraceHessianModel SU2MatrixExponentialBridge
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedSourceRows
open FourCubeHaarParity FourCubeIntegratedCubic FourCubeScaledBoundaryControl
open FourCubeMovingBoundaryQuadratic SU2GaussianConeCoordinates SU2HemisphereChart
open SU2QuaternionOddWord

abbrev Coordinates := Interior → Triple

def state (Y : Coordinates) (t : ℝ) : InteriorState := fun e => hemisphereChart (t • Y e)
def links (Y : Coordinates) (x y z t : ℝ) : FullEdge → SU2 :=
  fill (movingBoundary t x y z) (state Y t)
def velocity (Y : Coordinates) (x y z : ℝ) : FullEdge → M2
  | .inl e => SU2HemisphereJets.generator (Y e)
  | .inr c => algebraElement (boundaryVector x y z c)

def rawVelocity (Y : Coordinates) (x y z : ℝ) : FullEdge → Vector
  | .inl e => Y e
  | .inr c => FourCubeCubicCoordinates.rawBoundary x y z c

def vectors (Y : Coordinates) (x y z : ℝ) (p : FullFace) : Fin 4 → Vector :=
  ![rawVelocity Y x y z (rowEdges p 0),rawVelocity Y x y z (rowEdges p 1),
    -rawVelocity Y x y z (rowEdges p 2),-rawVelocity Y x y z (rowEdges p 3)]

def cubicCoefficient (Y : Coordinates) (x y z : ℝ) : ℝ :=
  ∑ p : FullFace,cubic (vectors Y x y z p)

def nativeRay (Y : Coordinates) (x y z t : ℝ) : ℝ :=
  FourCubeBoundaryCubic.fullAction (links Y x y z t)
def completedRay (Y : Coordinates) (x y z t : ℝ) : ℝ :=
  FourCubeCompletedHaar.completedAction (FourCubeCompletedHaar.angles (t*x) (t*y) (t*z)) (state Y t)
def standardRay (Y : Coordinates) (x y z t : ℝ) : ℝ :=
  FourCubeDirichletBox.action (FourCubeCompletedHaar.angles (t*x) (t*y) (t*z)) (state Y t)

theorem chart_parity (u : Triple) (t : ℝ) :
    SU2HemisphereJets.curve u (-t)=(SU2HemisphereJets.curve u t)ᴴ := by
  rw [SU2HemisphereJets.curve_formula,SU2HemisphereJets.curve_formula]
  have hw : SU2HemisphereJets.weight u (-t)=SU2HemisphereJets.weight u t := by
    simp [SU2HemisphereJets.weight]
  rw [hw]
  simp [SU2HemisphereJets.affine,Matrix.conjTranspose_smul,Matrix.conjTranspose_add,
    SU2HemisphereJets.generator,algebraElement_skewHermitian,neg_smul,smul_neg]

theorem links_zero (Y : Coordinates) (x y z : ℝ) (e : FullEdge) : links Y x y z 0 e=1 := by
  apply Subtype.ext
  cases e with
  | inl e => exact SU2HemisphereJets.curve_zero _
  | inr c => exact (boundary_jets x y z c).2.1

theorem links_hasDerivAt (Y : Coordinates) (x y z : ℝ) (e : FullEdge) :
    HasDerivAt (fun t : ℝ => (links Y x y z t e : M2)) (velocity Y x y z e) 0 := by
  cases e with
  | inl e =>
    change HasDerivAt (SU2HemisphereJets.curve (Y e)) (SU2HemisphereJets.generator (Y e)) 0
    convert! SU2HemisphereJets.curve_hasDerivAt (Y e) 0 using 1 <;>
      simp [SU2HemisphereJets.curveSlope,SU2HemisphereJets.weightSlope,
        SU2HemisphereJets.weight_zero,SU2HemisphereJets.affine]
  | inr c =>
    have hh : HasDerivAt (boundaryCurve x y z c) (deriv (boundaryCurve x y z c) 0) 0 :=
      ((boundary_jets x y z c).1.differentiable (by norm_num)).differentiableAt.hasDerivAt
    rw [(boundary_jets x y z c).2.2.1] at hh
    exact hh

theorem links_parity (Y : Coordinates) (x y z t : ℝ) (e : FullEdge) :
    links Y x y z (-t) e=(links Y x y z t e)⁻¹ := by
  cases e with
  | inl e =>
    apply Subtype.ext
    exact chart_parity (Y e) t
  | inr c =>
    cases c <;> simp only [links,fill,movingBoundary,boundaryData] <;>
      split_ifs <;> simp [SU2AxisMatrixJets.axis_inv,neg_mul]

theorem factors_zero (Y : Coordinates) (x y z : ℝ) (p : FullFace) (i : Fin 4) :
    FourCubeMovingOddAction.factors (links Y x y z 0) p i=1 := by
  fin_cases i <;> simp [FourCubeMovingOddAction.factors,links_zero]

theorem factors_parity (Y : Coordinates) (x y z t : ℝ) (p : FullFace) (i : Fin 4) :
    FourCubeMovingOddAction.factors (links Y x y z (-t)) p i=
      (FourCubeMovingOddAction.factors (links Y x y z t) p i)⁻¹ := by
  fin_cases i <;> simp [FourCubeMovingOddAction.factors,links_parity]

theorem factors_hasDerivAt (Y : Coordinates) (x y z : ℝ) (p : FullFace) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => (FourCubeMovingOddAction.factors (links Y x y z t) p i : M2))
      (FourCubeMovingOddAction.slopes (velocity Y x y z) p i) 0 := by
  fin_cases i
  · exact links_hasDerivAt Y x y z _
  · exact links_hasDerivAt Y x y z _
  · exact FourCubeAmbientAction.adjointCLM.hasFDerivAt.comp_hasDerivAt 0 (links_hasDerivAt Y x y z _)
  · exact FourCubeAmbientAction.adjointCLM.hasFDerivAt.comp_hasDerivAt 0 (links_hasDerivAt Y x y z _)

theorem velocity_quaternion (Y : Coordinates) (x y z : ℝ) (e : FullEdge) :
    imagVector (recover (velocity Y x y z e))=rawVelocity Y x y z e := by
  cases e with
  | inl e => exact FourCubeCubicCoordinates.generator_quaternion _
  | inr c => exact FourCubeCubicCoordinates.algebra_quaternion _

theorem velocity_skew (Y : Coordinates) (x y z : ℝ) (e : FullEdge) :
    (velocity Y x y z e)ᴴ= -velocity Y x y z e := by
  cases e <;> exact algebraElement_skewHermitian _

theorem slopes_quaternion (Y : Coordinates) (x y z : ℝ) (p : FullFace) :
    (fun i => imagVector (recover (FourCubeMovingOddAction.slopes (velocity Y x y z) p i)))=
      vectors Y x y z p := by
  funext i
  fin_cases i
  · exact velocity_quaternion Y x y z _
  · exact velocity_quaternion Y x y z _
  · change imagVector (recover ((velocity Y x y z (rowEdges p 2))ᴴ))= -rawVelocity Y x y z _
    rw [velocity_skew,FourCubeCubicCoordinates.imag_recover_neg,velocity_quaternion]
  · change imagVector (recover ((velocity Y x y z (rowEdges p 3))ᴴ))= -rawVelocity Y x y z _
    rw [velocity_skew,FourCubeCubicCoordinates.imag_recover_neg,velocity_quaternion]

/-- Actual pointwise action limit on all32 chart links; not a Haar integral limit. -/
theorem native_odd_limit (Y : Coordinates) (x y z : ℝ) :
    Tendsto (fun t : ℝ => (nativeRay Y x y z t-nativeRay Y x y z (-t))/(2*t^3))
      (𝓝[≠] 0) (𝓝 (cubicCoefficient Y x y z)) := by
  have hh := tendsto_finsetSum Finset.univ (fun p _ =>
    matrix_word_odd_limit (fun t => FourCubeMovingOddAction.factors (links Y x y z t) p)
      (FourCubeMovingOddAction.slopes (velocity Y x y z) p)
      (factors_zero Y x y z p) (fun t => factors_parity Y x y z t p)
      (factors_hasDerivAt Y x y z p))
  simp_rw [slopes_quaternion] at hh
  apply hh.congr'
  filter_upwards with t
  rw [nativeRay,nativeRay,FourCubeMovingOddAction.fullAction_rows,
    FourCubeMovingOddAction.fullAction_rows,← Finset.sum_sub_distrib,Finset.sum_div]

theorem diagonal_even (Y : Coordinates) (t : ℝ) :
    FourCubeCompletedHaar.diagonal (state Y (-t))=FourCubeCompletedHaar.diagonal (state Y t) := by
  apply Finset.sum_congr rfl
  intro e he
  have hp := links_parity Y 0 0 0 t (.inl e)
  change state Y (-t) e=(state Y t e)⁻¹ at hp
  rw [hp,FourCubePinnedCoercivity.defect_inv]

theorem completed_native (Y : Coordinates) (x y z t : ℝ) :
    completedRay Y x y z t=nativeRay Y x y z t+FourCubeCompletedHaar.diagonal (state Y t) := by
  rw [completedRay,FourCubeCompletedHaar.completedAction,FourCubeCompletedHaar.angles,
    FourCubeNativeTransport.native_angles]
  rfl

theorem standard_completed (Y : Coordinates) (x y z t : ℝ) :
    standardRay Y x y z t=completedRay Y x y z t+
      FourCubeCompletedHaar.sourceCost (FourCubeCompletedHaar.angles (t*x) (t*y) (t*z)) :=
  FourCubeCompletedHaar.action_split _ _

theorem completed_odd_identity (Y : Coordinates) (x y z t : ℝ) :
    completedRay Y x y z t-completedRay Y x y z (-t)=
      nativeRay Y x y z t-nativeRay Y x y z (-t) := by
  rw [completed_native,completed_native,diagonal_even]
  ring

theorem standard_odd_identity (Y : Coordinates) (x y z t : ℝ) :
    standardRay Y x y z t-standardRay Y x y z (-t)=
      nativeRay Y x y z t-nativeRay Y x y z (-t) := by
  rw [standard_completed,standard_completed]
  simp only [neg_mul,FourCubeCompletedHaar.sourceCost_reversal]
  rw [← completed_odd_identity]
  ring

theorem completed_odd_limit (Y : Coordinates) (x y z : ℝ) :
    Tendsto (fun t : ℝ => (completedRay Y x y z t-completedRay Y x y z (-t))/(2*t^3))
      (𝓝[≠] 0) (𝓝 (cubicCoefficient Y x y z)) := by
  simp_rw [completed_odd_identity]
  exact native_odd_limit Y x y z

theorem standard_odd_limit (Y : Coordinates) (x y z : ℝ) :
    Tendsto (fun t : ℝ => (standardRay Y x y z t-standardRay Y x y z (-t))/(2*t^3))
      (𝓝[≠] 0) (𝓝 (cubicCoefficient Y x y z)) := by
  simp_rw [standard_odd_identity]
  exact native_odd_limit Y x y z

end OperatorDerivativeRewrite.Foundation.FourCubeFullChartOdd
