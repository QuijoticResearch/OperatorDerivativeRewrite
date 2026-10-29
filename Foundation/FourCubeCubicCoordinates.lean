import Foundation.FourCubeOddFullPartition

/-! Explicit raw-quaternion coordinates for the verified actual full-cell cubic. -/
noncomputable section
open scoped Topology Quaternion Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubeCubicCoordinates
open QuaternionSU2Representation SU2TraceHessianModel SU2MatrixExponentialBridge
open SU2QuaternionOddWord FourCubeMovingOddAction FourCubeMovingBoundaryQuadratic
open FourCubePinnedSecondVariation OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex
open OneSidedSourceRows ChristoffelSkewCancellation
attribute [local irreducible] edges upperFaces innerFaces

def rawBoundary (x y z : ℝ) (c : Boundary) : Vector :=
  ![boundaryVector x y z c 2/2,boundaryVector x y z c 0/2,boundaryVector x y z c 1/2]

def vectorVelocity (Y : Coordinates) (x y z : ℝ) : FullEdge → Vector
  | .inl e => liftVelocity Y e
  | .inr c => rawBoundary x y z c

def vectors (Y : Coordinates) (x y z : ℝ) (p : FullFace) : Fin 4 → Vector :=
  ![vectorVelocity Y x y z (rowEdges p 0),vectorVelocity Y x y z (rowEdges p 1),
    -vectorVelocity Y x y z (rowEdges p 2),-vectorVelocity Y x y z (rowEdges p 3)]

theorem algebra_quaternion (v : Fin 3 → ℝ) :
    imagVector (recover (algebraElement v))= ![v 2/2,v 0/2,v 1/2] := by
  ext a
  fin_cases a <;> norm_num [imagVector,recover,algebraElement,tangent,SU2TraceHessianModel.generator,
    generatorX,generatorY,generatorZ,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im] <;> ring

theorem generator_quaternion (u : SU2GaussianConeCoordinates.Triple) :
    imagVector (recover (SU2HemisphereJets.generator u))=u := by
  rw [SU2HemisphereJets.generator,algebra_quaternion]
  ext a
  fin_cases a <;> simp [SU2HemisphereJets.frame]

theorem velocity_quaternion (Y : Coordinates) (x y z : ℝ) (e : FullEdge) :
    imagVector (recover (velocity Y x y z e))=vectorVelocity Y x y z e := by
  cases e with
  | inl e => exact generator_quaternion _
  | inr c => exact algebra_quaternion _

theorem velocity_skew (Y : Coordinates) (x y z : ℝ) (e : FullEdge) :
    (velocity Y x y z e)ᴴ= -velocity Y x y z e := by
  cases e with
  | inl e => exact algebraElement_skewHermitian _
  | inr c => exact algebraElement_skewHermitian _

theorem imag_recover_neg (M : M2) : imagVector (recover (-M))= -imagVector (recover M) := by
  ext a
  fin_cases a <;> simp [imagVector,recover]

theorem slopes_quaternion (Y : Coordinates) (x y z : ℝ) (p : FullFace) :
    (fun i => imagVector (recover (slopes (velocity Y x y z) p i)))=vectors Y x y z p := by
  funext i
  fin_cases i
  · exact velocity_quaternion Y x y z _
  · exact velocity_quaternion Y x y z _
  · change imagVector (recover ((velocity Y x y z (rowEdges p 2))ᴴ))= -vectorVelocity Y x y z (rowEdges p 2)
    rw [velocity_skew,imag_recover_neg,velocity_quaternion]
  · change imagVector (recover ((velocity Y x y z (rowEdges p 3))ᴴ))= -vectorVelocity Y x y z (rowEdges p 3)
    rw [velocity_skew,imag_recover_neg,velocity_quaternion]

theorem cubicCoefficient_vectors (Y : Coordinates) (x y z : ℝ) :
    cubicCoefficient Y x y z=∑ p : FullFace,cubic (vectors Y x y z p) := by
  unfold cubicCoefficient
  simp only [slopes_quaternion]

end OperatorDerivativeRewrite.Foundation.FourCubeCubicCoordinates
