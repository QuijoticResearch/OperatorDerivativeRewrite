import Foundation.FourCubeHarmonicCubicValue

/-! Exact amplitude dependence of the actual harmonic cubic, with no derivative interchange. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeHarmonicAmplitude
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedPinnedInterior
open FourCubeMovingSchurLimit FourCubeMovingBoundaryQuadratic FourCubeCubicCoordinates
open FourCubeMovingOddAction FourCubePinnedSecondVariation FourCubeCubicIntegral
open FourCubeHarmonicCubicValue SU2QuaternionOddWord

def amplitude (x y z : ℝ) : Vector := ![x,y,z]

def scale (x y z : ℝ) (Y : Coordinates) : Coordinates :=
  fun e a => amplitude x y z a*Y e a

theorem raw_boundary_scale (x y z : ℝ) (c : Boundary) (a : Fin 3) :
    rawBoundary x y z c a=amplitude x y z a*rawBoundary 1 1 1 c a := by
  cases c <;> fin_cases a <;>
    simp only [rawBoundary,boundaryVector] <;> split_ifs <;>
    norm_num [amplitude,SU2AxisMatrixJets.axisVector] <;> ring

theorem boundary_component_scale (x y z : ℝ) (a : Fin 3) :
    boundaryComponent x y z a=(![y,z,x] a : ℝ) • boundaryComponent 1 1 1 a := by
  funext c
  cases c <;> fin_cases a <;>
    simp only [boundaryComponent,boundaryVector,Pi.smul_apply,smul_eq_mul] <;> split_ifs <;>
    norm_num [SU2AxisMatrixJets.axisVector] <;> ring

theorem response_smul (r : ℝ) (eta : OneSidedBoundaryGauge.BoundaryField) :
    OneSidedSchurForm.response (r • eta)=r • OneSidedSchurForm.response eta := by
  unfold OneSidedSchurForm.response
  simp only [Matrix.mulVec_smul,smul_neg]

theorem harmonic_scale (x y z : ℝ) : harmonicShift x y z=scale x y z (harmonicShift 1 1 1) := by
  funext e a
  fin_cases a
  · change OneSidedSchurForm.response (boundaryComponent x y z 2) e/2=
      x*(OneSidedSchurForm.response (boundaryComponent 1 1 1 2) e/2)
    rw [boundary_component_scale x y z 2,response_smul]
    change (x*OneSidedSchurForm.response (boundaryComponent 1 1 1 2) e)/2=_
    ring
  · change OneSidedSchurForm.response (boundaryComponent x y z 0) e/2=
      y*(OneSidedSchurForm.response (boundaryComponent 1 1 1 0) e/2)
    rw [boundary_component_scale x y z 0,response_smul]
    change (y*OneSidedSchurForm.response (boundaryComponent 1 1 1 0) e)/2=_
    ring
  · change OneSidedSchurForm.response (boundaryComponent x y z 1) e/2=
      z*(OneSidedSchurForm.response (boundaryComponent 1 1 1 1) e/2)
    rw [boundary_component_scale x y z 1,response_smul]
    change (z*OneSidedSchurForm.response (boundaryComponent 1 1 1 1) e)/2=_
    ring

theorem velocity_scale (x y z : ℝ) (Y : Coordinates) (e : FullEdge) (a : Fin 3) :
    vectorVelocity (scale x y z Y) x y z e a=
      amplitude x y z a*vectorVelocity Y 1 1 1 e a := by
  cases e with
  | inl e =>
    by_cases hp : e=pole
    · subst e
      simp [vectorVelocity,liftVelocity_pole]
    · have hl (Z : Coordinates) : liftVelocity Z e=Z (⟨e,hp⟩ : Free) := liftVelocity_free Z ⟨e,hp⟩
      simp only [vectorVelocity,hl,scale]
  | inr c => exact raw_boundary_scale x y z c a

theorem vectors_scale (x y z : ℝ) (Y : Coordinates) (p : FullFace) :
    vectors (scale x y z Y) x y z p=(fun i a => amplitude x y z a*vectors Y 1 1 1 p i a) := by
  funext i a
  fin_cases i
  · exact velocity_scale x y z Y _ a
  · exact velocity_scale x y z Y _ a
  · change -vectorVelocity (scale x y z Y) x y z (OneSidedSourceRows.rowEdges p 2) a=
      amplitude x y z a*(-vectorVelocity Y 1 1 1 (OneSidedSourceRows.rowEdges p 2) a)
    rw [velocity_scale]
    ring
  · change -vectorVelocity (scale x y z Y) x y z (OneSidedSourceRows.rowEdges p 3) a=
      amplitude x y z a*(-vectorVelocity Y 1 1 1 (OneSidedSourceRows.rowEdges p 3) a)
    rw [velocity_scale]
    ring

theorem triple_scale (x y z : ℝ) (u v w : Vector) :
    triple (fun a => amplitude x y z a*u a) (fun a => amplitude x y z a*v a)
      (fun a => amplitude x y z a*w a)=x*y*z*triple u v w := by
  simp only [triple,amplitude,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  ring

theorem cubic_scale (x y z : ℝ) (w : Fin 4 → Vector) :
    cubic (fun i a => amplitude x y z a*w i a)=x*y*z*cubic w := by
  unfold cubic weightedCubic
  simp only [one_mul,triple_scale]
  ring

theorem coefficient_scale (x y z : ℝ) (Y : Coordinates) :
    cubicCoefficient (scale x y z Y) x y z=x*y*z*cubicCoefficient Y 1 1 1 := by
  simp_rw [cubicCoefficient_vectors,vectors_scale,cubic_scale]
  rw [Finset.mul_sum]

theorem harmonic_amplitudes (x y z : ℝ) :
    harmonicCubic x y z=((31877443263 : ℝ)/69438734552)*x*y*z := by
  rw [harmonicCubic,harmonic_scale,coefficient_scale]
  change x*y*z*harmonicCubic 1 1 1=_
  rw [harmonic_cubic_value]
  ring

end OperatorDerivativeRewrite.Foundation.FourCubeHarmonicAmplitude
