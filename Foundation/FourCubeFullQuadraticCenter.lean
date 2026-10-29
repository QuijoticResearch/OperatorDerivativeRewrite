import Foundation.FourCubeCompletedSquare
import Foundation.FourCubeHarmonicAmplitude
import Foundation.FourCubeCompletedCubic

/-! Identify the actual full32 chart quadratic with its raw-color incidence
energy and certified center. No31-variable pin or assumed Gaussian mean is used. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullQuadraticCenter
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedBoundaryGauge
open OneSidedEffectiveCurvature OneSidedPinnedInterior OneSidedPhysicalProjection OneSidedSourceRows
open SU2GaussianConeCoordinates SU2MatrixExponentialBridge
open FourCubeFullChartOdd FourCubeFullChartQuadratic FourCubeCompletedSquare

attribute [local irreducible] edges innerFaces upperFaces

def interiorColor (Y : Coordinates) (a : Fin 3) : Field := fun e => Y e a
def boundaryColor (x y z : ℝ) (a : Fin 3) : BoundaryField :=
  fun c => FourCubeCubicCoordinates.rawBoundary x y z c a
def scalarField (Y : Coordinates) (x y z : ℝ) (a : Fin 3) : FullField :=
  Sum.elim (interiorColor Y a) (boundaryColor x y z a)

theorem scalar_raw (Y : Coordinates) (x y z : ℝ) (a : Fin 3) (e : FullEdge) :
    scalarField Y x y z a e=rawVelocity Y x y z e a := by cases e <;> rfl

theorem scalar_incidence (f : Field) (eta : BoundaryField) :
    FourCubeCompletedSquare.residual f eta=faceCurl (Sum.elim f eta) := by
  rw [FourCubeCompletedSquare.residual,fullMatrix_mulVec,boundaryMatrix_mulVec]
  change flatten (incidence f)+flatten (boundaryCurl eta)=flatten (d1 (Sum.elim f eta))
  rw [d1_split,map_add]
  rfl

theorem residual_color (Y : Coordinates) (x y z : ℝ) (a : Fin 3) :
    FourCubeCompletedSquare.residual (interiorColor Y a) (boundaryColor x y z a)=faceCurl (scalarField Y x y z a) :=
  scalar_incidence _ _

theorem frame_row (u v w r : Triple) :
    SU2HemisphereJets.frame (u+v-w-r)=
      SU2HemisphereJets.frame u+SU2HemisphereJets.frame v-
        SU2HemisphereJets.frame w-SU2HemisphereJets.frame r := by
  ext a
  fin_cases a <;> simp [SU2HemisphereJets.frame] <;> ring

theorem frame_length (u : Triple) : lengthSq (SU2HemisphereJets.frame u)/4=SU2HemisphereJets.sizeSq u := by
  norm_num [lengthSq,SU2HemisphereJets.frame,SU2HemisphereJets.sizeSq,Fin.sum_univ_three]
  ring

theorem pauli_raw (Y : Coordinates) (x y z : ℝ) (e : FullEdge) :
    pauliVelocity Y x y z e=SU2HemisphereJets.frame (rawVelocity Y x y z e) := by
  cases e with
  | inl e => rfl
  | inr c =>
    ext a
    fin_cases a <;> simp [pauliVelocity,rawVelocity,FourCubeCubicCoordinates.rawBoundary,SU2HemisphereJets.frame] <;> ring

theorem face_raw (Y : Coordinates) (x y z : ℝ) (p : FullFace) :
    faceQuadratic Y x y z p=∑ a : Fin 3,(faceCurl (scalarField Y x y z a) p)^2 := by
  unfold faceQuadratic
  simp_rw [pauli_raw]
  rw [← frame_row,frame_length]
  simp_rw [row_formula,scalar_raw]
  simp [SU2HemisphereJets.sizeSq,Fin.sum_univ_three]

theorem native_colors (Y : Coordinates) (x y z : ℝ) :
    nativeQuadratic Y x y z=∑ a : Fin 3,
      dotProduct (FourCubeCompletedSquare.residual (interiorColor Y a) (boundaryColor x y z a))
        (FourCubeCompletedSquare.residual (interiorColor Y a) (boundaryColor x y z a)) := by
  unfold nativeQuadratic
  simp_rw [face_raw]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [residual_color]
  simp only [dotProduct,pow_two]

theorem size_sum (u : Triple) : SU2HemisphereJets.sizeSq u=∑ a : Fin 3,(u a)^2 := by
  simp [SU2HemisphereJets.sizeSq,Fin.sum_univ_three]

theorem diagonal_colors (Y : Coordinates) :
    diagonalQuadratic Y=∑ a : Fin 3,FourCubeCompletedGram.penalty (interiorColor Y a) := by
  unfold diagonalQuadratic
  simp_rw [size_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

/-- Exact actual-Hessian bridge in all three raw colors. -/
theorem quadratic_colors (Y : Coordinates) (x y z : ℝ) :
    completedQuadratic Y x y z=∑ a : Fin 3,energy (interiorColor Y a) (boundaryColor x y z a) := by
  rw [completedQuadratic,native_colors,diagonal_colors,← Finset.sum_add_distrib]
  rfl

def center (x y z : ℝ) : Coordinates :=
  fun e a => FourCubeHarmonicAmplitude.amplitude x y z a*FourCubeCompletedResponse.candidate a e

def fluctuation (Y : Coordinates) : ℝ :=
  ∑ a : Fin 3,FourCubeCompletedGram.quadratic (interiorColor Y a)

theorem boundary_unit (a : Fin 3) : boundaryColor 1 1 1 a=FourCubeCompletedResponse.eta a := by
  funext c
  exact congrFun (FourCubeHarmonicResponse.raw_boundary_unit c) a

theorem boundary_scaled (x y z : ℝ) (a : Fin 3) :
    boundaryColor x y z a=FourCubeHarmonicAmplitude.amplitude x y z a • FourCubeCompletedResponse.eta a := by
  funext c
  change FourCubeCubicCoordinates.rawBoundary x y z c a=_
  rw [FourCubeHarmonicAmplitude.raw_boundary_scale]
  have h := congrFun (boundary_unit a) c
  change FourCubeCubicCoordinates.rawBoundary 1 1 1 c a=FourCubeCompletedResponse.eta a c at h
  rw [h]
  rfl

theorem center_color (x y z : ℝ) (a : Fin 3) :
    interiorColor (center x y z) a=
      FourCubeHarmonicAmplitude.amplitude x y z a • FourCubeCompletedResponse.candidate a := rfl

theorem center_normal (x y z : ℝ) (a : Fin 3) :
    FourCubeCompletedGram.gram.mulVec (interiorColor (center x y z) a)+
      coupling (boundaryColor x y z a)=0 := by
  rw [center_color,boundary_scaled,Matrix.mulVec_smul]
  have hk (r : ℝ) (eta : BoundaryField) : coupling (r • eta)=r • coupling eta := by
    simp only [coupling,Matrix.mulVec_smul]
  rw [hk,← smul_add,candidate_normal,smul_zero]

/-- The actual full32 quadratic is centered at the verified unpinned response. -/
theorem centered_energy (Y : Coordinates) (x y z : ℝ) :
    completedQuadratic Y x y z=completedQuadratic (center x y z) x y z+
      fluctuation (Y-center x y z) := by
  rw [quadratic_colors,quadratic_colors]
  calc
    _ = ∑ a : Fin 3,(energy (interiorColor (center x y z) a) (boundaryColor x y z a)+
        FourCubeCompletedGram.quadratic (interiorColor Y a-interiorColor (center x y z) a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact completed_square _ _ _ (center_normal x y z a)
    _ = _ := by rw [Finset.sum_add_distrib]; rfl

theorem fluctuation_nonneg (Y : Coordinates) : 0 ≤ fluctuation Y :=
  Finset.sum_nonneg (fun a _ => FourCubeCompletedGram.quadratic_nonneg _)

theorem fluctuation_zero_iff (Y : Coordinates) : fluctuation Y=0 ↔ Y=0 := by
  constructor
  · intro h
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a (_ : a∈Finset.univ) => FourCubeCompletedGram.quadratic_nonneg (interiorColor Y a))).mp h
    funext e a
    have ha := (FourCubeCompletedGram.quadratic_zero_iff (interiorColor Y a)).mp (hs a (Finset.mem_univ a))
    exact congrFun ha e
  · intro h
    rw [h]
    apply Finset.sum_eq_zero
    intro a ha
    exact (FourCubeCompletedGram.quadratic_zero_iff _).mpr rfl

theorem unique_center (Y : Coordinates) (x y z : ℝ) :
    completedQuadratic Y x y z=completedQuadratic (center x y z) x y z ↔ Y=center x y z := by
  rw [centered_energy,add_eq_left,fluctuation_zero_iff,sub_eq_zero]

theorem center_unit : center 1 1 1=FourCubeCompletedCubic.field := by
  ext e a
  fin_cases a <;> simp [center,FourCubeHarmonicAmplitude.amplitude,FourCubeCompletedCubic.field]

end OperatorDerivativeRewrite.Foundation.FourCubeFullQuadraticCenter
