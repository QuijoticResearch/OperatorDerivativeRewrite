import Foundation.FourCubeHarmonicResponse
import Foundation.FourCubeHarmonicWordData

/-! Exact nonzero harmonic cubic in the actual full-Haar odd free-energy limit. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeHarmonicCubicValue
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedSourceRows
open OneSidedPinnedInterior OneSidedSourceMatrixData OneSidedBoundaryCycleData
open OneSidedCertifiedResidual FourCubeHarmonicResponse FourCubeHarmonicWordData
open FourCubeCubicCoordinates FourCubeCubicIntegral FourCubeCubicFreeEnergy
open FourCubeMovingSchurLimit FourCubePinnedSecondVariation SU2QuaternionOddWord
open FourCubeScaledBoundaryControl

theorem lift_candidate (e : Interior) : liftVelocity chart e=(fun a => candidate a e) := by
  by_cases hp : e=pole
  · subst e
    ext a
    rw [liftVelocity_pole,candidate_pole]
    rfl
  · rw [liftVelocity_free chart (⟨e,hp⟩ : Free)]
    rfl

theorem velocity_point (e : Fin 32 ⊕ Fin 80) :
    vectorVelocity chart 1 1 1 (edgePoint e)=
      (fun a => (FourCubeHarmonicIntegerData.linkValue e a : ℝ)/d) := by
  cases e with
  | inl i =>
    ext a
    change liftVelocity chart (interiorPoint i) a=_
    rw [lift_candidate]
    exact candidate_point i a
  | inr k =>
    ext a
    change rawBoundary 1 1 1 (point k) a=_
    rw [raw_boundary_unit]
    simp only [FourCubeHarmonicIntegerData.boundary_sources,FourCubeHarmonicIntegerData.linkValue,Sum.elim_inr]
    push_cast
    field_simp [d_positive.ne']

theorem vectors_integer (p : Fin 72) :
    vectors chart 1 1 1 (facePoint p)=(fun i a => (word p i a : ℝ)/d) := by
  have hs : vectors chart 1 1 1 (facePoint p)=
      (fun i a => (OneSidedSparseSourceData.rowSign i : ℝ)*
        vectorVelocity chart 1 1 1 (rowEdges (facePoint p) i) a) := by
    funext i a
    fin_cases i <;> simp [vectors,OneSidedSparseSourceData.rowSign]
  rw [hs]
  funext i a
  rw [actual_rows,velocity_point]
  simp only [word,Int.cast_mul]
  ring

theorem cubic_real (w : Fin 4 → Fin 3 → ℤ) :
    cubic (fun i a => (w i a : ℝ)/d)=(cubicInt w : ℝ)/d^3 := by
  simp only [cubic,weightedCubic,one_mul,triple,cubicInt,det3]
  push_cast
  ring

theorem harmonic_cubic_value : harmonicCubic 1 1 1=(31877443263 : ℝ)/69438734552 := by
  rw [harmonicCubic,harmonic_eq_chart,FourCubeCubicCoordinates.cubicCoefficient_vectors]
  rw [← sum_faces (fun p => cubic (vectors chart 1 1 1 p))]
  simp_rw [vectors_integer,cubic_real]
  rw [← Finset.sum_div,← Int.cast_sum,cubic_total]
  norm_num [d,FourCubeHarmonicIntegerData.denominator]

theorem harmonic_cubic_positive : 0 < harmonicCubic 1 1 1 := by
  rw [harmonic_cubic_value]
  norm_num

theorem actual_free_energy_nonzero_limit :
    Tendsto (fun t : ℝ => (-Real.log (normalizedPartition (1/t^2) (movingBoundary t 1 1 1))+
      Real.log (normalizedPartition (1/t^2) (movingBoundary (-t) 1 1 1)))/(2*t)) (𝓝[≠] 0)
      (𝓝 ((31877443263 : ℝ)/69438734552)) := by
  simpa only [harmonic_cubic_value] using actual_freeEnergy_harmonic_odd_limit 1 1 1

end OperatorDerivativeRewrite.Foundation.FourCubeHarmonicCubicValue
