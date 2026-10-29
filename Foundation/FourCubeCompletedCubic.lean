import Foundation.FourCubeFullChartOdd

/-! Kernel-certified ordered cubic at the new unpinned full32 source solution.
The action limit below is pointwise; no full-Haar asymptotic is claimed. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeCompletedCubic
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedSourceRows
open OneSidedSourceMatrixData OneSidedBoundaryCycleData OneSidedSparseSourceData
open OneSidedCertifiedResidual FourCubeHarmonicWordData FourCubeFullChartOdd
open SU2QuaternionOddWord

attribute [local irreducible] edges innerFaces upperFaces

def field : Coordinates := fun e j => FourCubeCompletedResponse.candidate j e

def word (p : Fin 72) (i : Fin 4) (a : Fin 3) : ℤ :=
  OneSidedSparseSourceData.rowSign i*FourCubeCompletedIntegerData.linkValue (rowLink p (slot p i)) a

theorem cubic_total : (∑ p : Fin 72,cubicInt (word p))=5831513325 := by decide +kernel

theorem velocity_point (e : Fin 32 ⊕ Fin 80) :
    rawVelocity field 1 1 1 (edgePoint e)=
      (fun a => (FourCubeCompletedIntegerData.linkValue e a : ℝ)/FourCubeCompletedResponse.d) := by
  cases e with
  | inl i =>
    ext a
    exact FourCubeCompletedResponse.candidate_point i a
  | inr k =>
    ext a
    change FourCubeCubicCoordinates.rawBoundary 1 1 1 (point k) a=_
    rw [FourCubeHarmonicResponse.raw_boundary_unit]
    simp only [FourCubeHarmonicIntegerData.boundary_sources,
      FourCubeCompletedIntegerData.linkValue,Sum.elim_inr]
    push_cast
    field_simp [FourCubeCompletedResponse.d_positive.ne']

theorem vectors_integer (p : Fin 72) :
    vectors field 1 1 1 (facePoint p)=
      (fun i a => (word p i a : ℝ)/FourCubeCompletedResponse.d) := by
  have hs : vectors field 1 1 1 (facePoint p)=
      (fun i a => (OneSidedSparseSourceData.rowSign i : ℝ)*rawVelocity field 1 1 1 (rowEdges (facePoint p) i) a) := by
    funext i a
    fin_cases i <;> simp [vectors,OneSidedSparseSourceData.rowSign]
  rw [hs]
  funext i a
  rw [actual_rows,velocity_point]
  simp only [word,Int.cast_mul]
  ring

theorem cubic_real (w : Fin 4 → Fin 3 → ℤ) :
    cubic (fun i a => (w i a : ℝ)/FourCubeCompletedResponse.d)=
      (cubicInt w : ℝ)/FourCubeCompletedResponse.d^3 := by
  simp only [cubic,weightedCubic,one_mul,triple,cubicInt,det3]
  push_cast
  ring

theorem coefficient_value : cubicCoefficient field 1 1 1=(1784975 : ℝ)/2750517 := by
  rw [cubicCoefficient,← sum_faces (fun p => cubic (vectors field 1 1 1 p))]
  simp_rw [vectors_integer,cubic_real]
  rw [← Finset.sum_div,← Int.cast_sum,cubic_total]
  norm_num [FourCubeCompletedResponse.d,FourCubeCompletedIntegerData.denominator]

theorem coefficient_positive : 0<cubicCoefficient field 1 1 1 := by
  rw [coefficient_value]
  norm_num

/-- Actual864-face action along the verified source-response chart ray. -/
theorem standard_action_odd_limit :
    Tendsto (fun t : ℝ => (standardRay field 1 1 1 t-standardRay field 1 1 1 (-t))/(2*t^3))
      (𝓝[≠] 0) (𝓝 ((1784975 : ℝ)/2750517)) := by
  simpa only [coefficient_value] using standard_odd_limit field 1 1 1

theorem completed_action_odd_limit :
    Tendsto (fun t : ℝ => (completedRay field 1 1 1 t-completedRay field 1 1 1 (-t))/(2*t^3))
      (𝓝[≠] 0) (𝓝 ((1784975 : ℝ)/2750517)) := by
  simpa only [coefficient_value] using completed_odd_limit field 1 1 1

end OperatorDerivativeRewrite.Foundation.FourCubeCompletedCubic
