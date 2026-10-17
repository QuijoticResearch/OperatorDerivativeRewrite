import Foundation.FibonacciNearestPartition

/-! The actual 16-center Fibonacci partition discharges the shear four-ray compatibility hypothesis. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FibonacciShearCentroid
open FiniteFourierDifferentialTrace FiniteFourierSynthesis GaussianShearFourierTail
open GaussianShearSectorMoments GaussianShearRayMoments LabelledShearCentroid
open FibonacciSphereWitness FibonacciNearestPartition

def partition (k : Wave) : Fin 16 := label (fun q => (k q : ℝ))

theorem axis_positive (m : ℤ) (hm : 0 < m) : partition (axis m)=rayLabels 0 := by
  have he : (fun q => (axis m q : ℝ))=(fun q => (m:ℝ)*ray 0 q) := by
    funext q
    fin_cases q <;> simp [axis,ray]
  change label (fun q => (axis m q : ℝ))=_
  rw [he,label_scale (m:ℝ) (by exact_mod_cast hm)]
  rfl

theorem axis_negative (m : ℤ) (hm : m < 0) : partition (axis m)=rayLabels 1 := by
  have he : (fun q => (axis m q : ℝ))=(fun q => (-(m:ℝ))*ray 1 q) := by
    funext q
    fin_cases q <;> simp [axis,ray]
  change label (fun q => (axis m q : ℝ))=_
  rw [he,label_scale (-(m:ℝ)) (by exact_mod_cast (neg_pos.mpr hm))]
  rfl

theorem plus_label : partition plus=rayLabels 2 := by
  have he : (fun q => (plus q : ℝ))=ray 2 := by
    funext q
    fin_cases q <;> simp [plus,ray]
  change label (fun q => (plus q : ℝ))=_
  rw [he]
  rfl

theorem minus_label : partition minus=rayLabels 3 := by
  have he : (fun q => (minus q : ℝ))=ray 3 := by
    funext q
    fin_cases q <;> simp [minus,ray]
  change label (fun q => (minus q : ℝ))=_
  rw [he]
  rfl

theorem compatible : Compatible rayLabels partition :=
  ⟨axis_positive,axis_negative,plus_label,minus_label⟩

theorem partition_moments (p : ℕ) (hp : 0 < p) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    partitionMoment partition p nu t=FiniteRayCentroid.energy rayLabels
      (GaussianShearSectorMoments.moment 0 p nu t/2) (GaussianShearSectorMoments.moment 1 p nu t/2) :=
  partition_table rayLabels partition compatible p hp nu t hs

theorem centroid_ratio_gt_one (nu t : ℝ) (hs : 0 < 1+nu*t) :
    1 < partitionRatio partition nu t :=
  partitionRatio_gt_one rayLabels partition compatible nu t hs

theorem zero_extended_centroid_gt_one (nu t : ℝ) (hs : 0 < 1+nu*t) :
    1 < zeroExtendedCentroid partition nu t :=
  zeroExtendedCentroid_gt_one rayLabels partition compatible nu t hs

end OperatorDerivativeRewrite.Foundation.FibonacciShearCentroid
