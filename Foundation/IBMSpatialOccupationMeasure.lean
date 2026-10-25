import Foundation.IBMSpatialPathReconstruction
import Foundation.DiagonalAmbientNullity

/-! The actual diagonal occupation is a finite positive Borel measure, with
mass T on the plane-null diagonal. Thus for T>0 it has no plane density. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialOccupationMeasure
open InfiniteGaussian IBMConstructedSources IBMClockOverlapEnergy
open IBMSpatialBoundedTestOperator IBMSpatialPathOccupation DiagonalAmbientNullity

def diagonalPath (Y : SampleSpace) (t : ℝ) : ℝ × ℝ :=
  (|clockPath Y t.toNNReal|,|clockPath Y t.toNNReal|)

theorem diagonalPath_measurable (Y : SampleSpace) : Measurable (diagonalPath Y) :=
  (((clockPath Y).continuous.comp continuous_real_toNNReal).measurable.norm).prodMk
    (((clockPath Y).continuous.comp continuous_real_toNNReal).measurable.norm)

def occupationMeasure (T : ℝ≥0) (Y : SampleSpace) : Measure (ℝ × ℝ) :=
  Measure.map (diagonalPath Y) (window T)

instance occupationMeasure_finite (T : ℝ≥0) (Y : SampleSpace) :
    IsFiniteMeasure (occupationMeasure T Y) := by unfold occupationMeasure; infer_instance

theorem mass (T : ℝ≥0) (Y : SampleSpace) :
    occupationMeasure T Y univ = ENNReal.ofReal T := by
  rw [occupationMeasure,Measure.map_apply (diagonalPath_measurable Y) MeasurableSet.univ]
  simp [window,Real.volume_Ioc]

theorem integral_actual (F : Tests) (T : ℝ≥0) (Y : SampleSpace) :
    (∫ z, F z ∂occupationMeasure T Y) = pathValue F T Y :=
  integral_map (diagonalPath_measurable Y).aemeasurable F.continuous.aestronglyMeasurable

theorem diagonal_mass (T : ℝ≥0) (Y : SampleSpace) :
    occupationMeasure T Y DiagonalAmbientNullity.diagonal = ENNReal.ofReal T := by
  rw [occupationMeasure,Measure.map_apply (diagonalPath_measurable Y) diagonal_measurable]
  have he : diagonalPath Y ⁻¹' DiagonalAmbientNullity.diagonal = univ := by
    ext t
    simp [diagonalPath,DiagonalAmbientNullity.diagonal]
  rw [he]
  simp [window,Real.volume_Ioc]

theorem not_absolutelyContinuous (T : ℝ≥0) (hT : 0 < T) (Y : SampleSpace) :
    ¬ occupationMeasure T Y ≪ plane := by
  intro ha
  have hz := ha plane_diagonal_zero
  rw [diagonal_mass] at hz
  have hp : 0 < ENNReal.ofReal (T:ℝ) := ENNReal.ofReal_pos.mpr hT
  exact (ne_of_gt hp) hz

theorem no_plane_density (T : ℝ≥0) (hT : 0 < T) (Y : SampleSpace)
    (f : ℝ × ℝ → ℝ≥0∞) : occupationMeasure T Y ≠ plane.withDensity f := by
  intro he
  apply not_absolutelyContinuous T hT Y
  rw [he]
  exact withDensity_absolutelyContinuous plane f

end OperatorDerivativeRewrite.Foundation.IBMSpatialOccupationMeasure
