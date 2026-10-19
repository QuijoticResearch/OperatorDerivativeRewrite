import Foundation.GaussianItoChaosIntertwining
import Foundation.GaussianFiniteHorizonAdjoint
import Foundation.GaussianComplexHorizonIto

/-! Actual finite-horizon predictable chaos projection, with its genuine
probability-section action and stochastic-integral degree shift. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianHorizonChaosIntertwining
open InfiniteGaussian GaussianTimeProductL2 GaussianTimeHilbert GaussianPredictableFull
open GaussianPredictableCutoff GaussianPredictableL2Completion GaussianSensitivityCore
open GaussianPredictableChaosCore GaussianItoChaosIntertwining GaussianPredictableHorizon
open GaussianFiniteHorizonAdjoint GaussianRoughFiniteHorizon GaussianComplexHorizonIto
set_option backward.isDefEq.respectTransparency false
attribute [local instance] timeHilbert_secondCountable
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe
local instance (T : ℝ≥0) : CompleteSpace (PredictableDomain T) :=
  (isClosed_aestronglyMeasurable
    (PredictableRealL2.predictable_le GaussianTimeProcess.naturalFiltration)).completeSpace_coe

theorem scalarLift_cut (A : GaussianL2 →L[ℝ] GaussianL2) (T : ℝ≥0) (u : fullPredictable) :
    scalarLift A (cut T u) = cut T (scalarLift A u) := by
  let D := (scalarLift A).comp (cut T) - (cut T).comp (scalarLift A)
  have h : closedProductSteps ≤ D.ker := by
    apply Submodule.topologicalClosure_minimal
    · rw [productStepSpan,Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro z ⟨m,r,p,s,t,hrs,hst,rfl⟩
      change scalarLift A (cut T (productTensor (intervalVector s t)
        (GaussianTimeDivergence.pastCoefficient r p))) -
        cut T (scalarLift A (productTensor (intervalVector s t)
          (GaussianTimeDivergence.pastCoefficient r p))) = 0
      rw [cut_tensor,scalarLift_tensor,scalarLift_tensor,cut_tensor,sub_self]
    · exact D.isClosed_ker
  have hu : (u : TimeProbabilityL2) ∈ closedProductSteps := by
    rw [closedProductSteps_eq_fullPredictable]
    exact u.property
  exact sub_eq_zero.mp (h hu)

theorem projected_cut (n : ℕ) (T : ℝ≥0) (u : fullPredictable) :
    projectedPredictable n (predictableCut T u) = predictableCut T (projectedPredictable n u) := by
  apply Subtype.ext
  exact scalarLift_cut (GaussianNumberSectors.projection n) T u

theorem projected_extended_supported (n : ℕ) (T : ℝ≥0) (u : PredictableDomain T) :
    predictableCut T (projectedPredictable n (extendPredictable T u)) =
      projectedPredictable n (extendPredictable T u) := by
  rw [← projected_cut,cut_extended]

theorem restricted_projection_integral (n : ℕ) (T : ℝ≥0) (u : PredictableDomain T) :
    GaussianPredictableHorizon.itoIntegral T
      (restrictPredictable T (projectedPredictable n (extendPredictable T u))) =
        GaussianNumberSectors.projection (n + 1) (GaussianPredictableHorizon.itoIntegral T u) := by
  rw [restricted_integral,projected_extended_supported,integral_projection,
    ← finite_integral_eq_extended]

def horizonProjection (n : ℕ) (T : ℝ≥0) : PredictableDomain T →L[ℝ] PredictableDomain T :=
  (finiteAdjoint T).comp ((GaussianNumberSectors.projection (n + 1)).comp
    (GaussianPredictableHorizon.itoIntegral T).toContinuousLinearMap)

/-- Identifies the bounded adjoint construction with ACTUAL probability
projection on the zero-extended and then restricted predictable field. -/
theorem horizonProjection_eq (n : ℕ) (T : ℝ≥0) (u : PredictableDomain T) :
    horizonProjection n T u =
      restrictPredictable T (projectedPredictable n (extendPredictable T u)) := by
  change (GaussianPredictableHorizon.itoIntegral T).toContinuousLinearMap.adjoint
    (GaussianNumberSectors.projection (n + 1) (GaussianPredictableHorizon.itoIntegral T u)) = _
  rw [← restricted_projection_integral]
  exact congrArg (fun A : PredictableDomain T →L[ℝ] PredictableDomain T =>
    A (restrictPredictable T (projectedPredictable n (extendPredictable T u))))
      (GaussianPredictableHorizon.itoIntegral T).adjoint_comp_self

theorem integral_horizonProjection (n : ℕ) (T : ℝ≥0) (u : PredictableDomain T) :
    GaussianPredictableHorizon.itoIntegral T (horizonProjection n T u) =
      GaussianNumberSectors.projection (n + 1) (GaussianPredictableHorizon.itoIntegral T u) := by
  rw [horizonProjection_eq,restricted_projection_integral]

def realProjection (n : ℕ) (T : ℝ≥0) :
    Lp ℝ 2 (predictableMeasure T) →L[ℝ] Lp ℝ 2 (predictableMeasure T) :=
  (GaussianComplexHorizonIto.trimEquiv T).toLinearIsometry.toContinuousLinearMap.comp
    ((horizonProjection n T).comp (GaussianComplexHorizonIto.trimEquiv T).symm.toLinearIsometry.toContinuousLinearMap)

theorem integral_realProjection (n : ℕ) (T : ℝ≥0) (u : Lp ℝ 2 (predictableMeasure T)) :
    realIto T (realProjection n T u) = GaussianNumberSectors.projection (n + 1) (realIto T u) := by
  change realIto T (GaussianComplexHorizonIto.trimEquiv T
    (horizonProjection n T ((GaussianComplexHorizonIto.trimEquiv T).symm u))) = _
  rw [realIto_trim,integral_horizonProjection]
  rfl

theorem realProjection_norm_le (n : ℕ) (T : ℝ≥0) (u : Lp ℝ 2 (predictableMeasure T)) :
    ‖realProjection n T u‖ ≤ ‖u‖ := by
  rw [← (realIto T).norm_map (realProjection n T u),integral_realProjection]
  exact (GaussianNumberSectors.projection_norm_le _ _).trans_eq ((realIto T).norm_map u)

theorem alternating_extended_supported (T : ℝ≥0) (u : PredictableDomain T) :
    predictableCut T (GaussianItoAlternatingProjection.alternatingOperator (extendPredictable T u)) =
      GaussianItoAlternatingProjection.alternatingOperator (extendPredictable T u) := by
  have hs := alternating_hasSum (extendPredictable T u)
  have ht := hs.map (predictableCut T).toAddMonoidHom (predictableCut T).continuous
  change HasSum (fun n : ℕ => predictableCut T
    ((n + 1 : ℝ)⁻¹ • projectedPredictable n (extendPredictable T u))) _ at ht
  simp only [map_smul,projected_extended_supported] at ht
  exact ht.unique hs

theorem restricted_regularization_integral (T : ℝ≥0) (u : PredictableDomain T) :
    GaussianPredictableHorizon.itoIntegral T (restrictPredictable T
      (GaussianItoAlternatingProjection.alternatingOperator (extendPredictable T u))) =
        GaussianInverseNumberPotential.potentialOperator (GaussianPredictableHorizon.itoIntegral T u) := by
  rw [restricted_integral,alternating_extended_supported,
    GaussianItoAlternatingProjection.integral_alternating,← finite_integral_eq_extended]

def horizonRegularization (T : ℝ≥0) : PredictableDomain T →L[ℝ] PredictableDomain T :=
  (finiteAdjoint T).comp (GaussianInverseNumberPotential.potentialOperator.comp
    (GaussianPredictableHorizon.itoIntegral T).toContinuousLinearMap)

theorem horizonRegularization_eq (T : ℝ≥0) (u : PredictableDomain T) :
    horizonRegularization T u = restrictPredictable T
      (GaussianItoAlternatingProjection.alternatingOperator (extendPredictable T u)) := by
  change (GaussianPredictableHorizon.itoIntegral T).toContinuousLinearMap.adjoint
    (GaussianInverseNumberPotential.potentialOperator (GaussianPredictableHorizon.itoIntegral T u)) = _
  rw [← restricted_regularization_integral]
  exact congrArg (fun A : PredictableDomain T →L[ℝ] PredictableDomain T =>
    A (restrictPredictable T (GaussianItoAlternatingProjection.alternatingOperator
      (extendPredictable T u)))) (GaussianPredictableHorizon.itoIntegral T).adjoint_comp_self

theorem integral_horizonRegularization (T : ℝ≥0) (u : PredictableDomain T) :
    GaussianPredictableHorizon.itoIntegral T (horizonRegularization T u) =
      GaussianInverseNumberPotential.potentialOperator (GaussianPredictableHorizon.itoIntegral T u) := by
  rw [horizonRegularization_eq,restricted_regularization_integral]

def realRegularization (T : ℝ≥0) :
    Lp ℝ 2 (predictableMeasure T) →L[ℝ] Lp ℝ 2 (predictableMeasure T) :=
  (GaussianComplexHorizonIto.trimEquiv T).toLinearIsometry.toContinuousLinearMap.comp
    ((horizonRegularization T).comp
      (GaussianComplexHorizonIto.trimEquiv T).symm.toLinearIsometry.toContinuousLinearMap)

theorem integral_realRegularization (T : ℝ≥0) (u : Lp ℝ 2 (predictableMeasure T)) :
    realIto T (realRegularization T u) = GaussianInverseNumberPotential.potentialOperator (realIto T u) := by
  change realIto T (GaussianComplexHorizonIto.trimEquiv T
    (horizonRegularization T ((GaussianComplexHorizonIto.trimEquiv T).symm u))) = _
  rw [realIto_trim,integral_horizonRegularization]
  rfl

theorem realRegularization_hasSum (T : ℝ≥0) (u : Lp ℝ 2 (predictableMeasure T)) :
    HasSum (fun k : ℕ => (k + 1 : ℝ)⁻¹ • realProjection k T u) (realRegularization T u) := by
  let a := (GaussianComplexHorizonIto.trimEquiv T).symm u
  let L := (GaussianComplexHorizonIto.trimEquiv T).toLinearIsometry.toContinuousLinearMap.comp
    (finiteAdjoint T)
  have hs := (GaussianInverseNumberPotential.potential_hasSum
    (GaussianPredictableHorizon.itoIntegral T a)).map L.toAddMonoidHom L.continuous
  change HasSum (fun k : ℕ => L ((k : ℝ)⁻¹ • GaussianNumberSectors.projection k
    (GaussianPredictableHorizon.itoIntegral T a))) (realRegularization T u) at hs
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one,Nat.cast_zero,inv_zero,zero_smul,map_zero,sub_zero] at ht
  have he (k : ℕ) : L (((k + 1 : ℕ) : ℝ)⁻¹ • GaussianNumberSectors.projection (k + 1)
      (GaussianPredictableHorizon.itoIntegral T a)) = (k + 1 : ℝ)⁻¹ • realProjection k T u := by
    rw [map_smul]
    simp only [Nat.cast_add,Nat.cast_one]
    rfl
  simpa only [he] using ht

end OperatorDerivativeRewrite.Foundation.GaussianHorizonChaosIntertwining
