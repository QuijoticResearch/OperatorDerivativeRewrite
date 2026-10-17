import Foundation.HigherHeatWeightedPaths
import Foundation.HigherHeatSignedRepresentation

/-! Eventual exactness of the actual path approximants on cylinders, and their weak-limit obstruction. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCylinderPathLimit
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatCylindricalExpectation
open HigherHeatPathCylinderAlgebra HigherHeatInterpolatedPaths HigherHeatWeightedPaths
open HigherHeatSignedRepresentation

theorem integral_current_level (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (f : Test n) :
    (∫ᵛ ω, sampleLift n f ω ∂•signedPath m hm T hT n)=expectation m hm T hT n f := by
  have hi := bounded_real_integrable (signedPath m hm T hT n) (sampleLift n f)
  have hh : (∫ᵛ x, f x ∂•(signedPath m hm T hT n).map (sample n))=
      ∫ᵛ ω, f (sample n ω) ∂•signedPath m hm T hT n :=
    VectorMeasure.integral_map (sample_continuous n).measurable f.continuous.aestronglyMeasurable hi
  rw [signedPath_sample] at hh
  exact hh.symm

theorem integral_coarse_level (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (k n : ℕ) (hkn : k ≤ n) (f : Test k) :
    (∫ᵛ ω, sampleLift k f ω ∂•signedPath m hm T hT n)=expectation m hm T hT k f := by
  rw [← sampleLift_transfer k n hkn f, integral_current_level, expectation_transfer]

theorem eventual_integral_level (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (k : ℕ) (f : Test k) :
    ∀ᶠ n in atTop, (∫ᵛ ω, sampleLift k f ω ∂•signedPath m hm T hT n)=expectation m hm T hT k f :=
  eventually_atTop.mpr ⟨k, fun n hn => integral_coarse_level m hm T hT k n hn f⟩

theorem eventual_integral_cylinder (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (c : Cylinder) :
    ∀ᶠ n in atTop, (∫ᵛ ω, realize c ω ∂•signedPath m hm T hT n)=cylindricalExpectation m hm T hT c := by
  obtain ⟨k,f,g,hc,hg⟩ := DirectLimit.exists_eq_mk₂ transition c c
  change c=cylinderOf k f at hc
  rw [hc, cylindricalExpectation_apply]
  exact eventual_integral_level m hm T hT k f

theorem eventual_integral_algebra (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (F : cylinderAlgebra) :
    ∀ᶠ n in atTop, (∫ᵛ ω, F.val ω ∂•signedPath m hm T hT n)=algebraExpectation m hm T hT F := by
  obtain ⟨c,hc⟩ := F.property
  have hF : F=representCylinder c := Subtype.ext hc.symm
  rw [hF, algebraExpectation_represent]
  exact eventual_integral_cylinder m hm T hT c

theorem tendsto_integral_algebra (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (F : cylinderAlgebra) :
    Tendsto (fun n => ∫ᵛ ω, F.val ω ∂•signedPath m hm T hT n) atTop
      (𝓝 (algebraExpectation m hm T hT F)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventual_integral_algebra m hm T hT F] with n hn
  exact hn.symm

theorem coarse_marginal (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (k n : ℕ) (hkn : k ≤ n) :
    (signedPath m hm T hT n).map (sample k)=law m hm T hT k := by
  apply signed_ext_bounded
  intro f
  have hi := bounded_real_integrable (signedPath m hm T hT n) (sampleLift k f)
  calc
    (∫ᵛ x, f x ∂•(signedPath m hm T hT n).map (sample k)) =
        ∫ᵛ ω, sampleLift k f ω ∂•signedPath m hm T hT n :=
      VectorMeasure.integral_map (sample_continuous k).measurable f.continuous.aestronglyMeasurable hi
    _ = expectation m hm T hT k f := integral_coarse_level m hm T hT k n hkn f
    _ = ∫ᵛ x, f x ∂•law m hm T hT k := rfl

def complexLift (k : ℕ) : (Grid k →ᵇ ℂ) →L[ℝ] (Path →ᵇ ℂ) :=
  BoundedContinuousFunction.compContinuousCLM ℂ ℝ ⟨sample k, sample_continuous k⟩

theorem complexLift_integrable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (k n : ℕ) (f : Grid k →ᵇ ℂ) : (signedPath m hm T hT n).Integrable (complexLift k f) :=
  SignedDensityIntegral.bounded_signed_integrable _ _ (complexLift k f).continuous.measurable
    ‖complexLift k f‖ (fun ω => (complexLift k f).norm_coe_le_norm ω)

theorem complex_integral_coarse (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (k n : ℕ) (hkn : k ≤ n) (f : Grid k →ᵇ ℂ) :
    (∫ᵛ ω, complexLift k f ω ∂<•signedPath m hm T hT n)=∫ᵛ x, f x ∂<•law m hm T hT k := by
  calc
    (∫ᵛ ω, complexLift k f ω ∂<•signedPath m hm T hT n) =
        ∫ᵛ x, f x ∂<•(signedPath m hm T hT n).map (sample k) :=
      (VectorMeasure.integral_map (sample_continuous k).measurable f.continuous.aestronglyMeasurable
        (complexLift_integrable m hm T hT k n f)).symm
    _ = ∫ᵛ x, f x ∂<•law m hm T hT k := by rw [coarse_marginal m hm T hT k n hkn]

theorem weighted_complex_cylinder (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (k n : ℕ) (hkn : k ≤ n) (f : Grid k →ᵇ ℂ) :
    (∫ ω, pathWeight m hm T hT n ω • complexLift k f ω ∂probabilityPath m hm T hT n)=
      ∫ᵛ x, f x ∂<•law m hm T hT k :=
  (signedPath_expectation m hm T hT n (complexLift k f)
    (complexLift_integrable m hm T hT k n f)).symm.trans
      (complex_integral_coarse m hm T hT k n hkn f)

theorem weighted_complex_integrable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (k n : ℕ) (f : Grid k →ᵇ ℂ) :
    Integrable (fun ω => pathWeight m hm T hT n ω • complexLift k f ω) (probabilityPath m hm T hT n) :=
  path_weighted_integrable m hm T hT n _ (complexLift_integrable m hm T hT k n f)

theorem no_signed_weak_limit_cofinal (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop) (ν : SignedMeasure Path) :
    ¬ ∀ F : Path →ᵇ ℝ, Tendsto (fun j => ∫ᵛ ω, F ω ∂•signedPath m (by omega) T hT (r j)) atTop
      (𝓝 (∫ᵛ ω, F ω ∂•ν)) := by
  intro h
  apply no_signed_observable_realization m hm T hT ν
  intro F
  exact tendsto_nhds_unique ((tendsto_integral_algebra m (by omega) T hT F).comp hr) (h F.val)

theorem no_signed_weak_limit (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) (ν : SignedMeasure Path) :
    ¬ ∀ F : Path →ᵇ ℝ, Tendsto (fun n => ∫ᵛ ω, F ω ∂•signedPath m (by omega) T hT n) atTop
      (𝓝 (∫ᵛ ω, F ω ∂•ν)) :=
  no_signed_weak_limit_cofinal m hm T hT id tendsto_id ν

end OperatorDerivativeRewrite.Foundation.HigherHeatCylinderPathLimit
