import Foundation.IBMNonlinearColumnContinuity
import Foundation.IBMClockOccupationPath
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Source-Hilbert-valued occupation identity for the actual original clock
kernel, including compactly localized native nonlinear source columns. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSourceValuedOccupation
open InfiniteGaussian IBMClockPhysicalOccupation IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def fieldValue (h : CoefficientSpace) (G : ℝ → GaussianL2) (p : ℝ × SampleSpace) : GaussianL2 :=
  (inner ℝ h (IBMClockAverageCandidate.direction p.1) *
    BrownianSignIntegral.signum (IBMConstructedSources.clockPath p.2 p.1.toNNReal)) •
      G |IBMConstructedSources.clockPath p.2 p.1.toNNReal|

theorem fieldValue_stronglyMeasurable (h : CoefficientSpace) (G : ℝ → GaussianL2)
    (hc : Continuous G) : StronglyMeasurable (fieldValue h G) := by
  have hd : Measurable (fun t : ℝ => inner ℝ h (IBMClockAverageCandidate.direction t)) :=
    (continuous_const.inner IBMClockAverageCandidate.direction_continuous).measurable
  have hb := BrownianClockWeightedEnergy.sigma_measurable
  exact (((hd.comp measurable_fst).mul
    (BrownianSignIntegral.signum_measurable.comp hb)).stronglyMeasurable).smul
      (hc.stronglyMeasurable.comp_measurable (continuous_abs.measurable.comp hb))

theorem fieldValue_bound (h : CoefficientSpace) (G : ℝ → GaussianL2)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ r, ‖G r‖ ≤ M) (T : ℝ≥0)
    (p : ℝ × SampleSpace) (hp : p.1 ∈ Ioc 0 (T : ℝ)) :
    ‖fieldValue h G p‖ ≤ ‖h‖ * Real.sqrt T * M := by
  have he : ‖fieldValue h G p‖ =
      ‖IBMClockOccupationPath.value h (fun r => ‖G r‖) p‖ := by
    simp only [fieldValue, IBMClockOccupationPath.value, norm_smul, norm_mul, norm_norm]
  rw [he]
  exact IBMClockOccupationPath.value_bound h _ hM
    (fun r => by simpa only [norm_norm] using hb r) T p hp

theorem field_time_integrable (h : CoefficientSpace) (G : ℝ → GaussianL2)
    (hc : Continuous G) (hs : HasCompactSupport G) (T : ℝ≥0) (Y : SampleSpace) :
    Integrable (fun t => fieldValue h G (t,Y)) (window T) := by
  obtain ⟨M,hb⟩ := hc.norm.bddAbove_range_of_hasCompactSupport hs.norm
  have hM : 0 ≤ M := (norm_nonneg (G 0)).trans (hb ⟨0,rfl⟩)
  apply Integrable.of_bound
    (((fieldValue_stronglyMeasurable h G hc).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable) (‖h‖*Real.sqrt T*M)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact fieldValue_bound h G hM (fun r => hb ⟨r,rfl⟩) T (t,Y) ht

def pathField (h : CoefficientSpace) (G : ℝ → GaussianL2) (T : ℝ≥0) (Y : SampleSpace) : GaussianL2 :=
  ∫ t, fieldValue h G (t,Y) ∂window T

theorem pathField_stronglyMeasurable (h : CoefficientSpace) (G : ℝ → GaussianL2)
    (hc : Continuous G) (T : ℝ≥0) : StronglyMeasurable (pathField h G T) :=
  (fieldValue_stronglyMeasurable h G hc).integral_prod_left' (μ := window T)

theorem pathField_bound (h : CoefficientSpace) (G : ℝ → GaussianL2)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ r, ‖G r‖ ≤ M) (T : ℝ≥0) (Y : SampleSpace) :
    ‖pathField h G T Y‖ ≤ (T : ℝ)*(‖h‖*Real.sqrt T*M) := by
  have ha : ∀ᵐ t ∂window T, ‖fieldValue h G (t,Y)‖ ≤ ‖h‖*Real.sqrt T*M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact fieldValue_bound h G hM hb T (t,Y) ht
  simpa [pathField, window, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal T.property, mul_comm] using norm_integral_le_of_norm_le_const ha

theorem pathField_memLp (h : CoefficientSpace) (G : ℝ → GaussianL2)
    (hc : Continuous G) (hs : HasCompactSupport G) (T : ℝ≥0) :
    MemLp (pathField h G T) 2 gaussianProduct := by
  obtain ⟨M,hb⟩ := hc.norm.bddAbove_range_of_hasCompactSupport hs.norm
  have hM : 0 ≤ M := (norm_nonneg (G 0)).trans (hb ⟨0,rfl⟩)
  exact MemLp.of_bound (pathField_stronglyMeasurable h G hc T).aestronglyMeasurable
    ((T : ℝ)*(‖h‖*Real.sqrt T*M))
    (ae_of_all _ (pathField_bound h G hM (fun r => hb ⟨r,rfl⟩) T))

def spatial (h : CoefficientSpace) (G : ℝ → GaussianL2) (T : ℝ≥0) (Y : SampleSpace) : GaussianL2 :=
  ∫ r : ℝ, kernel h T Y r • G r

theorem spatial_integrable (h : CoefficientSpace) (G : ℝ → GaussianL2)
    (hc : Continuous G) (hs : HasCompactSupport G) (T : ℝ≥0) (Y : SampleSpace) :
    Integrable (fun r : ℝ => kernel h T Y r • G r) := by
  have hG : MemLp G 2 volume := hc.memLp_of_hasCompactSupport hs
  have hi := (Lp.memLp (kernel h T Y)).norm.integrable_mul hG.norm
  apply hi.mono' ((Lp.aestronglyMeasurable (kernel h T Y)).smul hc.aestronglyMeasurable)
  exact ae_of_all _ fun r => by
    change ‖kernel h T Y r • G r‖ ≤ ‖kernel h T Y r‖ * ‖G r‖
    rw [norm_smul]

theorem spatial_pairing (h : CoefficientSpace) (G : ℝ → GaussianL2)
    (hc : Continuous G) (hs : HasCompactSupport G) (T : ℝ≥0) (Y : SampleSpace) (ζ : GaussianL2) :
    inner ℝ ζ (spatial h G T Y) = ∫ r : ℝ, kernel h T Y r * inner ℝ ζ (G r) := by
  rw [spatial, ← integral_inner (spatial_integrable h G hc hs T Y)]
  apply integral_congr_ae
  exact ae_of_all _ fun r => inner_smul_right _ _ _

theorem path_pairing (h : CoefficientSpace) (G : ℝ → GaussianL2)
    (hc : Continuous G) (hs : HasCompactSupport G) (T : ℝ≥0) (Y : SampleSpace) (ζ : GaussianL2) :
    inner ℝ ζ (pathField h G T Y) =
      IBMClockOccupationPath.pathIntegral h (fun r => inner ℝ ζ (G r)) T Y := by
  rw [pathField, ← integral_inner (field_time_integrable h G hc hs T Y)]
  apply integral_congr_ae
  exact ae_of_all _ fun t => inner_smul_right _ _ _

/-- Actual source-Hilbert-valued equality on one clock-full-measure event.
The existing countable dense-inner-product theorem justifies the AE exchange. -/
theorem spatial_path_ae (h : CoefficientSpace) (G : ℝ → GaussianL2)
    (hc : Continuous G) (hs : HasCompactSupport G) (T : ℝ≥0) :
    spatial h G T =ᵐ[gaussianProduct] pathField h G T := by
  have hz : (fun Y => spatial h G T Y-pathField h G T Y) =ᵐ[gaussianProduct] 0 :=
    ae_eq_zero_of_forall_inner (𝕜 := ℝ) (fun ζ => by
      have hφc : Continuous (fun r => inner ℝ ζ (G r)) := continuous_const.inner hc
      have hφs : HasCompactSupport (fun r => inner ℝ ζ (G r)) := hs.comp_left (by simp)
      filter_upwards [IBMClockOccupationPath.kernel_spatial_integral_ae h _ hφc hφs T] with Y hY
      change inner ℝ ζ (spatial h G T Y-pathField h G T Y) = 0
      rw [inner_sub_right, spatial_pairing h G hc hs T Y ζ, path_pairing h G hc hs T Y ζ]
      exact sub_eq_zero.mpr hY)
  filter_upwards [hz] with Y hY
  exact sub_eq_zero.mp hY

theorem spatial_memLp (h : CoefficientSpace) (G : ℝ → GaussianL2)
    (hc : Continuous G) (hs : HasCompactSupport G) (T : ℝ≥0) :
    MemLp (spatial h G T) 2 gaussianProduct :=
  (pathField_memLp h G hc hs T).ae_eq (spatial_path_ae h G hc hs T).symm

/-- Genuine finite-native nonlinear occupation identity, keeping the cutoff. -/
theorem nonlinear_spatial_path_ae (h : CoefficientSpace) (n : ℕ)
    (χ : ℝ → ℝ) (hc : Continuous χ) (hs : HasCompactSupport χ) (T : ℝ≥0) :
    spatial h (fun r => χ r • IBMNonlinearClockColumn.column n r) T =ᵐ[gaussianProduct]
      pathField h (fun r => χ r • IBMNonlinearClockColumn.column n r) T :=
  spatial_path_ae h _ (hc.smul (IBMNonlinearColumnContinuity.column_continuous n)) hs.smul_right T

end OperatorDerivativeRewrite.Foundation.IBMSourceValuedOccupation
