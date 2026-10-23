import Foundation.IBMSourceValuedOccupation
import Foundation.IBMNonlinearSpatialLimit
import Mathlib.MeasureTheory.Function.Holder

/-! Actual compactly localized nonlinear clock fields converge strongly to
completed rough spatial stochastic source integrals of the occupation kernel. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearClockLocalization
open InfiniteGaussian GaussianTimeHilbert IBMClockPhysicalOccupation
open IBMNonlinearSpatialOperator IBMNonlinearSpatialLimit
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨by simp⟩

def cutoffClass (χ : ℝ → ℝ) (hc : Continuous χ) (hs : HasCompactSupport χ) : Lp ℝ ∞ (volume : Measure ℝ) :=
  (hc.memLp_top_of_hasCompactSupport hs volume).toLp χ

def multiply (χ : ℝ → ℝ) (hc : Continuous χ) (hs : HasCompactSupport χ) :
    TimeHilbert →L[ℝ] TimeHilbert :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL volume ∞ 2 2 (cutoffClass χ hc hs)

theorem multiply_ae (χ : ℝ → ℝ) (hc : Continuous χ) (hs : HasCompactSupport χ)
    (k : TimeHilbert) : multiply χ hc hs k =ᵐ[volume] fun r => χ r*k r := by
  have he := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (cutoffClass χ hc hs) k
  filter_upwards [he, (hc.memLp_top_of_hasCompactSupport hs volume).coeFn_toLp] with r hm hχ
  change cutoffClass χ hc hs r = χ r at hχ
  change multiply χ hc hs k r = cutoffClass χ hc hs r * k r at hm
  rw [hχ] at hm
  exact hm

def restrictWindow (a b : ℝ) : TimeHilbert →L[ℝ] Space a b :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using
    (Measure.restrict_le_self : volume.restrict (Ioc a b) ≤ volume))

def cutoffInput (χ : ℝ → ℝ) (hc : Continuous χ) (hs : HasCompactSupport χ) (a b : ℝ) :
    TimeHilbert →L[ℝ] Space a b := (restrictWindow a b).comp (multiply χ hc hs)

theorem cutoffInput_ae (χ : ℝ → ℝ) (hc : Continuous χ) (hs : HasCompactSupport χ)
    (a b : ℝ) (k : TimeHilbert) :
    cutoffInput χ hc hs a b k =ᵐ[volume.restrict (Ioc a b)] fun r => χ r*k r := by
  have he := Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (show volume.restrict (Ioc a b) ≤ (1 : ℝ≥0∞) • volume by
      simpa using (Measure.restrict_le_self : volume.restrict (Ioc a b) ≤ volume))
    (multiply χ hc hs k)
  exact he.trans (ae_restrict_of_ae (multiply_ae χ hc hs k))

theorem operator_spatial_eq (n : ℕ) (χ : ℝ → ℝ) (hc : Continuous χ)
    (hs : HasCompactSupport χ) {a b : ℝ} (hab : a ≤ b)
    (hχ : ∀ r, r ∉ Ioc a b → χ r = 0) (k : TimeHilbert) :
    operator n hab (cutoffInput χ hc hs a b k) =
      ∫ r : ℝ, k r • (χ r • IBMNonlinearClockColumn.column n r) := by
  rw [operator_apply]
  calc
    _ = ∫ r in Ioc a b, k r • (χ r • IBMNonlinearClockColumn.column n r) := by
      apply integral_congr_ae
      filter_upwards [cutoffInput_ae χ hc hs a b k] with r hr
      rw [hr]
      simp only [smul_smul]
      congr 1
      exact mul_comm _ _
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun r hr => by simp [hχ r hr])

def finiteField (h : CoefficientSpace) (n : ℕ) (χ : ℝ → ℝ) (hc : Continuous χ)
    (hs : HasCompactSupport χ) {a b : ℝ} (hab : a ≤ b) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  (operator n hab).compLpL 2 gaussianProduct
    ((cutoffInput χ hc hs a b).compLpL 2 gaussianProduct (kernel h T))

def limitField (h : CoefficientSpace) (χ : ℝ → ℝ) (hc : Continuous χ)
    (hs : HasCompactSupport χ) {a b : ℝ} (hab : a ≤ b) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  (completed hab).compLpL 2 gaussianProduct
    ((cutoffInput χ hc hs a b).compLpL 2 gaussianProduct (kernel h T))

theorem finiteField_tendsto (h : CoefficientSpace) (χ : ℝ → ℝ) (hc : Continuous χ)
    (hs : HasCompactSupport χ) {a b : ℝ} (hab : a ≤ b) (T : ℝ≥0) :
    Tendsto (fun n => finiteField h n χ hc hs hab T) atTop (𝓝 (limitField h χ hc hs hab T)) :=
  clock_lift_tendsto hab ((cutoffInput χ hc hs a b).compLpL 2 gaussianProduct (kernel h T))

theorem finiteField_path_ae (h : CoefficientSpace) (n : ℕ) (χ : ℝ → ℝ)
    (hc : Continuous χ) (hs : HasCompactSupport χ) {a b : ℝ} (hab : a ≤ b)
    (hχ : ∀ r, r ∉ Ioc a b → χ r = 0) (T : ℝ≥0) :
    finiteField h n χ hc hs hab T =ᵐ[gaussianProduct]
      IBMSourceValuedOccupation.pathField h (fun r => χ r • IBMNonlinearClockColumn.column n r) T := by
  let u := (cutoffInput χ hc hs a b).compLpL 2 gaussianProduct (kernel h T)
  filter_upwards [(operator n hab).coeFn_compLpL u,
    (cutoffInput χ hc hs a b).coeFn_compLpL (kernel h T),
    IBMSourceValuedOccupation.nonlinear_spatial_path_ae h n χ hc hs T] with Y ho hu hp
  change u Y = cutoffInput χ hc hs a b (kernel h T Y) at hu
  change finiteField h n χ hc hs hab T Y = operator n hab (u Y) at ho
  rw [ho, hu, operator_spatial_eq n χ hc hs hab hχ]
  exact hp

def nativeField (h : CoefficientSpace) (n : ℕ) (χ : ℝ → ℝ) (hc : Continuous χ)
    (hs : HasCompactSupport χ) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  (IBMSourceValuedOccupation.pathField_memLp h _
    (hc.smul (IBMNonlinearColumnContinuity.column_continuous n)) hs.smul_right T).toLp _

theorem finiteField_eq_native (h : CoefficientSpace) (n : ℕ) (χ : ℝ → ℝ)
    (hc : Continuous χ) (hs : HasCompactSupport χ) {a b : ℝ} (hab : a ≤ b)
    (hχ : ∀ r, r ∉ Ioc a b → χ r = 0) (T : ℝ≥0) :
    finiteField h n χ hc hs hab T = nativeField h n χ hc hs T := by
  apply Lp.ext
  exact (finiteField_path_ae h n χ hc hs hab hχ T).trans (MemLp.coeFn_toLp _).symm

/-- Actual compactly localized native nonlinear clock-direction integrals
converge STRONGLY to the completed stochastic occupation integral. -/
theorem nativeField_tendsto (h : CoefficientSpace) (χ : ℝ → ℝ)
    (hc : Continuous χ) (hs : HasCompactSupport χ) {a b : ℝ} (hab : a ≤ b)
    (hχ : ∀ r, r ∉ Ioc a b → χ r = 0) (T : ℝ≥0) :
    Tendsto (fun n => nativeField h n χ hc hs T) atTop (𝓝 (limitField h χ hc hs hab T)) := by
  simpa only [finiteField_eq_native h _ χ hc hs hab hχ T] using finiteField_tendsto h χ hc hs hab T

def rawTimeValue (h : CoefficientSpace) (n : ℕ) (χ : ℝ → ℝ)
    (t : ℝ) (p : IBMSourceLaws.JointSample) : ℝ :=
  (inner ℝ h (IBMClockAverageCandidate.direction t) *
    BrownianSignIntegral.signum (IBMConstructedSources.clockPath p.2 t.toNNReal) *
      χ |IBMConstructedSources.clockPath p.2 t.toNNReal|) *
        IBMNonlinearClockColumn.value n |IBMConstructedSources.clockPath p.2 t.toNNReal| p.1

/-- For EACH clock sample, the actual source-Hilbert time integral has the
literal native nonlinear random-time representative on the original source. -/
theorem pathField_raw_source_ae (h : CoefficientSpace) (n : ℕ) (χ : ℝ → ℝ)
    (hc : Continuous χ) (hs : HasCompactSupport χ) (T : ℝ≥0) (Y : SampleSpace) :
    IBMSourceValuedOccupation.pathField h (fun r => χ r • IBMNonlinearClockColumn.column n r) T Y
      =ᵐ[gaussianProduct] fun X => ∫ t, rawTimeValue h n χ t (X,Y) ∂IBMClockOverlapEnergy.window T := by
  let σ : ℝ → ℝ := fun t => |IBMConstructedSources.clockPath Y t.toNNReal|
  let c : ℝ → ℝ := fun t => inner ℝ h (IBMClockAverageCandidate.direction t) *
    BrownianSignIntegral.signum (IBMConstructedSources.clockPath Y t.toNNReal) * χ (σ t)
  have hB : Measurable (fun t : ℝ => IBMConstructedSources.clockPath Y t.toNNReal) :=
    ((IBMConstructedSources.clockPath Y).continuous.comp continuous_real_toNNReal).measurable
  have hσ : Measurable σ := continuous_abs.measurable.comp hB
  have hc0 : Measurable c :=
    (((continuous_const.inner IBMClockAverageCandidate.direction_continuous).measurable.mul
      (BrownianSignIntegral.signum_measurable.comp hB)).mul (hc.measurable.comp hσ))
  have hg : StronglyMeasurable (fun p : ℝ × SampleSpace =>
      c p.1 * IBMNonlinearClockColumn.value n (σ p.1) p.2) :=
    ((hc0.comp measurable_fst).mul ((IBMNonlinearClockColumn.value_measurable n).comp
      ((hσ.comp measurable_fst).prodMk measurable_snd))).stronglyMeasurable
  change (∫ t, IBMSourceValuedOccupation.fieldValue h
    (fun r => χ r • IBMNonlinearClockColumn.column n r) (t,Y) ∂IBMClockOverlapEnergy.window T)
      =ᵐ[gaussianProduct] fun X => ∫ t, c t*IBMNonlinearClockColumn.value n (σ t) X
        ∂IBMClockOverlapEnergy.window T
  apply BochnerL2RepresentativeFubini.integral_coeFn_ae _
    (IBMSourceValuedOccupation.field_time_integrable h _
      (hc.smul (IBMNonlinearColumnContinuity.column_continuous n)) hs.smul_right T Y)
    _ hg.aestronglyMeasurable
  exact ae_of_all _ fun t => by
    have he : IBMSourceValuedOccupation.fieldValue h
        (χ • IBMNonlinearClockColumn.column n) (t,Y) =
          c t • IBMNonlinearClockColumn.column n (σ t) := by
      simp only [IBMSourceValuedOccupation.fieldValue, c, σ, Pi.smul_apply', smul_smul]
    rw [he]
    filter_upwards [Lp.coeFn_smul (c t) (IBMNonlinearClockColumn.column n (σ t)),
      IBMNonlinearClockColumn.column_actual_ae n (σ t)] with X hm hv
    rw [hm, Pi.smul_apply, hv]
    rfl

/-- Genuine curried clock/source representative of the actual localized native field. -/
theorem nativeField_raw_ae (h : CoefficientSpace) (n : ℕ) (χ : ℝ → ℝ)
    (hc : Continuous χ) (hs : HasCompactSupport χ) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, nativeField h n χ hc hs T Y =ᵐ[gaussianProduct]
      fun X => ∫ t, rawTimeValue h n χ t (X,Y) ∂IBMClockOverlapEnergy.window T := by
  have he := (IBMSourceValuedOccupation.pathField_memLp h _
    (hc.smul (IBMNonlinearColumnContinuity.column_continuous n)) hs.smul_right T).coeFn_toLp
  filter_upwards [he] with Y hY
  change nativeField h n χ hc hs T Y = _ at hY
  rw [hY]
  exact pathField_raw_source_ae h n χ hc hs T Y

/-- Enlarging the containing window leaves the SAME cutoff occupation integral unchanged. -/
theorem limitField_window_eq (h : CoefficientSpace) (χ : ℝ → ℝ)
    (hc : Continuous χ) (hs : HasCompactSupport χ) {a b c d : ℝ}
    (hab : a ≤ b) (hχab : ∀ r, r ∉ Ioc a b → χ r = 0)
    (hcd : c ≤ d) (hχcd : ∀ r, r ∉ Ioc c d → χ r = 0) (T : ℝ≥0) :
    limitField h χ hc hs hab T = limitField h χ hc hs hcd T :=
  tendsto_nhds_unique (nativeField_tendsto h χ hc hs hab hχab T)
    (nativeField_tendsto h χ hc hs hcd hχcd T)

end OperatorDerivativeRewrite.Foundation.IBMNonlinearClockLocalization
