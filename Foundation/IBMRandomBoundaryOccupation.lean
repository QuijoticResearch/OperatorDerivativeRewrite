import Foundation.IBMRandomTerminalBoundary
import Foundation.BochnerL2Approximation

/-! Literal occupation of shrinking neighborhoods of the RANDOM terminal
folded-clock level converges strongly in actual clock L2. This does not yet
control increment-weighted boundary terms in clipped quadratic variation. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRandomBoundaryOccupation
open InfiniteGaussian IBMRandomTerminalBoundary IBMClockOverlapEnergy

def band (δ : ℝ) (T : ℝ≥0) (z : ℝ × SampleSpace) : ℝ :=
  if distance T z ≤ δ then 1 else 0

theorem band_measurable (δ : ℝ) (T : ℝ≥0) : Measurable (band δ T) :=
  Measurable.ite (measurableSet_le (distance_measurable T) measurable_const)
    measurable_const measurable_const

theorem band_bounds (δ : ℝ) (T : ℝ≥0) (z : ℝ × SampleSpace) :
    0 ≤ band δ T z ∧ band δ T z ≤ 1 := by
  unfold band
  split_ifs <;> constructor <;> norm_num

theorem band_norm_bound (δ : ℝ) (T : ℝ≥0) (z : ℝ × SampleSpace) : ‖band δ T z‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (band_bounds δ T z).1]
  exact (band_bounds δ T z).2

theorem band_time_integrable (δ : ℝ) (T : ℝ≥0) (Y : SampleSpace) :
    Integrable (fun t => band δ T (t,Y)) (window T) :=
  Integrable.of_bound (((band_measurable δ T).comp
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable) 1
      (ae_of_all _ fun t => band_norm_bound δ T (t,Y))

def occupation (δ : ℝ) (T : ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∫ t, band δ T (t,Y) ∂window T

theorem occupation_measurable (δ : ℝ) (T : ℝ≥0) : Measurable (occupation δ T) :=
  ((band_measurable δ T).stronglyMeasurable.integral_prod_left' (μ:=window T)).measurable

theorem occupation_bound (δ : ℝ) (T : ℝ≥0) (Y : SampleSpace) : ‖occupation δ T Y‖ ≤ T := by
  have hi := norm_integral_le_of_norm_le_const
    (ae_of_all (window (T:ℝ)) fun t => band_norm_bound δ T (t,Y))
  simpa [occupation,window,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal T.property] using hi

theorem occupation_nonneg (δ : ℝ) (T : ℝ≥0) (Y : SampleSpace) : 0 ≤ occupation δ T Y :=
  integral_nonneg fun t => (band_bounds δ T (t,Y)).1

theorem occupation_memLp (δ : ℝ) (T : ℝ≥0) : MemLp (occupation δ T) 2 gaussianProduct :=
  MemLp.of_bound (occupation_measurable δ T).aestronglyMeasurable T
    (ae_of_all _ fun Y => occupation_bound δ T Y)

def occupationClass (δ : ℝ) (T : ℝ≥0) : GaussianL2 := (occupation_memLp δ T).toLp _

theorem occupationClass_actual (δ : ℝ) (T : ℝ≥0) :
    occupationClass δ T =ᵐ[gaussianProduct] occupation δ T := (occupation_memLp δ T).coeFn_toLp

theorem occupation_tendsto_ae (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, Tendsto (fun n => occupation (δ n) T Y) atTop (𝓝 0) := by
  filter_upwards [distance_positive_ae T] with Y hY
  have ht : ∀ᵐ t ∂window T, Tendsto (fun n => band (δ n) T (t,Y)) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hY] with t ht
    have he := (tendsto_order.1 hδ).2 (distance T (t,Y)) ht
    apply (tendsto_const_nhds (x:=(0:ℝ))).congr'
    filter_upwards [he] with n hn
    simp only [band,if_neg (not_le_of_gt hn)]
  have hi := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
    (fun n => ((band_measurable (δ n) T).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (integrable_const (1:ℝ) : Integrable _ (window T))
    (fun n => ae_of_all _ fun t => band_norm_bound (δ n) T (t,Y)) ht
  simpa only [occupation,Function.comp_def,id_eq,integral_zero] using hi

theorem occupationClass_tendsto (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun n => occupationClass (δ n) T) atTop (𝓝 (0:GaussianL2)) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _ (Lp.const 2 gaussianProduct (T:ℝ))
  · intro n
    filter_upwards [occupationClass_actual (δ n) T,Lp.coeFn_const 2 gaussianProduct (T:ℝ)] with Y hn hb
    rw [hn,hb]
    change ‖occupation (δ n) T Y‖ ≤ ‖(T:ℝ)‖
    exact (occupation_bound (δ n) T Y).trans (Real.le_norm_self (T:ℝ))
  · filter_upwards [Lp.coeFn_zero ℝ 2 gaussianProduct] with Y hz
    rw [hz]
    simp only [Pi.zero_apply,norm_zero]
    exact norm_nonneg _
  · filter_upwards [occupation_tendsto_ae δ hδ T,
      ae_all_iff.mpr (fun n => occupationClass_actual (δ n) T),Lp.coeFn_zero ℝ 2 gaussianProduct]
        with Y hY he hz
    rw [hz]
    exact hY.congr' (Eventually.of_forall fun n => (he n).symm)

end OperatorDerivativeRewrite.Foundation.IBMRandomBoundaryOccupation
