import Foundation.PoissonDifferenceOperators

/-! Continuous coordinate evaluations on positive-atom Poisson Hilbert spaces. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonCoordinateEvaluation
open PoissonDifferenceCore PoissonDifferenceOperators

variable (rate : ℝ≥0) (hr : 0 < rate)

/-- Evaluation at a Poisson atom as a continuous linear map. -/
def scalarCoordinate (_hr : 0 < rate) (n : ℕ) : ScalarL2 rate →L[ℝ] ℝ :=
  (poissonWeight rate n)⁻¹ • innerSL ℝ (scalarFinsupp rate (Finsupp.single n 1))

/-- Evaluation at a rate-weighted Poisson atom as a continuous linear map. -/
def fieldCoordinate (_hr : 0 < rate) (n : ℕ) : FieldL2 rate →L[ℝ] ℝ :=
  ((rate : ℝ) * poissonWeight rate n)⁻¹ •
    innerSL ℝ (fieldFinsupp rate (Finsupp.single n 1))

theorem scalarCoordinate_apply (v : ScalarL2 rate) (n : ℕ) :
    scalarCoordinate rate hr n v = v n := by
  have hw : poissonWeight rate n ≠ 0 := ne_of_gt (poisson_weight_pos rate hr n)
  simp [scalarCoordinate, scalar_inner_single, hw]

theorem fieldCoordinate_apply (v : FieldL2 rate) (n : ℕ) :
    fieldCoordinate rate hr n v = v n := by
  have hw : poissonWeight rate n ≠ 0 := ne_of_gt (poisson_weight_pos rate hr n)
  have hr0 : (rate : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  change ((rate : ℝ) * poissonWeight rate n)⁻¹ *
    inner ℝ (fieldFinsupp rate (Finsupp.single n 1)) v = v n
  rw [field_inner_single rate hr, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hr0 hw), one_mul]

/-- Hilbert convergence of scalar classes implies convergence at each positive-mass count. -/
theorem scalar_coordinate_tendsto (hr : 0 < rate) {v : ℕ → ScalarL2 rate} {z : ScalarL2 rate}
    (hv : Filter.Tendsto v Filter.atTop (nhds z)) (n : ℕ) :
    Filter.Tendsto (fun k => (v k : ℕ → ℝ) n) Filter.atTop (nhds (z n)) := by
  simpa only [Function.comp_def, scalarCoordinate_apply rate hr] using
    (scalarCoordinate rate hr n).continuous.continuousAt.tendsto.comp hv

/-- Hilbert convergence of field classes implies convergence at each positive-mass count. -/
theorem field_coordinate_tendsto (hr : 0 < rate) {v : ℕ → FieldL2 rate} {z : FieldL2 rate}
    (hv : Filter.Tendsto v Filter.atTop (nhds z)) (n : ℕ) :
    Filter.Tendsto (fun k => (v k : ℕ → ℝ) n) Filter.atTop (nhds (z n)) := by
  simpa only [Function.comp_def, fieldCoordinate_apply rate hr] using
    (fieldCoordinate rate hr n).continuous.continuousAt.tendsto.comp hv

/-- Representative addition is pointwise because every Poisson atom has positive mass. -/
theorem scalar_add_apply (hr : 0 < rate) (v w : ScalarL2 rate) (n : ℕ) :
    (v + w : ScalarL2 rate) n = v n + w n := by
  rw [← scalarCoordinate_apply rate hr, map_add,
    scalarCoordinate_apply rate hr, scalarCoordinate_apply rate hr]

theorem scalar_smul_apply (hr : 0 < rate) (c : ℝ) (v : ScalarL2 rate) (n : ℕ) :
    (c • v : ScalarL2 rate) n = c * v n := by
  rw [← scalarCoordinate_apply rate hr, map_smul,
    scalarCoordinate_apply rate hr]
  rfl

theorem scalar_zero_apply (hr : 0 < rate) (n : ℕ) : (0 : ScalarL2 rate) n = 0 := by
  rw [← scalarCoordinate_apply rate hr, map_zero]

theorem field_add_apply (hr : 0 < rate) (v w : FieldL2 rate) (n : ℕ) :
    (v + w : FieldL2 rate) n = v n + w n := by
  rw [← fieldCoordinate_apply rate hr, map_add,
    fieldCoordinate_apply rate hr, fieldCoordinate_apply rate hr]

theorem field_smul_apply (hr : 0 < rate) (c : ℝ) (v : FieldL2 rate) (n : ℕ) :
    (c • v : FieldL2 rate) n = c * v n := by
  rw [← fieldCoordinate_apply rate hr, map_smul,
    fieldCoordinate_apply rate hr]
  rfl

theorem field_zero_apply (hr : 0 < rate) (n : ℕ) : (0 : FieldL2 rate) n = 0 := by
  rw [← fieldCoordinate_apply rate hr, map_zero]

/-- Coordinate evaluation of a scalar L² representative is continuous. -/
theorem continuous_scalar_apply (hr : 0 < rate) (n : ℕ) :
    Continuous (fun v : ScalarL2 rate => (v : ℕ → ℝ) n) := by
  convert (scalarCoordinate rate hr n).continuous using 1
  funext v
  exact (scalarCoordinate_apply rate hr v n).symm

/-- Coordinate evaluation of a weighted-field L² representative is continuous. -/
theorem continuous_field_apply (hr : 0 < rate) (n : ℕ) :
    Continuous (fun v : FieldL2 rate => (v : ℕ → ℝ) n) := by
  convert (fieldCoordinate rate hr n).continuous using 1
  funext v
  exact (fieldCoordinate_apply rate hr v n).symm

/-- A finite-support scalar L² class equals its defining function at every Poisson atom. -/
theorem scalarFinsupp_apply (hr : 0 < rate) (f : ℕ →₀ ℝ) (n : ℕ) :
    (scalarFinsupp rate f) n = f n :=
  ae_eq_implies_pointwise rate hr (scalarFinsupp_coeFn rate f) n

/-- A finite-support field L² class equals its defining function at every Poisson atom. -/
theorem fieldFinsupp_apply (hr : 0 < rate) (u : ℕ →₀ ℝ) (n : ℕ) :
    (fieldFinsupp rate u) n = u n := by
  have hr0 : (rate : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  exact ae_eq_implies_pointwise rate hr
    ((Measure.ae_ennreal_smul_measure_iff hr0).mp (fieldFinsupp_coeFn rate u)) n

end OperatorDerivativeRewrite.Foundation.PoissonCoordinateEvaluation
