import Foundation.IBMNonlinearSpatialEnergy

/-! Genuine finite-stage nonlinear source integrals on spatial L2 of a finite
interval, with uniform bounds from the verified covariance/Schur estimate. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearSpatialOperator
open InfiniteGaussian IBMNonlinearSpatialEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

abbrev Space (a b : ℝ) := Lp ℝ 2 (volume.restrict (Ioc a b))

def native (n : ℕ) (a b : ℝ) (u : Space a b) : GaussianL2 :=
  ∫ r in Ioc a b, u r • IBMNonlinearClockColumn.column n r

theorem native_bound (n : ℕ) {a b : ℝ} (hab : a ≤ b) (u : Space a b) :
    ‖native n a b u‖ ≤ Real.sqrt (1+4*(b-a)) * ‖u‖ := by
  have he := original_energy_le_of_memLp n (u : ℝ → ℝ) hab (Lp.memLp u)
  simp only [intervalIntegral.integral_of_le hab] at he
  have hn : (∫ r in Ioc a b, (u r)^2) = ‖u‖^2 := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    exact ae_of_all _ fun r => by simp only [Real.norm_eq_abs, sq_abs]
  rw [hn] at he
  change ‖native n a b u‖^2 ≤ (1+4*(b-a))*‖u‖^2 at he
  have hC : 0 ≤ 1+4*(b-a) := by linarith
  have hs := Real.sq_sqrt hC
  have hp : 0 ≤ Real.sqrt (1+4*(b-a))*‖u‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (native n a b u),sq_nonneg (‖native n a b u‖-
    Real.sqrt (1+4*(b-a))*‖u‖)]

theorem native_add (n : ℕ) (a b : ℝ) (u v : Space a b) :
    native n a b (u+v) = native n a b u + native n a b v := by
  unfold native
  have he : (∫ r in Ioc a b, (u+v) r • IBMNonlinearClockColumn.column n r) =
      ∫ r in Ioc a b, (u r+v r) • IBMNonlinearClockColumn.column n r := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add u v] with r hr
    rw [hr]
    rfl
  rw [he]
  simp_rw [add_smul]
  exact integral_add (weighted_column_integrable_of_memLp n _ a b (Lp.memLp u))
    (weighted_column_integrable_of_memLp n _ a b (Lp.memLp v))

theorem native_smul (n : ℕ) (a b c : ℝ) (u : Space a b) :
    native n a b (c • u) = c • native n a b u := by
  unfold native
  have he : (∫ r in Ioc a b, (c • u) r • IBMNonlinearClockColumn.column n r) =
      ∫ r in Ioc a b, c • (u r • IBMNonlinearClockColumn.column n r) := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c u] with r hr
    rw [hr]
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul]
  rw [he, integral_smul]

def nativeLinear (n : ℕ) (a b : ℝ) : Space a b →ₗ[ℝ] GaussianL2 where
  toFun := native n a b
  map_add' := native_add n a b
  map_smul' := native_smul n a b

/-- The actual rough spatial test operator; no derivative of the test is required. -/
def operator (n : ℕ) {a b : ℝ} (hab : a ≤ b) : Space a b →L[ℝ] GaussianL2 :=
  (nativeLinear n a b).mkContinuous (Real.sqrt (1+4*(b-a))) (native_bound n hab)

theorem operator_apply (n : ℕ) {a b : ℝ} (hab : a ≤ b) (u : Space a b) :
    operator n hab u = ∫ r in Ioc a b, u r • IBMNonlinearClockColumn.column n r := rfl

theorem operator_norm_le (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ‖operator n hab‖ ≤ Real.sqrt (1+4*(b-a)) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (native_bound n hab)

/-- Genuine random source integral for EVERY L2 test on the finite interval. -/
theorem operator_actual_ae (n : ℕ) {a b : ℝ} (hab : a ≤ b) (u : Space a b) :
    operator n hab u =ᵐ[gaussianProduct] fun ω =>
      ∫ r in Ioc a b, u r * IBMNonlinearClockColumn.value n r ω := by
  rw [operator_apply]
  apply BochnerL2RepresentativeFubini.integral_coeFn_ae
    (fun r => u r • IBMNonlinearClockColumn.column n r)
    (weighted_column_integrable_of_memLp n _ a b (Lp.memLp u))
    (fun p : ℝ × SampleSpace => u p.1 * IBMNonlinearClockColumn.value n p.1 p.2)
  · exact (Lp.aestronglyMeasurable u).comp_fst.mul
      (IBMNonlinearClockColumn.value_measurable n).aestronglyMeasurable
  · exact ae_of_all _ fun r => by
      filter_upwards [Lp.coeFn_smul (u r) (IBMNonlinearClockColumn.column n r),
        IBMNonlinearClockColumn.column_actual_ae n r] with ω hs hc
      rw [hs, Pi.smul_apply, hc]
      rfl

theorem operator_actual_memLp (n : ℕ) {a b : ℝ} (hab : a ≤ b) (u : Space a b) :
    MemLp (fun ω => ∫ r in Ioc a b, u r * IBMNonlinearClockColumn.value n r ω)
      2 gaussianProduct := (Lp.memLp (operator n hab u)).ae_eq (operator_actual_ae n hab u)

end OperatorDerivativeRewrite.Foundation.IBMNonlinearSpatialOperator
