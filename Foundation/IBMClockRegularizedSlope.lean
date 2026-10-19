import Foundation.IBMNormalizedSlopeGraph
import Foundation.GaussianClockValueOperators

/-! A full-source realization of the shifted regularized signed slope at
each positive time, with uniform time-zero energy and genuine strong limits. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockRegularizedSlope
open InfiniteGaussian IBMNormalizedClockProfiles IBMNormalizedSlopeGraph
open IBMSchwartzFullReflectedIto GaussianClockValueOperators GaussianDirectionalRecovery
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

/-- The independently identified actual slope class, with all source chaos. -/
def pointSlope (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (T : ℝ≥0) (hT : 0 < T) : Field :=
  (Real.sqrt (T : ℝ))⁻¹ • sampledSlope g a n T hT

theorem pointSlope_actual_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ≥0} (hT : 0 < T) :
    pointSlope g a n T hT =ᵐ[gaussianProduct] fun ω =>
      signedSlope g a n (IBMConstructedSources.clockPath ω T) := by
  have hz : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (show 0 < (T : ℝ) from hT))
  filter_upwards [Lp.coeFn_smul (Real.sqrt (T : ℝ))⁻¹ (sampledSlope g a n T hT),
    sampledSlope_actual_ae g a n hT] with ω hs hp
  change pointSlope g a n T hT ω = _ at hs
  rw [hs,Pi.smul_apply,hp,smul_smul,inv_mul_cancel₀ hz,one_smul]

def normalizedRecovery (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (T : ℝ≥0) : Field :=
  clockLift (directionalRecovery (unitDirection T)) (endpointClass g a n T)

/-- Exact full-source equality in EVERY clock sector, identified using the
actual weak derivative. Completeness makes this a unique regularization. -/
theorem normalizedRecovery_projection (g : SchwartzMap ℝ ℝ) (a : ℝ) (n k : ℕ)
    {T : ℝ≥0} (hT : 0 < T) :
    clockLift (GaussianNumberSectors.projection k) (normalizedRecovery g a n T) =
      (k + 1 : ℝ)⁻¹ • clockLift (GaussianNumberSectors.projection k) (sampledSlope g a n T hT) := by
  apply eq_of_all_tests
  intro L
  change L.compLpL 2 gaussianProduct
    (clockLift (GaussianNumberSectors.projection k)
      (clockLift (directionalRecovery (unitDirection T)) (endpointClass g a n T))) = _
  rw [clockLift_test,clockLift_test,map_smul,clockLift_test]
  exact shifted_derivative_projection _ (unitDirection_norm hT)
    (tested_sampled_closed_graph g a n hT L) k

theorem normalizedRecovery_norm_le (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ≥0} (hT : 0 < T) :
    ‖normalizedRecovery g a n T‖ ≤ ‖endpointClass g a n T‖ := by
  have hh := clockRecovery_norm_le (unitDirection T) (endpointClass g a n T)
  simpa only [normalizedRecovery,unitDirection_norm hT,one_mul] using hh

def recoveredSlope (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : Field :=
  (Real.sqrt (T : ℝ))⁻¹ • normalizedRecovery g a n T

theorem recoveredSlope_projection (g : SchwartzMap ℝ ℝ) (a : ℝ) (n k : ℕ)
    {T : ℝ≥0} (hT : 0 < T) :
    clockLift (GaussianNumberSectors.projection k) (recoveredSlope g a n T) =
      (k + 1 : ℝ)⁻¹ • clockLift (GaussianNumberSectors.projection k) (pointSlope g a n T hT) := by
  change clockLift (GaussianNumberSectors.projection k)
    ((Real.sqrt (T : ℝ))⁻¹ • normalizedRecovery g a n T) = _
  rw [map_smul,normalizedRecovery_projection g a n k hT]
  change _ = (k + 1 : ℝ)⁻¹ • clockLift (GaussianNumberSectors.projection k)
    ((Real.sqrt (T : ℝ))⁻¹ • sampledSlope g a n T hT)
  rw [map_smul,smul_comm]

/-- The correct integrable squared-energy scale at time zero; uniform in
the concrete mollifier family and retaining ALL source and clock sectors. -/
theorem recoveredSlope_uniform_energy (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ≥0} (hT : 0 < T) :
    ‖recoveredSlope g a n T‖ ^ 2 ≤ slopeBound g ^ 2 * absoluteMoment / Real.sqrt (T : ℝ) := by
  have hp : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr (show 0 < (T : ℝ) from hT)
  have hb : ‖normalizedRecovery g a n T‖ ^ 2 ≤
      slopeBound g ^ 2 * Real.sqrt (T : ℝ) * absoluteMoment :=
    (pow_le_pow_left₀ (norm_nonneg _) (normalizedRecovery_norm_le g a n hT) 2).trans
      (endpoint_uniform_energy g a n hT)
  rw [recoveredSlope,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),mul_pow]
  apply (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans_eq
  field_simp

theorem recoveredSlope_unique (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ≥0} (hT : 0 < T) {q : Field}
    (hq : ∀ k : ℕ, clockLift (GaussianNumberSectors.projection k) q =
      (k + 1 : ℝ)⁻¹ • clockLift (GaussianNumberSectors.projection k) (pointSlope g a n T hT)) :
    q = recoveredSlope g a n T := by
  apply eq_of_clock_projections
  intro k
  rw [hq k,recoveredSlope_projection g a n k hT]

/-- The regularization is the strong FULL joint-L2 sum of the actual signed
slope's shifted chaos series, rather than only agreement of scalar tests. -/
theorem recoveredSlope_chaos_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun N => ∑ k ∈ Finset.range (N + 1),
      (k + 1 : ℝ)⁻¹ • clockLift (GaussianNumberSectors.projection k) (pointSlope g a n T hT))
        atTop (𝓝 (recoveredSlope g a n T)) := by
  have hh := clock_truncation_tendsto (recoveredSlope g a n T)
  simpa only [clock_truncation_eq,recoveredSlope_projection g a n _ hT] using hh

def recoveredSlopeLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : Field :=
  (Real.sqrt (T : ℝ))⁻¹ •
    clockLift (directionalRecovery (unitDirection T)) (endpointLimitClass g a T)

/-- Strong full joint-L2 convergence at each fixed positive time. Strong
time-integrated convergence and predictability remain separate obligations. -/
theorem recoveredSlope_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => recoveredSlope g a n T) atTop (𝓝 (recoveredSlopeLimit g a T)) :=
  tendsto_const_nhds.smul
    ((clockLift (directionalRecovery (unitDirection T))).continuous.tendsto _ |>.comp
      (endpointClass_tendsto g a T))

theorem recoveredSlopeLimit_energy (g : SchwartzMap ℝ ℝ) (a : ℝ)
    {T : ℝ≥0} (hT : 0 < T) :
    ‖recoveredSlopeLimit g a T‖ ^ 2 ≤ slopeBound g ^ 2 * absoluteMoment / Real.sqrt (T : ℝ) :=
  le_of_tendsto ((recoveredSlope_tendsto g a T).norm.pow 2)
    (Eventually.of_forall fun n => recoveredSlope_uniform_energy g a n hT)

end OperatorDerivativeRewrite.Foundation.IBMClockRegularizedSlope
