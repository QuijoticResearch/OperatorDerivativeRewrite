import Foundation.BackwardHeatMovingObstruction
import Foundation.LpStrongOperatorConvergence
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Uniformly bounded, jointly continuous path observables define continuous actual Lp processes. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.BoundedMovingLpProcess
open HigherHeatContinuousCylinders HigherHeatLpControls

variable (μ : Measure Path) [IsFiniteMeasure μ] (m : ℕ) [Fact (0 < m)]

def process (F : ℝ → (Path →ᵇ ℂ)) (t : ℝ) : Lp ℂ (power m) μ :=
  BoundedContinuousFunction.toLp (power m) μ ℂ (F t)

theorem process_ae (F : ℝ → (Path →ᵇ ℂ)) (t : ℝ) :
    process μ m F t =ᵐ[μ] F t :=
  BoundedContinuousFunction.coeFn_toLp (power m) μ ℂ (F t)

theorem continuous_process (F : ℝ → (Path →ᵇ ℂ))
    (hj : Continuous (fun z : ℝ × Path => F z.1 z.2)) (K : ℝ)
    (hb : ∀ t ω, ‖F t ω‖ ≤ K) : Continuous (process μ m F) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hp : 2*m ≠ 0 := by have := (inferInstance : Fact (0 < m)).out; omega
  have hn (t : ℝ) (ω : Path) : ‖F t ω - F s ω‖ ≤ 2*K := by
    calc
      _ ≤ ‖F t ω‖ + ‖F s ω‖ := norm_sub_le _ _
      _ ≤ K+K := add_le_add (hb t ω) (hb s ω)
      _ = _ := by ring
  have hI : Continuous (fun t => ∫ ω, ‖F t ω - F s ω‖^(2*m) ∂μ) := by
    apply continuous_of_dominated (bound := fun _ : Path => (2*K)^(2*m))
    · intro t
      exact (((F t).continuous.sub (F s).continuous).norm.pow _).aestronglyMeasurable
    · intro t
      exact Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hn t ω) (2*m))
    · exact integrable_const _
    · exact Eventually.of_forall (fun ω =>
        (((hj.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow _))
  have he (t : ℝ) : ‖process μ m F t - process μ m F s‖ =
      (∫ ω, ‖F t ω - F s ω‖^(2*m) ∂μ) ^ (((2*m : ℕ) : ℝ)⁻¹) := by
    rw [LpStrongOperatorConvergence.norm_integral μ m]
    congr 1
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (process μ m F t) (process μ m F s),
      process_ae μ m F t, process_ae μ m F s] with ω hsub ht hs
    rw [hsub]
    simp only [Pi.sub_apply, ht, hs]
  have hzero : (∫ ω, ‖F s ω - F s ω‖^(2*m) ∂μ) = 0 := by
    simp [hp]
  have ht := (Real.continuous_rpow_const
    (show 0 ≤ (((2*m : ℕ) : ℝ)⁻¹) by positivity)).continuousAt.tendsto.comp
      (hI.continuousAt (x := s)).tendsto
  rw [hzero, Real.zero_rpow (by positivity : (((2*m : ℕ) : ℝ)⁻¹) ≠ 0)] at ht
  exact (tendsto_iff_norm_sub_tendsto_zero.mpr
    (by simpa only [Function.comp_def, he] using ht))

theorem process_norm_bound (F : ℝ → (Path →ᵇ ℂ)) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ t ω, ‖F t ω‖ ≤ K) (t : ℝ) :
    ‖process μ m F t‖ ≤ measureUnivNNReal μ ^ (power m).toReal⁻¹ * K := by
  apply Lp.norm_le_of_ae_bound hK
  filter_upwards [process_ae μ m F t] with ω he
  rw [he]
  exact hb t ω

theorem process_memLp (F : ℝ → (Path →ᵇ ℂ))
    (hj : Continuous (fun z : ℝ × Path => F z.1 z.2)) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ t ω, ‖F t ω‖ ≤ K) (q : ℝ≥0∞) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    MemLp (process μ m F) q ν := by
  have hC : 0 ≤ measureUnivNNReal μ ^ (power m).toReal⁻¹ * K := by positivity
  have hc : MemLp (fun _ : ℝ =>
      (measureUnivNNReal μ ^ (power m).toReal⁻¹ * K : ℝ)) q ν := memLp_const _
  apply hc.mono (continuous_process μ m F hj K hb).aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using process_norm_bound μ m F K hK hb t)

end OperatorDerivativeRewrite.Foundation.BoundedMovingLpProcess
