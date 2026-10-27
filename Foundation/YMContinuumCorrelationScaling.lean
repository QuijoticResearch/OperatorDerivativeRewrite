import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform lattice-step decay at a fixed positive physical separation

If the number of lattice blocks between two fixed physical supports tends to
infinity, a uniform factor `q < 1` and a uniform amplitude force their
connected correlation to vanish. This is a conditional scaling obstruction
for a proposed continuum two-point function, not a theorem about any
particular Yang--Mills measure. Scale-dependent observable normalization or
amplitude bounds can change the conclusion and must be tracked separately.
-/

open Filter
open scoped Topology

namespace OperatorDerivativeRewrite.Foundation.YMContinuumCorrelationScaling

theorem uniform_block_bound_forces_zero
    (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : ℕ → ℝ) (h : ∀ n, |S n| ≤ C * q ^ n) :
    Tendsto S atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hu : Tendsto (fun n : ℕ => C * q ^ n) atTop (𝓝 0) := by
    simpa using hp.const_mul C
  have hl : Tendsto (fun n : ℕ => -(C * q ^ n)) atTop (𝓝 0) := by
    simpa using hu.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · exact Filter.Eventually.of_forall (fun n => (abs_le.mp (h n)).1)
  · exact Filter.Eventually.of_forall (fun n => (abs_le.mp (h n)).2)

theorem no_nonzero_limit_with_uniform_block_bound
    (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : ℕ → ℝ) (s : ℝ)
    (h : ∀ n, |S n| ≤ C * q ^ n)
    (hs : Tendsto S atTop (𝓝 s)) (hs0 : s ≠ 0) : False := by
  have hz := uniform_block_bound_forces_zero C q hq0 hq1 S h
  exact hs0 (tendsto_nhds_unique hs hz)

/-! If a positive cross covariance is normalized to one by multiplying
both observables by `S n` to the power `-1/2`, a nonvanishing raw variance
cannot remain uniformly bounded when `S n` has uniform block decay. -/

theorem no_uniform_variance_after_unit_covariance
    (C q v : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hv : 0 < v)
    (S V : ℕ → ℝ)
    (hSpos : ∀ n, 0 < S n)
    (hdecay : ∀ n, |S n| ≤ C * q ^ n)
    (hvar : ∀ n, v ≤ V n) :
    ¬ ∃ M : ℝ, ∀ n, V n / S n ≤ M := by
  rintro ⟨M, hM⟩
  have hzero := uniform_block_bound_forces_zero C q hq0 hq1 S hdecay
  have hMzero : Tendsto (fun n : ℕ => M * S n) atTop (𝓝 0) := by
    simpa using hzero.const_mul M
  have hev : ∀ᶠ n : ℕ in atTop, v ≤ M * S n := by
    filter_upwards [] with n
    exact (hvar n).trans ((div_le_iff₀ (hSpos n)).mp (hM n))
  have hv0 : v ≤ 0 := ge_of_tendsto hMzero hev
  linarith

end OperatorDerivativeRewrite.Foundation.YMContinuumCorrelationScaling
