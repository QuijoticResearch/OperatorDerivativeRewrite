import Foundation.SU2PointEntropy

/-! Exact reset mixtures and measurable-event mixing for the stationary SU2 loop chain. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.SU2InteractingLoopKernel
open OperatorDerivativeRewrite.Foundation.SU2LoopEquilibrium
open OperatorDerivativeRewrite.Foundation.SU2ResidualEntropy

namespace OperatorDerivativeRewrite.Foundation.SU2EventMixing

def resetCoefficient (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal (reset r)
def residualCoefficient (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1 - reset r)

def residualIterate (r : ℝ) (ρ : Measure SU2) : ℕ → Measure SU2
  | 0 => ρ
  | n + 1 => residualKernel r ∘ₘ residualIterate r ρ n

def stationaryWeight (r : ℝ) : ℕ → ℝ≥0∞
  | 0 => 0
  | n + 1 => stationaryWeight r n + (residualCoefficient r)^n * resetCoefficient r

theorem residualIterate_probability (r : ℝ) (ρ : Measure SU2)
    [IsProbabilityMeasure ρ] (n : ℕ) :
    IsProbabilityMeasure (residualIterate r ρ n) := by
  induction n with
  | zero => simpa [residualIterate] using (inferInstance : IsProbabilityMeasure ρ)
  | succ n ih =>
      letI : IsProbabilityMeasure (residualIterate r ρ n) := ih
      letI : IsMarkovKernel (residualKernel r) := residualKernel_markov r
      change IsProbabilityMeasure (residualKernel r ∘ₘ residualIterate r ρ n)
      infer_instance

theorem coefficient_sum_one (r : ℝ) : resetCoefficient r + residualCoefficient r = 1 := by
  have hr : 0 ≤ reset r := (reset_pos r).le
  have hc : 0 ≤ 1 - reset r := (sub_pos.mpr (reset_lt_one r)).le
  rw [resetCoefficient, residualCoefficient, ← ENNReal.ofReal_add hr hc]
  norm_num

theorem stationaryWeight_complement (r : ℝ) (n : ℕ) :
    stationaryWeight r n + (residualCoefficient r)^n = 1 := by
  induction n with
  | zero => simp [stationaryWeight]
  | succ n ih =>
      change stationaryWeight r n + (residualCoefficient r)^n * resetCoefficient r + (residualCoefficient r)^(n+1) = 1
      rw [pow_succ]
      calc
        stationaryWeight r n + (residualCoefficient r)^n * resetCoefficient r + (residualCoefficient r)^n * residualCoefficient r =
          stationaryWeight r n + (residualCoefficient r)^n * (resetCoefficient r + residualCoefficient r) := by ring
        _ = _ := by rw [coefficient_sum_one, mul_one, ih]

theorem exact_mixture (r : ℝ) (ρ : Measure SU2)
    [IsProbabilityMeasure ρ] (n : ℕ) :
    iterateLaw r ρ n = stationaryWeight r n • equilibriumLaw r +
      (residualCoefficient r)^n • residualIterate r ρ n := by
  induction n with
  | zero => simp [iterateLaw, stationaryWeight, residualIterate]
  | succ n ih =>
      letI : IsProbabilityMeasure (residualIterate r ρ n) :=
        residualIterate_probability r ρ n
      change loopKernel r ∘ₘ iterateLaw r ρ n = _
      rw [ih, Measure.comp_add, Measure.comp_smul, Measure.comp_smul,
        equilibriumLaw_stationary]
      rw [← forward_split r (residualIterate r ρ n)]
      simp only [smul_add, smul_smul, ← add_assoc]
      rw [← add_smul]
      simp [stationaryWeight, residualIterate, residualCoefficient, resetCoefficient, pow_succ]


theorem event_upper (r : ℝ) (ρ : Measure SU2)
    [IsProbabilityMeasure ρ] (n : ℕ) (B : Set SU2) :
    iterateLaw r ρ n B ≤ equilibriumLaw r B + (residualCoefficient r)^n := by
  letI : IsProbabilityMeasure (residualIterate r ρ n) :=
    residualIterate_probability r ρ n
  have hmix := congrArg (fun ν : Measure SU2 => ν B) (exact_mixture r ρ n)
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at hmix
  rw [hmix]
  have ha : stationaryWeight r n ≤ 1 := by
    calc
      _ ≤ stationaryWeight r n + (residualCoefficient r)^n := le_add_right le_rfl
      _ = 1 := stationaryWeight_complement r n
  have hB : residualIterate r ρ n B ≤ 1 := by
    calc
      _ ≤ residualIterate r ρ n Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  calc
    stationaryWeight r n * equilibriumLaw r B +
      (residualCoefficient r)^n * residualIterate r ρ n B ≤
      1 * equilibriumLaw r B + (residualCoefficient r)^n * 1 := by gcongr
    _ = _ := by simp

theorem event_lower (r : ℝ) (ρ : Measure SU2)
    [IsProbabilityMeasure ρ] (n : ℕ) (B : Set SU2) :
    equilibriumLaw r B ≤ iterateLaw r ρ n B + (residualCoefficient r)^n := by
  letI : IsProbabilityMeasure (residualIterate r ρ n) :=
    residualIterate_probability r ρ n
  letI : IsProbabilityMeasure (equilibriumLaw r) := equilibriumLaw_probability r
  have hmix := congrArg (fun ν : Measure SU2 => ν B) (exact_mixture r ρ n)
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at hmix
  have hB : equilibriumLaw r B ≤ 1 := by
    calc
      _ ≤ equilibriumLaw r Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hπ : equilibriumLaw r B = stationaryWeight r n * equilibriumLaw r B +
      (residualCoefficient r)^n * equilibriumLaw r B := by
    rw [← add_mul, stationaryWeight_complement, one_mul]
  calc
    equilibriumLaw r B = stationaryWeight r n * equilibriumLaw r B +
        (residualCoefficient r)^n * equilibriumLaw r B := hπ
    _ ≤ stationaryWeight r n * equilibriumLaw r B + (residualCoefficient r)^n := by
      simpa using add_le_add_right (mul_le_mul_of_nonneg_left hB bot_le)
        (stationaryWeight r n * equilibriumLaw r B)
    _ ≤ iterateLaw r ρ n B + (residualCoefficient r)^n := by
      rw [hmix]
      have hx : stationaryWeight r n * equilibriumLaw r B ≤
          stationaryWeight r n * equilibriumLaw r B +
            (residualCoefficient r)^n * residualIterate r ρ n B := le_add_right le_rfl
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_right hx ((residualCoefficient r)^n))

theorem c_lt_one (r : ℝ) : residualCoefficient r < 1 := by
  rw [residualCoefficient, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_lt_ofReal_iff'.mpr
    ⟨by linarith [reset_pos r], by norm_num⟩

theorem event_tendsto_equilibrium (r : ℝ) (ρ : Measure SU2)
    [IsProbabilityMeasure ρ] (B : Set SU2) :
    Filter.Tendsto (fun n : ℕ => iterateLaw r ρ n B)
      Filter.atTop (𝓝 (equilibriumLaw r B)) := by
  letI : IsProbabilityMeasure (equilibriumLaw r) := equilibriumLaw_probability r
  have hπfin : equilibriumLaw r B ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ B))
  have hpow : Tendsto (fun n : ℕ => (residualCoefficient r)^n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (c_lt_one r)
  have hweight : Tendsto (fun n : ℕ => stationaryWeight r n) atTop (𝓝 1) := by
    have heq : (fun n : ℕ => stationaryWeight r n) =
        (fun n : ℕ => 1 - (residualCoefficient r)^n) := by
      funext n
      exact ENNReal.eq_sub_of_add_eq' (by simp) (stationaryWeight_complement r n)
    rw [heq]
    simpa using (ENNReal.Tendsto.sub tendsto_const_nhds hpow
      (Or.inl (by simp : (1 : ℝ≥0∞) ≠ ⊤)))
  have hfirst : Tendsto (fun n : ℕ => stationaryWeight r n * equilibriumLaw r B)
      atTop (𝓝 (equilibriumLaw r B)) := by
    simpa using ENNReal.Tendsto.mul_const hweight (Or.inr hπfin)
  have hrem : Tendsto (fun n : ℕ => (residualCoefficient r)^n * residualIterate r ρ n B)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow
    · exact fun n => bot_le
    · intro n
      letI : IsProbabilityMeasure (residualIterate r ρ n) :=
        residualIterate_probability r ρ n
      have hB : residualIterate r ρ n B ≤ 1 := by
        calc
          _ ≤ residualIterate r ρ n Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      simpa using mul_le_mul_of_nonneg_left hB bot_le
  have hsum := hfirst.add hrem
  have heq : (fun n : ℕ => iterateLaw r ρ n B) =
      (fun n : ℕ => stationaryWeight r n * equilibriumLaw r B +
        (residualCoefficient r)^n * residualIterate r ρ n B) := by
    funext n
    have h := congrArg (fun ν : Measure SU2 => ν B) (exact_mixture r ρ n)
    simpa only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] using h
  rw [heq]
  simpa using hsum
end OperatorDerivativeRewrite.Foundation.SU2EventMixing
