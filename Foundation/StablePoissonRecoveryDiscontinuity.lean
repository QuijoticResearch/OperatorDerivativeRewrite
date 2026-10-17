import Foundation.StablePoissonRecoveryObstruction

/-! Normalized count outputs converge to zero while their required recovered inputs have norm one.
This tests continuity on the range, without assuming a linear recovery algorithm. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.StablePoissonRecoveryDiscontinuity
open PoissonLpLowerObstruction StableLevyAnnuli StablePoissonRecoveryObstruction
set_option backward.isDefEq.respectTransparency false

local instance : Fact (1 ≤ exponent) :=
  ⟨by simpa [exponent] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 4/3 by norm_num)⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def coefficient (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)^3

theorem coefficient_pos (n : ℕ) : 0 < coefficient n := by unfold coefficient; positivity

def normalizedInput (c : ℝ) (hc : 0 < c) (n : ℕ) : Energy μ c :=
  coefficient n • deterministicInput μ c hc (n + 1)

theorem normalizedInput_norm (c : ℝ) (hc : 0 < c) (n : ℕ) :
    ‖normalizedInput (μ := μ) c hc n‖ = 1 := by
  rw [normalizedInput, norm_smul, Real.norm_eq_abs, abs_of_pos (coefficient_pos n),
    deterministicInput_norm]
  simp only [coefficient, Nat.cast_add, Nat.cast_one]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

variable (c : ℝ) (hc : 0 < c) (N : FiniteCountLaws μ c)
  (S : Submodule ℝ (Lp ℝ exponent μ)) (hS : ∀ n, observed c hc N n ∈ S)

def normalizedOutput (n : ℕ) : S := coefficient n • (⟨observed c hc N n, hS n⟩ : S)

theorem normalizedOutput_norm_le (n : ℕ) :
    ‖normalizedOutput c hc N S hS n‖ ≤ 1 / ((n : ℝ) + 1) := by
  rw [normalizedOutput, norm_smul, Real.norm_eq_abs, abs_of_pos (coefficient_pos n)]
  have hout : ‖(⟨observed c hc N n, hS n⟩ : S)‖ ≤ ((n : ℝ) + 1)^2 := by
    change ‖observed c hc N n‖ ≤ _
    simpa only [Nat.cast_add, Nat.cast_one] using observed_norm_le c hc N n
  have h := mul_le_mul_of_nonneg_left hout (le_of_lt (coefficient_pos n))
  apply h.trans_eq
  unfold coefficient
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem normalizedOutput_tendsto :
    Tendsto (normalizedOutput c hc N S hS) atTop (𝓝 0) :=
  squeeze_zero_norm (normalizedOutput_norm_le c hc N S hS)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- This excludes nonlinear continuous recovery as well, if it recovers zero and these scaled tests. -/
theorem recovery_not_continuousAt_zero (R : S → Energy μ c) (hzero : R 0 = 0)
    (hR : ∀ n, R (normalizedOutput c hc N S hS n) = normalizedInput c hc n) :
    ¬ ContinuousAt R 0 := by
  intro hcont
  have ht := hcont.tendsto.comp (normalizedOutput_tendsto c hc N S hS)
  have hn : Tendsto (fun n => ‖R (normalizedOutput c hc N S hS n)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, hzero, norm_zero] using ht.norm
  obtain ⟨n, hn⟩ := (hn.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).exists
  rw [hR n, normalizedInput_norm] at hn
  exact (lt_irrefl (1 : ℝ)) hn

theorem linear_recovery_not_continuousAt_zero (R : S →ₗ[ℝ] Energy μ c)
    (hR : ∀ n, R ⟨observed c hc N n, hS n⟩ = deterministicInput μ c hc (n + 1)) :
    ¬ ContinuousAt R 0 := by
  apply recovery_not_continuousAt_zero c hc N S hS R R.map_zero
  intro n
  simp only [normalizedOutput, map_smul, hR n, normalizedInput]

def observedFour (n : ℕ) : Lp ℝ 4 μ :=
  (observed_memLp_four c hc N n).toLp _

theorem observedFour_norm (n : ℕ) :
    ‖observedFour c hc N n‖ =
      ‖PoissonLpTwoRegime.outputFour (rate (n + 1)) (rate_pos (by omega))‖ := by
  have hX := block_count_law c hc N (n + 1)
  have hm : AEStronglyMeasurable (PoissonPolynomialExamples.centeredCount (rate (n + 1)))
      (Measure.map (N.count (block c (n + 1))) μ) := by
    rw [hX.map_eq]
    exact (PoissonLpTwoRegime.count_memLp_four _ (rate_pos (by omega))).aestronglyMeasurable
  have he := eLpNorm_map_measure (p := 4) hm hX.aemeasurable
  rw [hX.map_eq] at he
  rw [observedFour, PoissonLpTwoRegime.outputFour, Lp.norm_toLp, Lp.norm_toLp]
  exact congrArg ENNReal.toReal he.symm

theorem observedFour_norm_le (n : ℕ) :
    ‖observedFour c hc N n‖ ≤ 2 * ((n : ℝ) + 1)^2 := by
  rw [observedFour_norm]
  have he := PoissonLpTwoRegime.outputFour_energy (rate (n + 1)) (rate_pos (by omega))
  have hr : (rate (n + 1) : ℝ) = ((n : ℝ) + 1)^4 := by
    simp [rate]
  rw [hr] at he
  have hm : 1 ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hp : ((n : ℝ) + 1)^4 ≤ (((n : ℝ) + 1)^4)^2 := by
    have ht : 1 ≤ ((n : ℝ) + 1)^4 := one_le_pow₀ hm
    nlinarith
  by_contra h
  have hlt := pow_lt_pow_left₀ (lt_of_not_ge h) (by positivity) (by norm_num : 4 ≠ 0)
  nlinarith [sq_nonneg (((n : ℝ) + 1)^4)]

def normalizedFour (n : ℕ) : Lp ℝ 4 μ := coefficient n • observedFour c hc N n

theorem normalizedFour_norm_le (n : ℕ) :
    ‖normalizedFour c hc N n‖ ≤ 2 / ((n : ℝ) + 1) := by
  rw [normalizedFour, norm_smul, Real.norm_eq_abs, abs_of_pos (coefficient_pos n)]
  have h := mul_le_mul_of_nonneg_left (observedFour_norm_le c hc N n)
    (le_of_lt (coefficient_pos n))
  apply h.trans_eq
  unfold coefficient
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem normalizedFour_tendsto : Tendsto (normalizedFour c hc N) atTop (𝓝 0) := by
  apply squeeze_zero_norm (normalizedFour_norm_le c hc N)
  simpa only [mul_zero, mul_one_div] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)

theorem normalized_classes_ae (n : ℕ) :
    (fun ω => (normalizedOutput c hc N S hS n : Lp ℝ exponent μ) ω) =ᵐ[μ]
      normalizedFour c hc N n := by
  have hp := lawOutput_ae (N.count (block c (n + 1))) (rate (n + 1))
    (rate_pos (by omega)) (block_count_law c hc N (n + 1))
  have hq := (observed_memLp_four c hc N n).coeFn_toLp
  have hs := Lp.coeFn_smul (coefficient n) (observed c hc N n)
  have ht := Lp.coeFn_smul (coefficient n) (observedFour c hc N n)
  change (coefficient n • observed c hc N n : Lp ℝ exponent μ) =ᵐ[μ]
    (coefficient n • observedFour c hc N n : Lp ℝ 4 μ)
  filter_upwards [hs, ht, hp, hq] with ω hs ht hp hq
  change observed c hc N n ω = _ at hp
  change observedFour c hc N n ω = _ at hq
  simp only [Pi.smul_apply, smul_eq_mul] at hs ht
  rw [hs, ht, hp, hq]

theorem normalized_pair_tendsto :
    Tendsto (fun n => (normalizedOutput c hc N S hS n, normalizedFour c hc N n))
      atTop (𝓝 (0, 0)) :=
  (normalizedOutput_tendsto c hc N S hS).prodMk_nhds (normalizedFour_tendsto c hc N)

/-- Even the topology inherited from both terminal norms cannot make exact recovery continuous. -/
theorem intersection_recovery_not_continuousAt_zero
    (T : Submodule ℝ (S × Lp ℝ 4 μ))
    (hT : ∀ n, (normalizedOutput c hc N S hS n, normalizedFour c hc N n) ∈ T)
    (R : T → Energy μ c) (hzero : R 0 = 0)
    (hR : ∀ n, R ⟨(normalizedOutput c hc N S hS n, normalizedFour c hc N n), hT n⟩ =
      normalizedInput c hc n) : ¬ ContinuousAt R 0 := by
  intro hcont
  have hseq : Tendsto
      (fun n => (⟨(normalizedOutput c hc N S hS n, normalizedFour c hc N n), hT n⟩ : T))
      atTop (𝓝 0) := by
    apply tendsto_subtype_rng.mpr
    exact normalized_pair_tendsto c hc N S hS
  have ht := hcont.tendsto.comp hseq
  have hn : Tendsto
      (fun n => ‖R ⟨(normalizedOutput c hc N S hS n, normalizedFour c hc N n), hT n⟩‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, hzero, norm_zero] using ht.norm
  obtain ⟨n, hn⟩ := (hn.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).exists
  rw [hR n, normalizedInput_norm] at hn
  exact (lt_irrefl (1 : ℝ)) hn

end OperatorDerivativeRewrite.Foundation.StablePoissonRecoveryDiscontinuity
