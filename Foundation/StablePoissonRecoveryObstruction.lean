import Foundation.PoissonLpTwoRegime

/-! A bounded recovery obstruction on any range containing the elementary count outputs.
The assumptions specify finite-set count laws, not a construction of a random measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.StablePoissonRecoveryObstruction
open PoissonLpLowerObstruction StableLevyAnnuli
set_option backward.isDefEq.respectTransparency false

local instance : Fact (1 ≤ exponent) :=
  ⟨by simpa [exponent] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 4/3 by norm_num)⟩

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def energyMeasure (c : ℝ) : Measure ((ℝ × ℝ) × Ω) := (controlMeasure c).prod μ
def energyBlock (c : ℝ) (n : ℕ) : Set ((ℝ × ℝ) × Ω) := block c n ×ˢ univ
abbrev Energy (c : ℝ) := Lp ℝ exponent (energyMeasure μ c)

theorem energyBlock_measurable (c : ℝ) (n : ℕ) : MeasurableSet (energyBlock (Ω := Ω) c n) :=
  (block_measurable c n).prod MeasurableSet.univ

theorem energyBlock_mass (c : ℝ) (hc : 0 < c) (n : ℕ) :
    energyMeasure μ c (energyBlock c n) = (rate n : ℝ≥0∞) := by
  rw [energyMeasure, energyBlock, Measure.prod_prod, block_mass c hc n]
  simp

theorem energyBlock_memLp (c : ℝ) (hc : 0 < c) (n : ℕ) :
    MemLp ((energyBlock (Ω := Ω) c n).indicator (fun _ => (1 : ℝ))) exponent (energyMeasure μ c) :=
  indicator_memLp _ _ (energyBlock_measurable c n) _ (energyBlock_mass μ c hc n)

def deterministicInput (c : ℝ) (hc : 0 < c) (n : ℕ) : Energy μ c :=
  (energyBlock_memLp μ c hc n).toLp _

theorem deterministicInput_norm (c : ℝ) (hc : 0 < c) (n : ℕ) :
    ‖deterministicInput μ c hc n‖ = (n : ℝ)^3 := by
  rw [deterministicInput, Lp.norm_toLp,
    indicator_norm _ _ (energyBlock_measurable c n) _ (energyBlock_mass μ c hc n), input_norm_rate]

variable {μ}

def observed (c : ℝ) (hc : 0 < c) (N : FiniteCountLaws μ c) (n : ℕ) : Lp ℝ exponent μ :=
  lawOutput (N.count (block c (n+1))) (rate (n+1)) (rate_pos (by omega))
    (block_count_law c hc N (n+1))

theorem observed_norm_le (c : ℝ) (hc : 0 < c) (N : FiniteCountLaws μ c) (n : ℕ) :
    ‖observed c hc N n‖ ≤ ((n+1 : ℕ) : ℝ)^2 := by
  rw [observed, lawOutput_norm]
  exact output_norm_rate (by omega)

theorem observed_memLp_four (c : ℝ) (hc : 0 < c) (N : FiniteCountLaws μ c) (n : ℕ) :
    MemLp (fun ω => (N.count (block c (n+1)) ω : ℝ) - (rate (n+1) : ℝ)) 4 μ := by
  exact (block_count_law c hc N (n+1)).memLp_comp
    (PoissonLpTwoRegime.count_memLp_four _ (rate_pos (by omega)))

/-- The domain can be the range itself; neither closedness nor ambient extension is assumed. -/
theorem recovery_norm_ge (c : ℝ) (hc : 0 < c) (N : FiniteCountLaws μ c)
    (S : Submodule ℝ (Lp ℝ exponent μ)) (hS : ∀ n, observed c hc N n ∈ S)
    (R : S →L[ℝ] Energy μ c)
    (hR : ∀ n, R ⟨observed c hc N n, hS n⟩ = deterministicInput μ c hc (n+1))
    (n : ℕ) : ((n+1 : ℕ) : ℝ) ≤ ‖R‖ := by
  have h := R.le_opNorm (⟨observed c hc N n, hS n⟩ : S)
  rw [hR n, deterministicInput_norm] at h
  have hout : ‖(⟨observed c hc N n, hS n⟩ : S)‖ ≤ ((n+1 : ℕ) : ℝ)^2 :=
    observed_norm_le c hc N n
  have hbound := h.trans (mul_le_mul_of_nonneg_left hout (norm_nonneg R))
  have hp : 0 < ((n+1 : ℕ) : ℝ)^2 := by positivity
  have heq : ((n+1 : ℕ) : ℝ)^3 = ((n+1 : ℕ) : ℝ) * ((n+1 : ℕ) : ℝ)^2 := by ring
  rw [heq] at hbound
  exact (mul_le_mul_iff_left₀ hp).mp hbound

theorem no_bounded_range_recovery (c : ℝ) (hc : 0 < c) (N : FiniteCountLaws μ c)
    (S : Submodule ℝ (Lp ℝ exponent μ)) (hS : ∀ n, observed c hc N n ∈ S) :
    ¬ ∃ R : S →L[ℝ] Energy μ c,
      ∀ n, R ⟨observed c hc N n, hS n⟩ = deterministicInput μ c hc (n+1) := by
  rintro ⟨R, hR⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ‖R‖
  have h := recovery_norm_ge c hc N S hS R hR n
  push_cast at h
  linarith

end OperatorDerivativeRewrite.Foundation.StablePoissonRecoveryObstruction
