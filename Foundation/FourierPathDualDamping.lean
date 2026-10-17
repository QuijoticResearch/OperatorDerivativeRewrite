import Foundation.FourierPathDualGrid
import Foundation.FourierPathHeatTransfer

/-! Actual conjugate-exponent control directions admit uniform heat damping and closed gradients. -/
noncomputable section
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualDamping
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierPathDerivative FourierPathDirectionalCharacters
open HigherHeatFourierPathSemigroup FourierPathDualControls FourierPathDualGrid

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def tail (i : ℕ) : Fin (gridSize (spectrumLevels levels i)) → ℝ := fun j =>
  2*Real.pi*(∑ k ∈ Finset.univ.filter (fun k => j ≤ k), spectrumFrequency levels ξ i k)

theorem tail_clock (m : ℕ) [Fact (0 < m)] (i : ℕ) :
    (HigherHeatLpControls.clock m (step m (gridSize (spectrumLevels levels i)) (tail levels ξ i)) : ℝ) =
      rate levels ξ m i := by
  rw [step_clock m _ (gridSize_pos _)]
  rfl

def frequencyMap (m : ℕ) [Fact (0 < m)] (i : ℕ) : Control m →L[ℝ] ℝ :=
  -((pairing m).flip (step m (gridSize (spectrumLevels levels i)) (tail levels ξ i)))

theorem frequencyMap_apply (m : ℕ) [Fact (0 < m)] (i : ℕ) (u : Control m) :
    frequencyMap levels ξ m i u = frequency levels ξ (direction m u) i := by
  change -pairing m u (step m (gridSize (spectrumLevels levels i)) (tail levels ξ i)) = _
  rw [direction_pairing m u _ (gridSize_pos _), FourierPathLipschitzDamping.frequency_increment]
  rfl

theorem frequency_bound (m : ℕ) [Fact (0 < m)] (u : Control m) (i : ℕ) :
    |frequency levels ξ (direction m u) i| ≤ ‖u‖ * (1 + rate levels ξ m i) := by
  rw [← frequencyMap_apply, frequencyMap]
  change |-pairing m u (step m (gridSize (spectrumLevels levels i)) (tail levels ξ i))| ≤ _
  rw [abs_neg]
  calc
    _ ≤ ‖u‖ * ‖step m (gridSize (spectrumLevels levels i)) (tail levels ξ i)‖ := pairing_bound m u _
    _ ≤ ‖u‖ * (1 + (HigherHeatLpControls.clock m
        (step m (gridSize (spectrumLevels levels i)) (tail levels ξ i)) : ℝ)) :=
      mul_le_mul_of_nonneg_left (norm_le_clock m _) (norm_nonneg u)
    _ = _ := by rw [tail_clock]

theorem damped_frequency_bound (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖eigenvalue (frequency levels ξ (direction m u) i) * multiplier levels ξ m T i‖ ≤
      ‖u‖ * (1 + (T : ℝ)⁻¹) := by
  rw [norm_mul, eigenvalue_norm, multiplier_exp, Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (‖u‖ * (1 + rate levels ξ m i)) * Real.exp (-(T : ℝ)*rate levels ξ m i) :=
      mul_le_mul_of_nonneg_right (frequency_bound levels ξ m u i) (Real.exp_pos _).le
    _ = ‖u‖ * ((1 + rate levels ξ m i) * Real.exp (-(T : ℝ)*rate levels ξ m i)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (FourierPathLinearDirection.damped_rate_bound _ _ (by exact_mod_cast hT)
        (rate_nonneg levels ξ m i)) (norm_nonneg u)

def bound (m : ℕ) [Fact (0 < m)] (u : Control m) (T : ℝ≥0) : ℝ :=
  (1+‖u‖)*(1+(T : ℝ)⁻¹)

theorem bound_pos (m : ℕ) [Fact (0 < m)] (u : Control m) (T : ℝ≥0) :
    0 < bound m u T := by unfold bound; positivity

theorem damped_bound (m : ℕ) [Fact (0 < m)] (u : Control m)
    (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖eigenvalue (frequency levels ξ (direction m u) i) * multiplier levels ξ m T i‖ ≤
      bound m u T := by
  exact (damped_frequency_bound levels ξ m u T hT i).trans (by unfold bound; gcongr; linarith)

def gradient (m : ℕ) [h : Fact (0 < m)] (u : Control m) (T : ℝ≥0) (hT : 0 < T) :
    TestSpace levels ξ →L[ℂ] TestSpace levels ξ :=
  FourierPathHeatGradient.gradient levels ξ (direction m u) m h.out T (bound m u T)
    (bound_pos m u T) (damped_bound levels ξ m u T hT)

theorem gradient_graph (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    (evolution levels ξ m h.out T q, gradient levels ξ m u T hT q) ∈
      FourierPathDirectionalOperator.graph levels ξ (direction m u) :=
  FourierPathHeatGradient.gradient_graph levels ξ (direction m u) m h.out T _ _ _ q

theorem gradient_bound (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    ‖gradient levels ξ m u T hT q‖ ≤ bound m u T * ‖q‖ :=
  FourierPathHeatGradient.gradient_bound levels ξ (direction m u) m h.out T _ _ _ q

def transfer (m : ℕ) [h : Fact (0 < m)] (u : Control m) (T : ℝ≥0) (hT : 0 < T) :
    TestSpace levels ξ →L[ℂ] ℂ :=
  FourierPathHeatTransfer.transfer levels ξ (direction m u) m h.out T (bound m u T)
    (bound_pos m u T) (damped_bound levels ξ m u T hT)

theorem transfer_identity (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (T : ℝ≥0) (hT : 0 < T) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ FourierPathDirectionalOperator.graph levels ξ (direction m u)) :
    expectation levels ξ m h.out T hT z.2 = transfer levels ξ m u T hT z.1 :=
  FourierPathHeatTransfer.transfer_identity levels ξ (direction m u) m h.out T hT _ _ _ z hz

theorem smoothing_domain (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    evolution levels ξ m h.out T q ∈
      (FourierPathDirectionalOperator.operator levels ξ (direction m u)).domain := by
  apply LinearPMap.mem_domain_iff.mpr
  refine ⟨gradient levels ξ m u T hT q, ?_⟩
  rw [FourierPathDirectionalOperator.operator_graph]
  exact gradient_graph levels ξ m u T hT q

theorem transfer_bound (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    ‖transfer levels ξ m u T hT q‖ ≤ bound m u T * ‖q‖ :=
  FourierPathHeatTransfer.transfer_bound levels ξ (direction m u) m h.out T _ _ _ q

end OperatorDerivativeRewrite.Foundation.FourierPathDualDamping
