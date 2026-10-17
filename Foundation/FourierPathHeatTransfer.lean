import Foundation.FourierPathHeatGradient
import Foundation.FourierPathLinearDirection

/-! Genuine bounded expectation-transfer identities, instantiated for the linear path direction. -/
noncomputable section
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathHeatTransfer
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierTranslations HigherHeatFourierPathSemigroup
open FourierPathDirectionalOperator FourierPathHeatGradient

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def transfer (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C) :
    TestSpace levels ξ →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ zeroPath).comp
    ((realize levels ξ).comp (gradient levels ξ h m hm T C hC hb))

theorem transfer_identity (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (C : ℝ) (hC : 0 < C) (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C)
    (z : TestSpace levels ξ × TestSpace levels ξ) (hz : z ∈ graph levels ξ h) :
    expectation levels ξ m hm T hT z.2=transfer levels ξ h m hm T C hC hb z.1 := by
  have hs := FourierPathDifferentialCommutation.heat_graph levels ξ h m hm T z hz
  have hg := gradient_graph levels ξ h m hm T C hC hb z.1
  have hs' : (evolution levels ξ m hm T z.1,evolution levels ξ m hm T z.2) ∈
      (operator levels ξ h).graph := by rw [operator_graph]; exact hs
  have hg' : (evolution levels ξ m hm T z.1,gradient levels ξ h m hm T C hC hb z.1) ∈
      (operator levels ξ h).graph := by rw [operator_graph]; exact hg
  have hv := (operator levels ξ h).mem_graph_snd_inj hs' hg' rfl
  rw [← expectation_at_zero levels ξ m hm T hT z.2, hv]
  rfl

theorem transfer_bound (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C) (q : TestSpace levels ξ) :
    ‖transfer levels ξ h m hm T C hC hb q‖ ≤ C*‖q‖ := by
  change ‖realize levels ξ (gradient levels ξ h m hm T C hC hb q) zeroPath‖ ≤ _
  exact ((realize levels ξ _).norm_coe_le_norm zeroPath).trans
    ((realize_bound levels ξ _).trans (gradient_bound levels ξ h m hm T C hC hb q))

def linearGradient (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    TestSpace levels ξ →L[ℂ] TestSpace levels ξ :=
  gradient levels ξ FourierPathLinearDirection.direction m hm T (1+(T:ℝ)⁻¹)
    (by positivity) (FourierPathLinearDirection.damped_frequency_bound levels ξ m hm T hT)

theorem linearGradient_graph (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) :
    (evolution levels ξ m hm T q,linearGradient levels ξ m hm T hT q) ∈
      graph levels ξ FourierPathLinearDirection.direction :=
  gradient_graph levels ξ _ m hm T _ _ _ q

theorem linearGradient_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) : ‖linearGradient levels ξ m hm T hT q‖ ≤ (1+(T:ℝ)⁻¹)*‖q‖ :=
  gradient_bound levels ξ _ m hm T _ _ _ q

theorem linear_smoothing_domain (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) : evolution levels ξ m hm T q ∈
      (operator levels ξ FourierPathLinearDirection.direction).domain := by
  apply LinearPMap.mem_domain_iff.mpr
  refine ⟨linearGradient levels ξ m hm T hT q, ?_⟩
  rw [operator_graph]
  exact linearGradient_graph levels ξ m hm T hT q

def linearTransfer (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : TestSpace levels ξ →L[ℂ] ℂ :=
  transfer levels ξ FourierPathLinearDirection.direction m hm T (1+(T:ℝ)⁻¹)
    (by positivity) (FourierPathLinearDirection.damped_frequency_bound levels ξ m hm T hT)

theorem linearTransfer_identity (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ FourierPathLinearDirection.direction) :
    expectation levels ξ m hm T hT z.2=linearTransfer levels ξ m hm T hT z.1 :=
  transfer_identity levels ξ _ m hm T hT _ _ _ z hz

theorem linearTransfer_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) : ‖linearTransfer levels ξ m hm T hT q‖ ≤ (1+(T:ℝ)⁻¹)*‖q‖ :=
  transfer_bound levels ξ _ m hm T _ _ _ q

end OperatorDerivativeRewrite.Foundation.FourierPathHeatTransfer
