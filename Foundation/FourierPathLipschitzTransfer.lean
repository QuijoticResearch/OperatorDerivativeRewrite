import Foundation.FourierPathLipschitzDamping
import Foundation.FourierPathHeatTransfer

/-! Genuine heat smoothing and bounded transfer for every direction Lipschitz on [0,1]. -/
noncomputable section
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathLipschitzTransfer
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathDirectionalOperator HigherHeatFourierPathSemigroup FourierPathLipschitzDamping

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def gradient (h : Path) (K : ℝ≥0) (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    TestSpace levels ξ →L[ℂ] TestSpace levels ξ :=
  FourierPathHeatGradient.gradient levels ξ h m hm T (bound K T) (bound_pos K T)
    (damped_frequency_bound levels ξ h K hK m hm T hT)

theorem gradient_graph (h : Path) (K : ℝ≥0) (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    (evolution levels ξ m hm T q,gradient levels ξ h K hK m hm T hT q) ∈ graph levels ξ h :=
  FourierPathHeatGradient.gradient_graph levels ξ h m hm T _ _ _ q

theorem gradient_bound (h : Path) (K : ℝ≥0) (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    ‖gradient levels ξ h K hK m hm T hT q‖ ≤ bound K T*‖q‖ :=
  FourierPathHeatGradient.gradient_bound levels ξ h m hm T _ _ _ q

theorem smoothing_domain (h : Path) (K : ℝ≥0) (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    evolution levels ξ m hm T q ∈ (operator levels ξ h).domain := by
  apply LinearPMap.mem_domain_iff.mpr
  refine ⟨gradient levels ξ h K hK m hm T hT q, ?_⟩
  rw [operator_graph]
  exact gradient_graph levels ξ h K hK m hm T hT q

def transfer (h : Path) (K : ℝ≥0) (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : TestSpace levels ξ →L[ℂ] ℂ :=
  FourierPathHeatTransfer.transfer levels ξ h m hm T (bound K T) (bound_pos K T)
    (damped_frequency_bound levels ξ h K hK m hm T hT)

theorem transfer_identity (h : Path) (K : ℝ≥0) (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (z : TestSpace levels ξ × TestSpace levels ξ) (hz : z ∈ graph levels ξ h) :
    expectation levels ξ m hm T hT z.2=transfer levels ξ h K hK m hm T hT z.1 :=
  FourierPathHeatTransfer.transfer_identity levels ξ h m hm T hT _ _ _ z hz

theorem transfer_bound (h : Path) (K : ℝ≥0) (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    ‖transfer levels ξ h K hK m hm T hT q‖ ≤ bound K T*‖q‖ :=
  FourierPathHeatTransfer.transfer_bound levels ξ h m hm T _ _ _ q

end OperatorDerivativeRewrite.Foundation.FourierPathLipschitzTransfer
