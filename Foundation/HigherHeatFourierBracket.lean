import Foundation.HigherHeatFourierCovariance
import Foundation.HigherHeatGenerator
import Mathlib.Analysis.Complex.RealDeriv

/-! Infinitesimal signed covariance and the failure of a Brownian quadratic product rule. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierBracket
open HigherHeatL2 HigherHeatGenerator HigherHeatFourierCovariance

def rate (m : ℕ) (ξ η : ℝ) : ℝ := weight m ξ+weight m η-weight m (ξ+η)

def realCovariance (m : ℕ) (t ξ η : ℝ) : ℝ :=
  Real.exp (-t*weight m (ξ+η))-Real.exp (-t*weight m ξ)*Real.exp (-t*weight m η)

theorem covariance_eq (m : ℕ) (t : ℝ≥0) (ξ η : ℝ) :
    covariance m t ξ η=(realCovariance m t ξ η:ℂ) := by
  simp [covariance,realCovariance,symbol,weight]

theorem real_covariance_hasDerivAt (m : ℕ) (ξ η : ℝ) :
    HasDerivAt (fun t : ℝ => realCovariance m t ξ η) (rate m ξ η) 0 := by
  have hd (ζ : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-t*weight m ζ)) (-weight m ζ) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).neg.mul_const (weight m ζ)).exp)
  change HasDerivAt ((fun t : ℝ => Real.exp (-t*weight m (ξ+η)))-
    ((fun t : ℝ => Real.exp (-t*weight m ξ))*(fun t : ℝ => Real.exp (-t*weight m η))))
    (rate m ξ η) 0
  convert (hd (ξ+η)).sub ((hd ξ).mul (hd η)) using 1 <;> simp [rate] <;> ring

theorem covariance_slope_tendsto (m : ℕ) (ξ η : ℝ) :
    Tendsto (fun t : ℝ => covariance m t.toNNReal ξ η/(t:ℂ))
      (𝓝[Set.Ioi 0] 0) (𝓝 (rate m ξ η:ℂ)) := by
  have hd := (real_covariance_hasDerivAt m ξ η).ofReal_comp
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi 0) (by simp)).mp
    hd.hasDerivWithinAt
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp [slope,covariance_eq,realCovariance,Real.coe_toNNReal t ht.le,Complex.real_smul,
    div_eq_mul_inv]
  ring

theorem heat_rate (ξ η : ℝ) : rate 1 ξ η= -2*(2*Real.pi)^2*ξ*η := by
  unfold rate weight
  norm_num
  ring

theorem fourth_order_rate (ξ η : ℝ) :
    rate 2 ξ η= -(2*Real.pi)^4*(4*ξ^3*η+6*ξ^2*η^2+4*ξ*η^3) := by
  unfold rate weight
  norm_num
  ring

theorem fourth_order_not_quadratic : ¬ ∃ c : ℝ, ∀ ξ η : ℝ, rate 2 ξ η=c*ξ*η := by
  rintro ⟨c,h⟩
  have h1 := h 1 1
  have h2 := h 2 2
  rw [fourth_order_rate] at h1 h2
  norm_num at h1 h2
  have hp : 0 < (2*Real.pi)^4 := pow_pos (mul_pos (by norm_num) Real.pi_pos) _
  nlinarith

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierBracket
