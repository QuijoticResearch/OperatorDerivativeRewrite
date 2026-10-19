import Foundation.RiemannQuarticFullCell

/-! Actual uniform derivative and Taylor-integral error bounds for all three
four-term real Fourier integrands on quadrature cell50. -/
noncomputable section
open Set MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFullCellChecks
open RiemannQuarticIntervalChecks RiemannQuarticTaylorJets RiemannQuarticRealCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Check all rounded order16 recurrences for the full four-term kernel.
theorem sixteenth_check :
    inside (RiemannQuarticFullCell.I 0 16) (-(10^22)) (10^22)=true ∧
      inside (RiemannQuarticFullCell.I 1 16) (-(10^22)) (10^22)=true ∧
      inside (RiemannQuarticFullCell.I 2 16) (-(10^22)) (10^22)=true := by
  decide +kernel

theorem uniform_sixteenth (u : ℝ) (hu : u ∈ Icc (1/2 : ℝ) (51/100))
    (k : ℕ) (hk : k ≤ 2) :
    |coefficient (realIntegrand 4 k (632083/10000)) 16 u| ≤ (10^22 : ℝ) := by
  have hc : inside (RiemannQuarticFullCell.I k 16) (-(10^22)) (10^22)=true := by
    interval_cases k
    · exact sixteenth_check.1
    · exact sixteenth_check.2.1
    · exact sixteenth_check.2.2
  have h := inside_spec hc (RiemannQuarticFullCell.uniform_I u hu k 16 hk)
  apply abs_le.mpr
  norm_num at h ⊢
  exact h

theorem cell_taylor_error (k : ℕ) (hk : k ≤ 2) :
    |(∫ u in (1/2 : ℝ)..(51/100), realIntegrand 4 k (632083/10000) u)-
      (∫ u in (1/2 : ℝ)..(51/100),
        localPolynomial (realIntegrand 4 k (632083/10000)) 15 (101/200) u)| ≤
      (1/10^16 : ℝ) := by
  have hf := realIntegrand_contDiff 4 k (632083/10000)
  have he := local_integral_error (realIntegrand 4 k (632083/10000)) hf 15
    (101/200) (1/200) (10^22) (by norm_num) (by positivity) (by
      intro u hu
      apply uniform_sixteenth u _ k hk
      norm_num at hu ⊢
      exact hu)
  norm_num at he
  exact he.trans (by norm_num)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFullCellChecks
