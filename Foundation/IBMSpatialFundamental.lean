import Foundation.IBMSmoothIncrementMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Fundamental theorem of calculus for the actual Gaussian L² fields.
The integral is a Bochner integral in GaussianL2, not a samplewise integral. -/
noncomputable section
open MeasureTheory

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousScenery

theorem wholeLineScenery_continuous {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) :
    Continuous (wholeLineScenery ρ) :=
  continuous_iff_continuousAt.mpr fun x => (wholeLineScenery_hasDerivAt hc hρ x).continuousAt

/-- The spatial derivative integrates to the actual difference of convolution
classes, for either ordering of the real endpoints. -/
theorem wholeLineScenery_integral_deriv {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (a b : ℝ) :
    (∫ r in a..b, wholeLineScenery (deriv ρ) r) =
      wholeLineScenery ρ b - wholeLineScenery ρ a := by
  have hd : ContDiff ℝ 1 (deriv ρ) := (contDiff_succ_iff_deriv.mp hρ).2.2
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => wholeLineScenery_hasDerivAt hc (hρ.of_le (by norm_num)) r)
    ((wholeLineScenery_continuous hc.deriv hd).intervalIntegrable a b)

/-- Both derivative identities for the concrete normalized bump are genuine
Gaussian-L² Bochner identities, with no supplied sample paths. -/
theorem concreteMollifier_integral_derivatives (n : ℕ) (a b : ℝ) :
    ((∫ r in a..b, wholeLineScenery (deriv (IBMMollifier.kernel n)) r) =
      wholeLineScenery (IBMMollifier.kernel n) b -
        wholeLineScenery (IBMMollifier.kernel n) a) ∧
    ((∫ r in a..b, wholeLineScenery (deriv (deriv (IBMMollifier.kernel n))) r) =
      wholeLineScenery (deriv (IBMMollifier.kernel n)) b -
        wholeLineScenery (deriv (IBMMollifier.kernel n)) a) := by
  have h := IBMMollifier.kernel_smooth n
  have hd := (contDiff_infty_iff_deriv.mp h).2
  exact ⟨wholeLineScenery_integral_deriv (IBMMollifier.kernel_compactSupport n)
    (h.of_le (by norm_num)) a b,
    wholeLineScenery_integral_deriv (IBMMollifier.kernel_compactSupport n).deriv
      (hd.of_le (by norm_num)) a b⟩

end OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
