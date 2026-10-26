import Foundation.GaussianClockSpectralPowers
import Foundation.IBMClockSubcritical

/-! The actual reflected-clock IBM endpoint belongs to the canonical closed
clock Bessel domain with multiplier (1+n)^(s/2) exactly when s<1/2.
This is ambient source-clock regularity, not a physical adapted derivative. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockFractionalDomain
open InfiniteGaussian GaussianClockValueOperators GaussianClockSpectralPowers

def bessel (s : ℝ) : Field →ₗ.[ℝ] Field := operator (fun n => ((n:ℝ)+1)^(s/2))

theorem bessel_weight_sq (s : ℝ) (n : ℕ) :
    (((n:ℝ)+1)^(s/2))^2 = ((n:ℝ)+1)^s := by
  rw [← Real.rpow_two,← Real.rpow_mul (by positivity : (0:ℝ) ≤ (n:ℝ)+1)]
  congr 1; ring

theorem bessel_domain (s : ℝ) (f : Field) :
    f ∈ (bessel s).domain ↔ Summable (fun (n : ℕ) => ((n:ℝ)+1)^s*‖project n f‖^2) := by
  unfold bessel
  rw [operator_domain]
  simp only [bessel_weight_sq]

theorem actual_bessel_domain (s : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    IBMRandomTimeHilbert.randomSourceL2 T ∈ (bessel s).domain ↔ s < 1/2 := by
  rw [bessel_domain]
  exact IBMClockSubcritical.actual_bessel_summable_iff T hT s

end OperatorDerivativeRewrite.Foundation.IBMClockFractionalDomain
