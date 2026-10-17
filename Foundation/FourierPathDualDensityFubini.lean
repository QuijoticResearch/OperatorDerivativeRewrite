import Foundation.FourierPathDualJointDensity
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual weighted product integrals and Fubini for the jointly measurable time/path density. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualDensityFubini
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathDualControls FourierPathDualJointDensity

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def weighted (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ)
    (u : Control m) (w : Path → ℝ) (z : ℝ × Path) : ℂ :=
  w z.2 • (u z.1 • joint levels ξ m T hT q z)

theorem weighted_integrable (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control m) (μ : Measure Path) [SFinite μ]
    (w : Path → ℝ) (hw : Integrable w μ) :
    Integrable (weighted levels ξ m T hT q u w) (volume.prod μ) := by
  have hr : MemLp (representative levels ξ m T hT q) (HigherHeatLpControls.power m) volume :=
    MemLp.ae_eq (representative_ae levels ξ m T hT q)
      (Lp.memLp (FourierPathDualTimeGradient.timeGradient levels ξ m T hT q))
  have hi : Integrable (fun t : ℝ => ‖u t‖ * ‖representative levels ξ m T hT q t‖) :=
    (Lp.memLp u).norm.integrable_mul hr.norm
  have hm : AEStronglyMeasurable (weighted levels ξ m T hT q u w) (volume.prod μ) :=
    hw.aestronglyMeasurable.comp_snd.smul
      ((Lp.aestronglyMeasurable u).comp_fst.smul
        (joint_measurable levels ξ m T hT q).aestronglyMeasurable)
  apply (hi.mul_prod hw.norm).mono' hm
  exact Eventually.of_forall (fun z => by
    change ‖w z.2 • (u z.1 • joint levels ξ m T hT q z)‖ ≤ _
    rw [norm_smul, norm_smul]
    calc
      _ ≤ ‖w z.2‖ * (‖u z.1‖ * ‖representative levels ξ m T hT q z.1‖) := by
        gcongr
        exact joint_bound levels ξ m T hT q z
      _ = _ := by ring)

theorem weighted_fubini (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control m) (μ : Measure Path) [SFinite μ]
    (w : Path → ℝ) (hw : Integrable w μ) :
    (∫ t : ℝ, ∫ ω, weighted levels ξ m T hT q u w (t,ω) ∂μ) =
      ∫ ω, w ω • realize levels ξ (FourierPathDualGradient.gradient levels ξ m T hT q u) ω ∂μ := by
  rw [integral_integral_swap (μ := (volume : Measure ℝ)) (ν := μ)
    (f := fun (t : ℝ) (ω : Path) => weighted levels ξ m T hT q u w (t,ω))
    (weighted_integrable levels ξ m T hT q u μ w hw)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω => by
    change (∫ t : ℝ, w ω • (u t • joint levels ξ m T hT q (t,ω))) = _
    rw [integral_smul, joint_contraction])

end OperatorDerivativeRewrite.Foundation.FourierPathDualDensityFubini
