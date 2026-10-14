import Foundation.GaussianInverseNumberPotential
import Foundation.FractionalDualRegimePrediction

/-! Inverse-number damping preserves positive terminal Hermite ranks and prediction obstructions. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianPotentialPredictionRank
open InfiniteGaussian GaussianNumberSectors GaussianInverseNumberPotential
open GaussianTimeSpaceHermite GaussianTerminalPredictionSpectrum GaussianSingleObservationPrediction
open GaussianConditionalGraph FractionalTerminalPredictionRank FractionalDualRegimePrediction

theorem potential_inner (f g : GaussianL2) :
    inner ℝ (potentialOperator f) g=inner ℝ f (potentialOperator g) := by
  change inner ℝ (GaussianDivergenceRecovery.recoveryOperator.adjoint
    (GaussianDivergenceRecovery.recoveryOperator f)) g=_
  rw [ContinuousLinearMap.adjoint_inner_left]
  change _=inner ℝ f (GaussianDivergenceRecovery.recoveryOperator.adjoint
    (GaussianDivergenceRecovery.recoveryOperator g))
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem potential_sector (n : ℕ) (f : sector n) :
    potentialOperator f=(n : ℝ)⁻¹ • (f : GaussianL2) := by
  apply (potential_hasSum f).unique
  have hs : HasSum (fun m : ℕ => (m : ℝ)⁻¹ • projection m f)
      ((n : ℝ)⁻¹ • projection n f) := by
    apply hasSum_single n
    intro m hmn
    rw [projection_of_sector f,if_neg hmn,smul_zero]
  simpa only [projection_fix] using hs

theorem potential_wick (u : CoefficientSpace) (n : ℕ) :
    potentialOperator (wick u n : GaussianL2)=(n : ℝ)⁻¹ • (wick u n : GaussianL2) :=
  potential_sector n ⟨_,IBMCubicFirstChaos.wick_mem_sector u n⟩

theorem potential_coefficient (u : CoefficientSpace) (f : GaussianL2) (n : ℕ) :
    coefficient u (potentialOperator f) n=(n : ℝ)⁻¹*coefficient u f n := by
  rw [coefficient,← potential_inner,potential_wick,real_inner_smul_left,coefficient]
  ring

theorem potential_centered (u : CoefficientSpace) (f : GaussianL2) :
    coefficient u (potentialOperator f) 0=0 := by rw [potential_coefficient]; simp

theorem positive_coefficient_iff (u : CoefficientSpace) (f : GaussianL2) (n : ℕ) (hn : 0<n) :
    coefficient u (potentialOperator f) n≠0 ↔ coefficient u f n≠0 := by
  rw [potential_coefficient]
  constructor
  · intro h hc
    exact h (by rw [hc,mul_zero])
  · intro hc
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast ne_of_gt hn)) hc

theorem potential_prediction_energy {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) (hf : f∈singleGenerated u) :
    HasSum (fun n : ℕ => ((n : ℝ)⁻¹*coefficient u f n)^2*(n.factorial : ℝ)*
      (‖GaussianWickConditionalProjection.sourceProjection h u‖^2)^n)
      (‖conditionalProjection h (potentialOperator f)‖^2) := by
  have hp := potential_preserves_generated (fun _ : Unit => u) hf
  simpa only [potential_coefficient] using terminal_prediction_energy_hasSum h u hu (potentialOperator f) hp

theorem fractional_potential_lower (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (f : GaussianL2) (hf : f∈singleGenerated (terminalDirection H hH0 hH1))
    (t : ℝ≥0) (ht0 : 0<t) (ht1 : t≤1) (m : ℕ) :
    (((m : ℝ)⁻¹*coefficient (terminalDirection H hH0 hH1) f m)^2*
      (m.factorial : ℝ)/(4 : ℝ)^m)*(t : ℝ)^(predictionPower H*(m : ℝ)) ≤
      ‖forecast H hH0 hH1 (potentialOperator f) t‖^2 := by
  have hp := potential_preserves_generated (fun _ : Unit => terminalDirection H hH0 hH1) hf
  simpa only [potential_coefficient] using
    terminal_forecast_dual_lower H hH0 hH1 (potentialOperator f) hp t ht0 ht1 m

theorem fractional_potential_no_higher_bound (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (f : GaussianL2) (hf : f∈singleGenerated (terminalDirection H hH0 hH1))
    (m : ℕ) (hm : 0<m) (hcm : coefficient (terminalDirection H hH0 hH1) f m≠0)
    (α : ℝ) (hα : predictionPower H*(m : ℝ)<α) (C δ : ℝ) (hδ : 0<δ) :
    ∃ t : ℝ≥0, 0<t ∧ (t : ℝ)<δ ∧ t≤1 ∧
      C*(t : ℝ)^α < ‖forecast H hH0 hH1 (potentialOperator f) t-
        forecast H hH0 hH1 (potentialOperator f) 0‖^2 := by
  have hp := potential_preserves_generated (fun _ : Unit => terminalDirection H hH0 hH1) hf
  exact no_higher_dual_prediction_increment_bound H hH0 hH1 (potentialOperator f) hp
    (potential_centered _ f) m ((positive_coefficient_iff _ f m hm).mpr hcm) α hα C δ hδ

end OperatorDerivativeRewrite.Foundation.GaussianPotentialPredictionRank
