import Foundation.SmoothAtomicJet
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-! A finite atomic reference law does not make the ordinary smooth gradient closable. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ContDiff
namespace OperatorDerivativeRewrite.Foundation.AtomicGradientObstruction
open SmoothAtomicJet
set_option backward.isDefEq.respectTransparency false

def μ : Measure ℝ := Measure.dirac 0

instance μ_probability : IsProbabilityMeasure μ := by unfold μ; infer_instance
instance μ_regular : μ.Regular := by infer_instance

theorem all_memLp (f : ℝ → ℝ) (p : ℝ≥0∞) : MemLp f p μ := by
  have he : f =ᵐ[μ] (fun _ => f 0) := ae_eq_dirac f
  exact (memLp_congr_ae he).mpr (memLp_const _)

def toL2 (f : ℝ → ℝ) : Lp ℝ 2 μ := (all_memLp f 2).toLp f

theorem toL2_eq_iff (f g : ℝ → ℝ) : toL2 f = toL2 g ↔ f 0 = g 0 := by
  unfold toL2
  rw [MemLp.toLp_eq_toLp_iff]
  change (∀ᵐ x ∂μ, f x = g x) ↔ f 0 = g 0
  rw [μ, ae_dirac_eq]
  simp

theorem toL2_zero : toL2 (0 : ℝ → ℝ) = 0 := MemLp.toLp_zero _

theorem toL2_witness : toL2 witness = 0 := by
  rw [← toL2_zero]
  exact (toL2_eq_iff _ _).mpr witness_zero

theorem no_derivative_map : ¬ ∃ D : Lp ℝ 2 μ → Lp ℝ 2 μ,
    ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → D (toL2 f) = toL2 (deriv f) := by
  rintro ⟨D,hD⟩
  have hw := hD witness witness_smooth witness_compact
  have h0 := hD 0 contDiff_const (by simp [HasCompactSupport])
  have hc : toL2 witness = toL2 0 := (toL2_eq_iff _ _).mpr witness_zero
  have he := congrArg D hc
  rw [hw,h0] at he
  have hd := (toL2_eq_iff _ _).mp he
  rw [witness_deriv] at hd
  norm_num at hd

def Energy (κ : ℝ) (f : ℝ → ℝ) : ℝ := ∫ x, κ * (deriv f x)^2 ∂μ

theorem energy_formula (κ : ℝ) (f : ℝ → ℝ) : Energy κ f = κ * (deriv f 0)^2 := by
  rw [Energy, μ, integral_dirac]

theorem energy_witness (κ : ℝ) : Energy κ witness = κ := by
  rw [energy_formula, witness_deriv]
  ring

theorem energy_zero (κ : ℝ) : Energy κ (0 : ℝ → ℝ) = 0 := by
  simp [energy_formula]

def FormClosable (κ : ℝ) : Prop :=
  ∀ f : ℕ → (ℝ → ℝ), (∀ n, ContDiff ℝ ∞ (f n) ∧ HasCompactSupport (f n)) →
    Tendsto (fun n => toL2 (f n)) atTop (nhds 0) →
    Tendsto (fun q : ℕ × ℕ => Energy κ (f q.1 - f q.2)) atTop (nhds 0) →
    Tendsto (fun n => Energy κ (f n)) atTop (nhds 0)

theorem zero_coefficient_closable : FormClosable 0 := by
  intro f _ _ _
  simpa only [energy_formula, zero_mul] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

theorem nonzero_coefficient_not_closable (κ : ℝ) (hκ : κ ≠ 0) : ¬ FormClosable κ := by
  intro h
  have hL : Tendsto (fun _ : ℕ => toL2 witness) atTop (nhds 0) := by
    simpa only [toL2_witness] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Lp ℝ 2 μ)) atTop (nhds 0))
  have hC : Tendsto (fun _ : ℕ × ℕ => Energy κ (witness - witness)) atTop (nhds 0) := by
    simpa only [sub_self, energy_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ × ℕ => (0 : ℝ)) atTop (nhds 0))
  have he := h (fun _ => witness) (fun _ => ⟨witness_smooth,witness_compact⟩) hL hC
  simp only [energy_witness] at he
  exact hκ (tendsto_nhds_unique tendsto_const_nhds he)

end OperatorDerivativeRewrite.Foundation.AtomicGradientObstruction
