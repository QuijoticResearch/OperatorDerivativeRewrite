import Foundation.MixedAtomicGradient
import Foundation.WeightedFormClosability
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Smooth derivative data under a full-support law need not admit a closable extension. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ContDiff Topology
namespace OperatorDerivativeRewrite.Foundation.MixedAtomicNonclosability
open MixedAtomicGradient ShrinkingSmoothJet
set_option backward.isDefEq.respectTransparency false

theorem no_closable_extension : ¬ ∃ (T : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ)
    (hd : ∀ f : Core, input f ∈ T.domain), T.IsClosable ∧
      ∀ f : Core, T ⟨input f,hd f⟩ = output f := by
  rintro ⟨T,hd,hT,hAgree⟩
  let seq : ℕ → T.domain := fun n => ⟨input (jetCore n),hd (jetCore n)⟩
  have hi : Tendsto (fun n => (seq n : Lp ℝ 2 μ)) atTop (nhds 0) := input_jets_tendsto_zero
  have ho : Tendsto (fun n => T (seq n)) atTop (nhds atomClass) := by
    simpa only [seq, hAgree] using output_jets_tendsto_atom
  have hz := WeightedFormClosability.operator_seqClosable hT seq hi atomClass ho
  exact atomClass_nonzero hz

theorem atomClass_norm_sq : ‖atomClass‖^2 = (1/2 : ℝ) := by
  rw [BochnerL2Dominated.norm_sq_integral]
  calc
    _ = ∫ x, (atom x)^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (atom_memLp 2)] with x hx
      change ‖(atom_memLp 2).toLp atom x‖^2 = _
      rw [hx]
      simp [Real.norm_eq_abs]
    _ = ∫ x, ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) x ∂μ := by
      congr 1
      funext x
      by_cases hx : x = 0 <;> simp [atom,Set.indicator,hx]
    _ = μ.real {0} := by
      rw [integral_indicator_const _ (measurableSet_singleton 0)]
      simp
    _ = 1/2 := by rw [measureReal_def, μ_atom]; norm_num

def coreSub (f g : Core) : Core :=
  ⟨f.val-g.val, f.property.1.sub g.property.1, f.property.2.sub g.property.2⟩

theorem output_coe (f : Core) : output f =ᵐ[μ] deriv f.val :=
  MemLp.coeFn_toLp (derivative_memLp f 2)

theorem output_sub (f g : Core) : output (coreSub f g) = output f - output g := by
  apply Lp.ext
  filter_upwards [output_coe (coreSub f g), output_coe f, output_coe g,
    Lp.coeFn_sub (output f) (output g)] with x hs hf hg hd
  rw [hs, hd, Pi.sub_apply, hf, hg]
  change deriv (f.val-g.val) x = deriv f.val x - deriv g.val x
  exact deriv_sub (f.property.1.differentiable (by norm_num) x)
    (g.property.1.differentiable (by norm_num) x)

def Energy (κ : ℝ) (f : Core) : ℝ := κ * ‖output f‖^2

theorem energy_integral (κ : ℝ) (f : Core) :
    Energy κ f = ∫ x, κ * (deriv f.val x)^2 ∂μ := by
  rw [Energy, BochnerL2Dominated.norm_sq_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [output_coe f] with x hx
  rw [hx]
  simp [Real.norm_eq_abs]

theorem energy_sub (κ : ℝ) (f g : Core) :
    Energy κ (coreSub f g) = κ * ‖output f-output g‖^2 := by
  rw [Energy, output_sub]

theorem energy_jets_limit (κ : ℝ) :
    Tendsto (fun n => Energy κ (jetCore n)) atTop (nhds (κ/2)) := by
  have h : Tendsto (fun n => κ * ‖output (jetCore n)‖^2) atTop
      (nhds (κ * ‖atomClass‖^2)) :=
    tendsto_const_nhds.mul (output_jets_tendsto_atom.norm.pow 2)
  simpa only [Energy, atomClass_norm_sq, div_eq_mul_inv, one_mul] using h

def FormClosable (κ : ℝ) : Prop :=
  ∀ f : ℕ → Core, Tendsto (fun n => input (f n)) atTop (nhds 0) →
    Tendsto (fun q : ℕ × ℕ => Energy κ (coreSub (f q.1) (f q.2))) atTop (nhds 0) →
    Tendsto (fun n => Energy κ (f n)) atTop (nhds 0)

theorem zero_coefficient_closable : FormClosable 0 := by
  intro f _ _
  simpa only [Energy, zero_mul] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

theorem derivative_energy_cauchy (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun q : ℕ × ℕ => Energy κ (coreSub (jetCore q.1) (jetCore q.2)))
      atTop (nhds 0) := by
  have h := (WeightedFormClosability.energy_cauchy_iff κ hκ
    (LinearMap.id : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ) (fun n => output (jetCore n))).mpr
      output_jets_tendsto_atom.cauchySeq
  simpa only [energy_sub, WeightedFormClosability.energy, LinearMap.id_apply] using h

theorem positive_coefficient_not_closable (κ : ℝ) (hκ : 0 < κ) : ¬ FormClosable κ := by
  intro h
  have he := h jetCore input_jets_tendsto_zero (derivative_energy_cauchy κ hκ)
  have hz : κ/2 = 0 := tendsto_nhds_unique (energy_jets_limit κ) he
  linarith

end OperatorDerivativeRewrite.Foundation.MixedAtomicNonclosability
