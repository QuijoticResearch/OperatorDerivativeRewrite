import Foundation.PhysicalHeatChain

/-!
# Exact grid marginals of the physical heat chain

The actual Ionescu--Tulcea path law at step `δ` has one-point marginal at
coordinate `n` equal to the physical heat kernel at time `nδ`. The proof
extracts a marginal recurrence from the genuine joint law and uses
Chapman--Kolmogorov. Fourier expectations then agree with the verified
operator multiplier at every grid point. This does not construct a
continuous-time path law.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open PhysicalHeatKernel PhysicalHeatChain
open MeasureTheory AddCircle ProbabilityTheory Function Preorder
open scoped NNReal ProbabilityTheory

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatChain

theorem chainLaw_one (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (x₀ : UnitAddTorus (Fin 3)) :
    (chainLaw r hr hr0 δ x₀).map (fun path => path 1) =
      heatKernel r hr hr0 δ x₀ := by
  unfold chainLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.map_traj_succ_self]
  rw [Measure.map_dirac' (by fun_prop)]
  rw [Measure.dirac_bind (Kernel.measurable _)]
  rfl

theorem chainLaw_one_character (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (x₀ : UnitAddTorus (Fin 3)) (k : Wave) :
    (∫ path, UnitAddTorus.mFourier (-k) (path 1) ∂chainLaw r hr hr0 δ x₀) =
      UnitAddTorus.mFourier (-k) x₀ *
        (Real.exp (-((δ : ℝ) * (r k : ℝ))) : ℂ) := by
  rw [← integral_map (by exact (measurable_pi_apply 1).aemeasurable)]
  · rw [chainLaw_one]
    exact heatKernel_character r hr hr0 δ x₀ k
  · exact (UnitAddTorus.mFourier (-k)).continuous.measurable.aestronglyMeasurable

theorem chainLaw_next (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (x₀ : UnitAddTorus (Fin 3)) (n : ℕ) :
    (chainLaw r hr hr0 δ x₀).map (fun path => path (n+1)) =
      heatKernel r hr hr0 δ ∘ₘ
        (chainLaw r hr hr0 δ x₀).map (fun path => path n) := by
  let μ := chainLaw r hr hr0 δ x₀
  let κ := fun n => stepKernel r hr hr0 δ n
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => UnitAddTorus (Fin 3))
    (μ₀ := Measure.dirac x₀) (κ := κ) (a := n)
  have hs := congrArg Measure.snd h
  change ((μ.map (frestrictLe n)) ⊗ₘ κ n).snd =
    (μ.map (fun x => (frestrictLe n x, x (n+1)))).snd at hs
  rw [Measure.snd_compProd,
    Measure.snd_map_prodMk (measurable_frestrictLe n) (by fun_prop)] at hs
  have hstep : κ n ∘ₘ μ.map (frestrictLe n) =
      heatKernel r hr hr0 δ ∘ₘ μ.map (fun path => path n) := by
    change (heatKernel r hr hr0 δ).comap
      (fun past : Π _i : Finset.Iic n, UnitAddTorus (Fin 3) =>
        past ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop) ∘ₘ
      μ.map (frestrictLe n) = _
    rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map (by fun_prop)]
    congr 1
    let g : (Π _i : Finset.Iic n, UnitAddTorus (Fin 3)) →
        UnitAddTorus (Fin 3) := fun past => past ⟨n, Finset.mem_Iic.mpr le_rfl⟩
    change (μ.map (frestrictLe n)).map g = μ.map (fun path => path n)
    calc
      _ = μ.map (g ∘ frestrictLe n) :=
        Measure.map_map (by fun_prop) (measurable_frestrictLe n)
      _ = μ.map (fun path => path n) := rfl
  exact hs.symm.trans hstep

theorem chainLaw_marginal (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (x₀ : UnitAddTorus (Fin 3)) (n : ℕ) :
    (chainLaw r hr hr0 δ x₀).map (fun path => path n) =
      heatKernel r hr hr0 ((n : ℝ≥0) * δ) x₀ := by
  induction n with
  | zero =>
      simpa [heatKernel_zero, Kernel.id_apply] using
        chainLaw_initial r hr hr0 δ x₀
  | succ n ih =>
      rw [chainLaw_next, ih]
      change (heatKernel r hr hr0 δ ∘ₖ
        heatKernel r hr hr0 ((n : ℝ≥0) * δ)) x₀ = _
      rw [heatKernel_comp]
      congr 1
      simp [Nat.cast_succ, add_mul]

theorem chainLaw_character (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (x₀ : UnitAddTorus (Fin 3))
    (n : ℕ) (k : Wave) :
    (∫ path, UnitAddTorus.mFourier (-k) (path n) ∂chainLaw r hr hr0 δ x₀) =
      UnitAddTorus.mFourier (-k) x₀ *
        (Real.exp (-((((n : ℝ≥0) * δ) : ℝ) * (r k : ℝ))) : ℂ) := by
  rw [← integral_map (by exact (measurable_pi_apply n).aemeasurable)]
  · rw [chainLaw_marginal]
    exact heatKernel_character r hr hr0 ((n : ℝ≥0) * δ) x₀ k
  · exact (UnitAddTorus.mFourier (-k)).continuous.measurable.aestronglyMeasurable

end OperatorDerivativeRewrite.Foundation.PhysicalHeatChain
