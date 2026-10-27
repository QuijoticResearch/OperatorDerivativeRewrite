import Foundation.PhysicalHeatKernel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# A genuine discrete-time heat chain

For each fixed nonnegative time step, the Ionescu--Tulcea trajectory theorem
realizes the verified physical heat transition kernel as a probability law on
countable torus paths. The initial coordinate is the chosen starting point,
and the next coordinate has the heat kernel as its regular conditional law
given the entire finite past. No continuous-time path regularity is asserted.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open PhysicalHeatKernel
open MeasureTheory AddCircle ProbabilityTheory Function Preorder
open scoped NNReal ProbabilityTheory

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatChain

def stepKernel (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (n : ℕ) :
    Kernel (Π _i : Finset.Iic n, UnitAddTorus (Fin 3)) (UnitAddTorus (Fin 3)) :=
  (heatKernel r hr hr0 δ).comap
    (fun past => past ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance stepKernel_isMarkov (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (n : ℕ) :
    IsMarkovKernel (stepKernel r hr hr0 δ n) := by
  unfold stepKernel
  infer_instance

theorem stepKernel_apply (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (n : ℕ)
    (past : Π _i : Finset.Iic n, UnitAddTorus (Fin 3)) :
    stepKernel r hr hr0 δ n past =
      heatKernel r hr hr0 δ (past ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := rfl

def chainLaw (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (x₀ : UnitAddTorus (Fin 3)) :
    Measure (ℕ → UnitAddTorus (Fin 3)) :=
  Kernel.trajMeasure (Measure.dirac x₀) (fun n => stepKernel r hr hr0 δ n)

instance chainLaw_isProbability (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (x₀ : UnitAddTorus (Fin 3)) :
    IsProbabilityMeasure (chainLaw r hr hr0 δ x₀) := by
  unfold chainLaw
  infer_instance

theorem chainLaw_condDistrib (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (x₀ : UnitAddTorus (Fin 3)) (n : ℕ) :
    condDistrib (fun path : ℕ → UnitAddTorus (Fin 3) => path (n+1))
      (frestrictLe n) (chainLaw r hr hr0 δ x₀) =ᵐ[
        (chainLaw r hr hr0 δ x₀).map (frestrictLe n)]
      stepKernel r hr hr0 δ n := by
  exact Kernel.condDistrib_trajMeasure

theorem chainLaw_initial (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (δ : ℝ≥0) (x₀ : UnitAddTorus (Fin 3)) :
    (chainLaw r hr hr0 δ x₀).map (fun path => path 0) = Measure.dirac x₀ := by
  unfold chainLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop)]
  let κ := fun n => stepKernel r hr hr0 δ n
  have hcoord : (Kernel.traj (X := fun _ : ℕ => UnitAddTorus (Fin 3)) κ 0).map
      (fun path => path 0) =
      Kernel.deterministic
        (fun past : Π i : Finset.Iic 0, UnitAddTorus (Fin 3) =>
          past ⟨0, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop) := by
    have hf : (fun path : ℕ → UnitAddTorus (Fin 3) => path 0) =
        (fun past : Π i : Finset.Iic 0, UnitAddTorus (Fin 3) =>
          past ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘ frestrictLe 0 := rfl
    rw [hf, Kernel.map_comp_right _ (measurable_frestrictLe 0) (by fun_prop),
      Kernel.traj_map_frestrictLe_of_le (le_refl 0)]
    ext past
    rw [Kernel.map_apply _ (by fun_prop), Kernel.deterministic_apply,
      Measure.map_dirac' (by fun_prop), Kernel.deterministic_apply]
    rfl
  rw [hcoord]
  rw [Measure.deterministic_comp_eq_map (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_dirac' (by fun_prop)]
  rfl

end OperatorDerivativeRewrite.Foundation.PhysicalHeatChain
