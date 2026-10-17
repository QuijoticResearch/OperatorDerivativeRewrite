import Foundation.ComplexRootPoissonKernel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! An actual infinite discrete-time compound-root process, with its conditional laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Preorder Finset
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonTrajectory
open ComplexRootPoissonKernel

abbrev History (n : ℕ) := (i : Iic n) → ℂ
abbrev Sample := ℕ → ℂ

def historyKernel (a : ℝ) (δ : ℝ≥0) (n : ℕ) : Kernel (History n) ℂ :=
  (kernel a δ).comap (fun h => h ⟨n, by simp⟩)
    (measurable_pi_apply (X := fun _ : ↥(Iic n) => ℂ) ⟨n, by simp⟩)

instance historyKernel_isMarkov (a : ℝ) (δ : ℝ≥0) (n : ℕ) :
    IsMarkovKernel (historyKernel a δ n) := by
  unfold historyKernel
  infer_instance

theorem historyKernel_apply (a : ℝ) (δ : ℝ≥0) (n : ℕ) (h : History n) :
    historyKernel a δ n h = kernel a δ (h ⟨n, by simp⟩) := rfl

def law (a : ℝ) (δ : ℝ≥0) : Measure Sample :=
  Kernel.trajMeasure (X := fun _ => ℂ) (Measure.dirac 0) (historyKernel a δ)

instance law_isProbability (a : ℝ) (δ : ℝ≥0) : IsProbabilityMeasure (law a δ) := by
  unfold law
  infer_instance

def coordinate (n : ℕ) (ω : Sample) : ℂ := ω n

theorem coordinate_measurable (n : ℕ) : Measurable (coordinate n) :=
  measurable_pi_apply n

theorem law_eq_traj (a : ℝ) (δ : ℝ≥0) :
    law a δ = Kernel.traj (historyKernel a δ) 0 (fun _ => 0) := by
  unfold law Kernel.trajMeasure
  rw [Measure.map_dirac]
  change Measure.bind (Measure.dirac _) _ = _
  rw [Measure.dirac_bind (Kernel.measurable _)]
  rfl

theorem prefix_law (a : ℝ) (δ : ℝ≥0) (n : ℕ) :
    (law a δ).map (frestrictLe n) =
      Kernel.partialTraj (X := fun _ => ℂ) (historyKernel a δ) 0 n (fun _ => 0) := by
  rw [law_eq_traj]
  exact Kernel.traj_map_frestrictLe_apply _ _ _

theorem initial_law (a : ℝ) (δ : ℝ≥0) :
    (law a δ).map (coordinate 0) = Measure.dirac 0 := by
  have hm : Measurable (fun h : History 0 => h ⟨0, by simp⟩) :=
    measurable_pi_apply (X := fun _ : ↥(Iic 0) => ℂ) ⟨0, by simp⟩
  have he : coordinate 0 = (fun h : History 0 => h ⟨0, by simp⟩) ∘ frestrictLe 0 := rfl
  rw [he, ← Measure.map_map hm (measurable_frestrictLe 0), prefix_law,
    Kernel.partialTraj_self, Kernel.id_apply, Measure.map_dirac]

theorem conditional_next (a : ℝ) (δ : ℝ≥0) (n : ℕ) :
    condDistrib (coordinate (n+1)) (frestrictLe n) (law a δ)
      =ᵐ[(law a δ).map (frestrictLe n)] historyKernel a δ n := by
  exact Kernel.condDistrib_trajMeasure (X := fun _ => ℂ) (μ₀ := Measure.dirac (0 : ℂ))
    (κ := historyKernel a δ)

theorem joint_next (a : ℝ) (δ : ℝ≥0) (n : ℕ) :
    (law a δ).map (frestrictLe n) ⊗ₘ historyKernel a δ n =
      (law a δ).map (fun ω => (frestrictLe n ω, coordinate (n+1) ω)) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => ℂ) (μ₀ := Measure.dirac (0 : ℂ)) (κ := historyKernel a δ)

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonTrajectory
