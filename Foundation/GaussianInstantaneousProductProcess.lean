import Foundation.GaussianKernelPathObstruction
import Mathlib.Probability.Independence.InfinitePi

/-! A genuine product probability realization of all limiting one-time laws.
Finite restrictions and ordered two-time kernel laws are verified explicitly.
This construction does not assert joint time/sample measurability or path regularity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianInstantaneousProductProcess
open GaussianMehler GaussianAcceleratedKernelLimit FixedLawPathObstruction

abbrev PathSpace := ℝ → ℝ

def pathMeasure (x : ℝ) : Measure PathSpace :=
  Measure.infinitePi (fun t : ℝ => limitKernel t x)

instance pathMeasure_probability (x : ℝ) : IsProbabilityMeasure (pathMeasure x) := by
  unfold pathMeasure
  infer_instance

def process (t : ℝ) (ω : PathSpace) : ℝ := ω t

theorem process_measurable (t : ℝ) : Measurable (process t) := measurable_pi_apply t

theorem process_law (x t : ℝ) : HasLaw (process t) (limitKernel t x) (pathMeasure x) :=
  (measurePreserving_eval_infinitePi (fun t : ℝ => limitKernel t x) t).hasLaw

theorem process_independent (x : ℝ) : iIndepFun process (pathMeasure x) :=
  iIndepFun_infinitePi (X := fun _ : ℝ => (id : ℝ → ℝ)) (by fun_prop)

theorem finite_restriction_law (x : ℝ) (s : Finset ℝ) :
    (pathMeasure x).map s.restrict = Measure.pi (fun t : s => limitKernel t x) :=
  Measure.infinitePi_map_restrict _

theorem ordered_pair_law (x s t : ℝ) (hs : 0 ≤ s) (hst : s < t) :
    (pathMeasure x).map (fun ω => (process s ω, process t ω)) =
      (limitKernel s x).prod γ := by
  have he := Measure.infinitePi_map_eval_prod
    (P := fun r : ℝ => limitKernel r x) (ne_of_lt hst)
  change (pathMeasure x).map (fun ω => (process s ω, process t ω)) =
    (limitKernel s x).prod (limitKernel t x) at he
  rw [limit_positive t (hs.trans_lt hst), Kernel.const_apply] at he
  exact he

theorem ordered_pair_kernel_law (x s t : ℝ) (hs : 0 ≤ s) (hst : s < t) :
    (pathMeasure x).map (fun ω => (process s ω, process t ω)) =
      (limitKernel s x) ⊗ₘ limitKernel (t-s) := by
  rw [ordered_pair_law x s t hs hst, limit_positive (t-s) (sub_pos.mpr hst),
    Measure.compProd_const]

theorem initial_value (x : ℝ) : process 0 =ᵐ[pathMeasure x] fun _ => x :=
  GaussianKernelPathObstruction.zero_row_ae (pathMeasure x) process x (fun t _ => process_law x t)

theorem no_right_continuous_paths (x : ℝ) :
    ¬ ∀ᵐ ω ∂pathMeasure x, ContinuousWithinAt (fun t => process t ω) (Ici 0) 0 :=
  GaussianKernelPathObstruction.no_right_continuous_paths (pathMeasure x) process x
    (fun t _ => process_law x t)

theorem no_right_continuous_modification (x : ℝ) (Y : ℝ → PathSpace → ℝ)
    (hmod : ∀ t, Y t =ᵐ[pathMeasure x] process t) :
    ¬ ∀ᵐ ω ∂pathMeasure x, ContinuousWithinAt (fun t => Y t ω) (Ici 0) 0 :=
  GaussianKernelPathObstruction.no_right_continuous_modification (pathMeasure x) process Y x
    (fun t _ => process_law x t) hmod

end OperatorDerivativeRewrite.Foundation.GaussianInstantaneousProductProcess
