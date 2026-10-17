import Foundation.SU2StapleKernel
import Mathlib.Probability.Kernel.Composition.MapComap

/-! Actual measurable boundary words and their normalized SU(2) link kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion Matrix
namespace OperatorDerivativeRewrite.Foundation.SU2BoundaryWordKernel
open QuaternionSU2Representation SU2TraceHessianModel
set_option backward.isDefEq.respectTransparency false

theorem multiplication_measurable : Measurable (fun p : SU2 × SU2 => p.1 * p.2) := by
  have hentry (b : Bool) (i j : Fin 2) :
      Measurable (fun p : SU2 × SU2 => ((if b then p.1 else p.2) : M2) i j) := by
    cases b
    · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        (measurable_subtype_coe.comp measurable_snd))
    · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        (measurable_subtype_coe.comp measurable_fst))
  have hm : Measurable (fun p : SU2 × SU2 => (p.1 : M2) * (p.2 : M2)) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    simp only [Matrix.mul_apply]
    apply Finset.measurable_sum
    intro k hk
    exact (hentry true i k).mul (hentry false k j)
  exact hm.subtype_mk

theorem inverse_measurable : Measurable (fun A : SU2 => A⁻¹) := by
  have hval : Measurable (fun A : SU2 => (A : M2)) := measurable_subtype_coe
  have hm : Measurable (fun A : SU2 => (A : M2)ᴴ) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    have he : Measurable (fun A : SU2 => (A : M2) j i) :=
      (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hval)
    exact Complex.continuous_conj.measurable.comp he
  exact hm.subtype_mk

variable {ι : Type*}

def letter (a : ι × Bool) (U : ι → SU2) : SU2 := if a.2 then (U a.1)⁻¹ else U a.1

theorem letter_measurable (a : ι × Bool) : Measurable (letter a) := by
  rcases a with ⟨i,b⟩
  cases b
  · exact measurable_pi_apply i
  · exact inverse_measurable.comp (measurable_pi_apply i)

def word : List (ι × Bool) → (ι → SU2) → SU2
  | [], _ => 1
  | a :: w, U => letter a U * word w U

theorem word_measurable (w : List (ι × Bool)) : Measurable (word w) := by
  induction w with
  | nil =>
    change Measurable (fun _ : ι → SU2 => (1 : SU2))
    exact measurable_const
  | cons a w ih =>
    change Measurable (fun U => letter a U * word w U)
    have hp : Measurable (fun U : ι → SU2 => (letter a U, word w U)) :=
      (letter_measurable a).prodMk ih
    have h := multiplication_measurable.comp hp
    simpa only [Function.comp_def] using h

def family {κ : Type*} (w : κ → List (ι × Bool)) (U : ι → SU2) : κ → SU2 :=
  fun j => word (w j) U

theorem family_measurable {κ : Type*} (w : κ → List (ι × Bool)) : Measurable (family w) :=
  measurable_pi_iff.mpr (fun j => word_measurable (w j))

variable (ν : Measure SU2) [IsProbabilityMeasure ν]

def kernel {κ : Type*} (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    Kernel (ι → SU2) SU2 := (SU2StapleKernel.kernel ν s β).comap (family w) (family_measurable w)

theorem kernel_markov {κ : Type*} (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    IsMarkovKernel (kernel ν s w β) := by
  let _ := SU2StapleKernel.kernel_markov ν s β
  exact inferInstanceAs (IsMarkovKernel ((SU2StapleKernel.kernel ν s β).comap
    (family w) (family_measurable w)))

theorem kernel_section {κ : Type*} [ν.IsHaarMeasure] (s : Finset κ)
    (w : κ → List (ι × Bool)) (β : ℝ) (U : ι → SU2) :
    kernel ν s w β U = SU2StapleTiltLaw.stapleLaw ν s (family w U) β :=
  SU2StapleKernel.kernel_eq_stapleLaw ν s β (family w U)

end OperatorDerivativeRewrite.Foundation.SU2BoundaryWordKernel
