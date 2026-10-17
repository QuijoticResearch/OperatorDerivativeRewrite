import Foundation.SU2BoundaryWordKernel
import Foundation.ExponentialJointDisintegration

/-! Actual globally normalized finite-word SU(2) interaction and its link conditional. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Quaternion ENNReal
namespace OperatorDerivativeRewrite.Foundation.SU2BoundaryJointLaw
open QuaternionSU2Representation SU2BoundaryWordKernel
variable {ι κ : Type*}

def interaction (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ)
    (U : ι → SU2) (A : SU2) : ℝ := SU2StapleKernel.exponent s β (family w U) A

theorem interaction_measurable (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    Measurable (Function.uncurry (interaction s w β)) := by
  have hp : Measurable (fun p : (ι → SU2) × SU2 => (family w p.1, p.2)) :=
    ((family_measurable w).comp measurable_fst).prodMk measurable_snd
  have h := (SU2StapleKernel.exponent_measurable s β).comp hp
  change Measurable (fun p : (ι → SU2) × SU2 => SU2StapleKernel.exponent s β (family w p.1) p.2)
  simpa only [Function.comp_def, Function.uncurry] using h

variable (ρ : Measure (ι → SU2)) (ν : Measure SU2)
variable [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]

theorem interaction_integrable (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    Integrable (fun p : (ι → SU2) × SU2 => Real.exp (interaction s w β p.1 p.2)) (ρ.prod ν) := by
  apply Integrable.mono' (integrable_const (Real.exp (|β| * (s.card : ℝ))))
    (interaction_measurable s w β).exp.aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans
    (SU2StapleKernel.exponent_bound s β (family w p.1) p.2))

def joint (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) : Measure ((ι → SU2) × SU2) :=
  ExponentialJointDisintegration.joint ρ ν (interaction s w β)

def boundary (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) : Measure (ι → SU2) :=
  ExponentialJointDisintegration.boundary ρ ν (interaction s w β)

theorem boundary_probability (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    IsProbabilityMeasure (boundary ρ ν s w β) :=
  ExponentialJointDisintegration.boundary_probability ρ ν _ (interaction_measurable s w β)
    (fun U => SU2StapleKernel.exponential_integrable ν s β (family w U))
    (interaction_integrable ρ ν s w β)

theorem joint_probability (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    IsProbabilityMeasure (joint ρ ν s w β) :=
  ExponentialJointDisintegration.joint_probability ρ ν _ (interaction_measurable s w β)
    (fun U => SU2StapleKernel.exponential_integrable ν s β (family w U))
    (interaction_integrable ρ ν s w β)

theorem section_kernel (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    MeasurableExponentialKernel.kernel ν (interaction s w β) =
      SU2BoundaryWordKernel.kernel ν s w β := by
  ext U : 1
  change MeasurableExponentialKernel.kernel ν (interaction s w β) U =
    SU2StapleKernel.kernel ν s β (family w U)
  rw [MeasurableExponentialKernel.kernel_apply ν _ (interaction_measurable s w β),
    SU2StapleKernel.kernel,
    MeasurableExponentialKernel.kernel_apply ν _ (SU2StapleKernel.exponent_measurable s β)]
  rfl

theorem factorization (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    joint ρ ν s w β = (boundary ρ ν s w β) ⊗ₘ SU2BoundaryWordKernel.kernel ν s w β := by
  change ExponentialJointDisintegration.joint ρ ν _ = _
  rw [ExponentialJointDisintegration.factorization ρ ν _ (interaction_measurable s w β)
    (fun U => SU2StapleKernel.exponential_integrable ν s β (family w U)), section_kernel]
  rfl

theorem boundary_marginal (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    (joint ρ ν s w β).fst = boundary ρ ν s w β :=
  ExponentialJointDisintegration.boundary_marginal ρ ν _ (interaction_measurable s w β)
    (fun U => SU2StapleKernel.exponential_integrable ν s β (family w U))
    (interaction_integrable ρ ν s w β)

theorem conditional_rectangles (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ)
    (a : Set (ι → SU2)) (b : Set SU2) (ha : MeasurableSet a) (hb : MeasurableSet b) :
    joint ρ ν s w β (a ×ˢ b) =
      ∫⁻ U in a, SU2BoundaryWordKernel.kernel ν s w β U b ∂boundary ρ ν s w β := by
  have h := ExponentialJointDisintegration.conditional_rectangles ρ ν _
    (interaction_measurable s w β)
    (fun U => SU2StapleKernel.exponential_integrable ν s β (family w U))
    (interaction_integrable ρ ν s w β) a b ha hb
  rw [section_kernel] at h
  exact h

theorem conditional_kernel (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    (joint ρ ν s w β).IsCondKernel (SU2BoundaryWordKernel.kernel ν s w β) := by
  constructor
  rw [boundary_marginal]
  exact (factorization ρ ν s w β).symm

def finiteBoundaryHaar [Fintype ι] : Measure (ι → SU2) := Measure.pi (fun _ => law)

instance finiteBoundaryHaar_probability [Fintype ι] :
    IsProbabilityMeasure (finiteBoundaryHaar (ι := ι)) := by
  unfold finiteBoundaryHaar
  infer_instance

theorem concrete_joint_probability [Fintype ι] (s : Finset κ)
    (w : κ → List (ι × Bool)) (β : ℝ) :
    IsProbabilityMeasure (joint finiteBoundaryHaar law s w β) :=
  joint_probability _ _ s w β

end OperatorDerivativeRewrite.Foundation.SU2BoundaryJointLaw
