import Foundation.SU2HeatBathEntropy
import Foundation.ConditioningRelativeEntropy
import Foundation.ExponentialBoundaryEquivalence

/-! A stationary finite-entropy perturbation of the actual continuous-boundary
SU(2) interaction law, obtained by conditioning a nontrivial boundary event. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
namespace OperatorDerivativeRewrite.Foundation.SU2BoundaryConditionedEntropy
open QuaternionSU2Representation SU2BoundaryJointLaw
open ConditioningRelativeEntropy ConditionalResamplingKernel

def hemisphere : Set (Unit → SU2) := {U | 0 < ((U () : SU2TraceHessianModel.M2) 0 0).re}

theorem entry_continuous :
    Continuous (fun U : Unit → SU2 => ((U () : SU2TraceHessianModel.M2) 0 0).re) := by
  have h : Continuous (fun U : Unit → SU2 => (U () : SU2TraceHessianModel.M2)) :=
    continuous_subtype_val.comp (continuous_apply ())
  exact Complex.continuous_re.comp ((continuous_apply 0).comp ((continuous_apply 0).comp h))

instance boundaryHaar_isHaar : (finiteBoundaryHaar (ι := Unit)).IsHaarMeasure := by
  unfold finiteBoundaryHaar
  infer_instance

theorem hemisphere_measurable : MeasurableSet hemisphere := by
  exact (isOpen_lt continuous_const entry_continuous).measurableSet

theorem haar_hemisphere_positive : 0 < finiteBoundaryHaar hemisphere := by
  exact IsOpen.measure_pos finiteBoundaryHaar (isOpen_lt continuous_const entry_continuous)
    ⟨fun _ => 1, by norm_num [hemisphere]⟩

theorem haar_complement_positive : 0 < finiteBoundaryHaar hemisphereᶜ := by
  let t : Set (Unit → SU2) := {U | ((U () : SU2TraceHessianModel.M2) 0 0).re < 0}
  have ht : 0 < finiteBoundaryHaar t := by
    exact IsOpen.measure_pos finiteBoundaryHaar (isOpen_lt entry_continuous continuous_const)
      ⟨fun _ => SU2HeatBathEntropy.opposite, by
        norm_num [t, SU2HeatBathEntropy.opposite,
          SU2TraceHessianModel.rotation, Matrix.one_apply]⟩
  apply lt_of_lt_of_le ht (measure_mono _)
  intro U hU
  change ((U () : SU2TraceHessianModel.M2) 0 0).re < 0 at hU
  change ¬ 0 < ((U () : SU2TraceHessianModel.M2) 0 0).re
  exact not_lt_of_ge (le_of_lt hU)

variable {κ : Type*} (s : Finset κ) (w : κ → List (Unit × Bool)) (β : ℝ)

theorem boundary_null_iff (a : Set (Unit → SU2)) :
    boundary finiteBoundaryHaar law s w β a = 0 ↔ finiteBoundaryHaar a = 0 := by
  exact ExponentialBoundaryEquivalence.null_iff _ _ _ (interaction_measurable s w β)
    (fun U => SU2StapleKernel.exponential_integrable law s β (SU2BoundaryWordKernel.family w U))
    (interaction_integrable finiteBoundaryHaar law s w β) a

theorem boundary_event_nontrivial :
    0 < boundary finiteBoundaryHaar law s w β hemisphere ∧
      boundary finiteBoundaryHaar law s w β hemisphere < 1 := by
  let μ := boundary finiteBoundaryHaar law s w β
  let _ := boundary_probability finiteBoundaryHaar law s w β
  have hp : μ hemisphere ≠ 0 := fun h => (ne_of_gt haar_hemisphere_positive)
    ((boundary_null_iff s w β hemisphere).mp h)
  have hn : μ hemisphereᶜ ≠ 0 := fun h => (ne_of_gt haar_complement_positive)
    ((boundary_null_iff s w β hemisphereᶜ).mp h)
  refine ⟨bot_lt_iff_ne_bot.mpr hp, ?_⟩
  have hle : μ hemisphere ≤ 1 := by
    calc μ hemisphere ≤ μ univ := measure_mono (subset_univ _)
         _ = 1 := measure_univ
  apply lt_of_le_of_ne hle
  intro h
  have hh := measure_add_measure_compl hemisphere_measurable (μ := μ)
  rw [h, measure_univ] at hh
  have : μ hemisphereᶜ = 0 := by simpa using hh
  exact hn this

def conditionedBoundary : Measure (Unit → SU2) :=
  cond (boundary finiteBoundaryHaar law s w β) hemisphere

instance conditionedBoundary_probability : IsProbabilityMeasure (conditionedBoundary s w β) := by
  let _ := boundary_probability finiteBoundaryHaar law s w β
  exact cond_isProbabilityMeasure (ne_of_gt (boundary_event_nontrivial s w β).1)

def perturbedJoint : Measure ((Unit → SU2) × SU2) :=
  conditionedBoundary s w β ⊗ₘ SU2BoundaryWordKernel.kernel law s w β

instance perturbedJoint_probability : IsProbabilityMeasure (perturbedJoint s w β) := by
  let _ := SU2BoundaryWordKernel.kernel_markov law s w β
  unfold perturbedJoint
  infer_instance

theorem perturbed_stationary :
    SU2ConditionalHeatBath.update law s w β ∘ₘ perturbedJoint s w β = perturbedJoint s w β := by
  let _ := SU2BoundaryWordKernel.kernel_markov law s w β
  exact every_boundary_stationary _ _

theorem entropy_finite : klDiv (perturbedJoint s w β) (joint finiteBoundaryHaar law s w β) ≠ ⊤ := by
  let _ := SU2BoundaryWordKernel.kernel_markov law s w β
  let _ := boundary_probability finiteBoundaryHaar law s w β
  rw [factorization, perturbedJoint, klDiv_compProd_left]
  exact entropy_cond_finite _ _ hemisphere_measurable (ne_of_gt (boundary_event_nontrivial s w β).1)

theorem entropy_exact :
    (klDiv (perturbedJoint s w β) (joint finiteBoundaryHaar law s w β)).toReal =
      Real.log ((boundary finiteBoundaryHaar law s w β hemisphere)⁻¹).toReal := by
  let _ := SU2BoundaryWordKernel.kernel_markov law s w β
  let _ := boundary_probability finiteBoundaryHaar law s w β
  rw [factorization, perturbedJoint, klDiv_compProd_left]
  exact entropy_cond_exact _ _ hemisphere_measurable (ne_of_gt (boundary_event_nontrivial s w β).1)

theorem entropy_positive :
    0 < (klDiv (perturbedJoint s w β) (joint finiteBoundaryHaar law s w β)).toReal := by
  let _ := SU2BoundaryWordKernel.kernel_markov law s w β
  let _ := boundary_probability finiteBoundaryHaar law s w β
  rw [factorization, perturbedJoint, klDiv_compProd_left]
  exact entropy_cond_positive _ _ hemisphere_measurable
    (ne_of_gt (boundary_event_nontrivial s w β).1) (boundary_event_nontrivial s w β).2

theorem no_strict_contraction (q : ℝ) (hq : q < 1) :
    ¬ (klDiv (SU2ConditionalHeatBath.update law s w β ∘ₘ perturbedJoint s w β)
      (joint finiteBoundaryHaar law s w β)).toReal ≤
      q * (klDiv (perturbedJoint s w β) (joint finiteBoundaryHaar law s w β)).toReal := by
  rw [perturbed_stationary]
  have hp := entropy_positive s w β
  nlinarith

end OperatorDerivativeRewrite.Foundation.SU2BoundaryConditionedEntropy
