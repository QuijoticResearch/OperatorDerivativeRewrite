import Foundation.PeriodicLocalQuotientEnergy
import Mathlib.LinearAlgebra.Isomorphisms

/-! The actual local gradient quotient and its minimized, positive energy. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalGradientQuotient
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity PeriodicLocalGradientModes
  PeriodicLocalSpectralSet PeriodicLocalHodgeExact PeriodicLocalTransverseSpace
  PeriodicLocalHodgeProjection PeriodicLocalQuotientEnergy
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

abbrev GradientQuotient := Field ⧸ LinearMap.range localGradient

def quotientEquiv : GradientQuotient ≃ₗ[ℝ] transverseSpace :=
  (Submodule.quotEquivOfEq (LinearMap.range localGradient) (LinearMap.ker transverseProjection)
    transverseProjection_kernel.symm).trans
    (transverseProjection.quotKerEquivRange.trans
      (LinearEquiv.ofEq (LinearMap.range transverseProjection) transverseSpace
        transverseProjection_range))

theorem quotientEquiv_mk (f : Field) :
    (quotientEquiv (Submodule.Quotient.mk f) : Field) = transverseProjection f := by
  simp only [quotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearEquiv.coe_ofEq_apply, LinearMap.quotKerEquivRange_apply_mk]

theorem quotient_finrank : Module.finrank ℝ GradientQuotient = 17 :=
  quotientEquiv.finrank_eq.trans transverseSpace_finrank

def quotientEnergy (q : GradientQuotient) : ℝ := energy (quotientEquiv q)

def quotientSize (q : GradientQuotient) : ℝ := squaredSize (quotientEquiv q)

theorem quotientEnergy_mk (f : Field) : quotientEnergy (Submodule.Quotient.mk f) =
    energy (transverseProjection f) := by
  unfold quotientEnergy
  rw [quotientEquiv_mk]

theorem quotientSize_mk (f : Field) : quotientSize (Submodule.Quotient.mk f) =
    squaredSize (transverseProjection f) := by
  unfold quotientSize
  rw [quotientEquiv_mk]

theorem quotientSize_nonneg (q : GradientQuotient) : 0 ≤ quotientSize q :=
  squaredSize_nonneg _

theorem quotientSize_zero_iff (q : GradientQuotient) : quotientSize q=0 ↔ q=0 := by
  constructor
  · intro h
    have hv : (quotientEquiv q : Field)=0 := (squaredSize_zero_iff _).mp h
    apply quotientEquiv.injective
    apply Subtype.ext
    simpa using hv
  · intro h
    rw [h]
    simp [quotientSize, PeriodicSingleBlockCoercivity.squaredSize]

theorem quotientEnergy_bounds (q : GradientQuotient) :
    7*quotientSize q ≤ quotientEnergy q ∧ quotientEnergy q ≤ 11*quotientSize q :=
  ⟨PeriodicLocalTransverseGap.transverse_coercive (quotientEquiv q).property,
    transverse_upper_bound (quotientEquiv q).property⟩

theorem quotientEnergy_zero_iff (q : GradientQuotient) : quotientEnergy q=0 ↔ q=0 := by
  constructor
  · intro h
    apply (quotientSize_zero_iff q).mp
    have hb := (quotientEnergy_bounds q).1
    have hn := quotientSize_nonneg q
    linarith
  · intro h
    rw [h]
    simp [quotientEnergy, PeriodicSingleBlockCoercivity.energy]

theorem quotientEnergy_minimum (f : Field) :
    (∀ φ : Vertex → ℝ, quotientEnergy (Submodule.Quotient.mk f) ≤ energy (f+localGradient φ)) ∧
    ∃ φ : Vertex → ℝ, energy (f+localGradient φ)=quotientEnergy (Submodule.Quotient.mk f) := by
  rw [quotientEnergy_mk]
  refine ⟨energy_minimum_lower f, ?_⟩
  obtain ⟨φ, _, he, _⟩ := minimum_attained f
  exact ⟨φ, he⟩

theorem class_eq_iff (f g : Field) :
    (Submodule.Quotient.mk f : GradientQuotient)=Submodule.Quotient.mk g ↔
      transverseProjection f=transverseProjection g := by
  rw [Submodule.Quotient.eq]
  exact (transverseProjection_coset_iff f g).symm

theorem star_is_gradient : star ∈ LinearMap.range localGradient := by
  rw [gradient_range_eq_coreKernel, coreKernel_eq_eigenspace, Module.End.mem_eigenspace_iff]
  exact star_eigenvalue_three

theorem conditional_energy_not_class_invariant : ∃ f g : Field,
    (Submodule.Quotient.mk f : GradientQuotient)=Submodule.Quotient.mk g ∧ energy f ≠ energy g := by
  refine ⟨star, 0, ?_, ?_⟩
  · apply (Submodule.Quotient.eq _).mpr
    simpa only [sub_zero] using star_is_gradient
  · rw [star_energy]
    norm_num [PeriodicSingleBlockCoercivity.energy]

end OperatorDerivativeRewrite.Foundation.PeriodicLocalGradientQuotient
