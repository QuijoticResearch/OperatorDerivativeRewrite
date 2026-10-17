import Foundation.SU2StapleTiltLaw

/-! Sharp aligned concentration and an actual cancelling SU(2) staple pair. -/
noncomputable section
open MeasureTheory
open scoped Quaternion Matrix
namespace OperatorDerivativeRewrite.Foundation.SU2StapleExtremes
open QuaternionSU2Representation SU2TraceHessianModel SU2StaplePolar SU2StapleTiltLaw
open BoundedExponentialTiltResponse
set_option backward.isDefEq.respectTransparency false

theorem recover_one : recover (1 : M2) = (1 : ℍ) := by
  rw [← repr_one, recover_repr]

theorem identity_sum {ι : Type*} (s : Finset ι) :
    quaternionSum s (fun _ => (1 : SU2)) = (s.card : ℍ) := by
  simp [quaternionSum, recover_one]

theorem identity_radius {ι : Type*} (s : Finset ι) :
    ‖quaternionSum s (fun _ => (1 : SU2))‖ = (s.card : ℝ) := by
  rw [identity_sum]
  rw [← Quaternion.coe_natCast, Quaternion.norm_coe]
  simp

theorem identity_concentration {ι : Type*} (s : Finset ι) (β : ℝ) :
    concentration s (fun _ => (1 : SU2)) β = β * (s.card : ℝ) := by
  rw [concentration, identity_radius]

theorem eight_exceeds_six (β : ℝ) (hβ : 0 < β) :
    6 * β < concentration (Finset.univ : Finset (Fin 8)) (fun _ => (1 : SU2)) β := by
  rw [identity_concentration]
  norm_num
  linarith

def minusOne : SU2 := hom ⟨(-1 : ℍ), by simp [Unitary.mem_iff]⟩

def cancellingPair : Fin 2 → SU2 := ![1, minusOne]

theorem cancelling_sum : quaternionSum Finset.univ cancellingPair = 0 := by
  simp [quaternionSum, cancellingPair, Fin.sum_univ_two, minusOne, hom,
    recover_one, recover_repr]

theorem cancelling_staple : staple Finset.univ cancellingPair = 0 :=
  (staple_zero_iff _ _).mpr cancelling_sum

theorem cancelling_concentration (β : ℝ) :
    concentration Finset.univ cancellingPair β = 0 := by
  simp [concentration, cancelling_sum]

theorem zero_tilt (ν : Measure SU2) [IsProbabilityMeasure ν] (X : SU2 → ℝ) :
    tiltedMeasure ν X 0 = ν := by
  simp [tiltedMeasure, density, partition_zero]

theorem cancelling_law (ν : Measure SU2) [IsProbabilityMeasure ν] (β : ℝ) :
    stapleLaw ν Finset.univ cancellingPair β = ν := by
  rw [stapleLaw, cancelling_concentration, zero_tilt]

end OperatorDerivativeRewrite.Foundation.SU2StapleExtremes
