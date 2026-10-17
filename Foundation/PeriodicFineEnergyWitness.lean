import Foundation.PeriodicFineEnergyWitnessCertificates

/-! Normalized concrete fields, actual projection, and Green equation for the witness. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicFineEnergyWitness
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseGaugeDiagnostics PeriodicFinePhysicalGreen PeriodicProjectedCoarseLift
open PeriodicFineEnergyWitnessCertificates
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def c : CoarseEdge → ℝ := average badGradient

def a : Edge → ℝ := (1/8 : ℝ) • (fun e => (aZ e : ℝ))
def p : Edge → ℝ := (1/24 : ℝ) • (fun e => (pZ e : ℝ))
def z : Edge → ℝ := (1/6 : ℝ) • p + (1/3 : ℝ) • a
def k : Edge → ℝ := (1/6 : ℝ) • z + (1/6 : ℝ) • a

theorem c_cast : c = (1/8 : ℝ) • (fun q => (averageZ (gradient badPotentialZ) q : ℝ)) := by
  have hb : badGradient = fun e => (gradient badPotentialZ e : ℝ) := funext badGradient_cast
  funext q
  rw [c, hb, average_cast]
  rfl

set_option maxHeartbeats 16000000 in
-- Kernel arithmetic certifies normalization and averaging on the actual finite lattice.
theorem flat_w_int : ∀ e : Edge,
    flatLiftZ (averageZ (gradient badPotentialZ)) e = 8 * wZ e := by decide

set_option maxHeartbeats 16000000 in
-- Kernel arithmetic certifies normalization and averaging on the actual finite lattice.
theorem average_a_int : ∀ q : CoarseEdge,
    2 * averageZ aZ q = averageZ (gradient badPotentialZ) q := by decide

theorem rawLift_formula : normalizedLift c = (1/8 : ℝ) • (fun e => (wZ e : ℝ)) := by
  rw [c_cast, map_smul, normalizedLift, LinearMap.smul_apply, flatLift_cast]
  funext e
  simp only [Pi.smul_apply, smul_eq_mul, flat_w_int, Int.cast_mul, Int.cast_ofNat]
  ring

theorem p_formula : p = normalizedLift c - (1/24 : ℝ) • badGradient := by
  rw [rawLift_formula]
  funext e
  simp only [p, pZ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Int.cast_sub,
    Int.cast_mul, Int.cast_ofNat, badGradient_cast]
  ring

theorem gram_a : G a = (2 : ℝ) • a := by
  rw [a, map_smul, G_cast]
  funext e
  simp only [gram_a_int, Int.cast_mul, Int.cast_ofNat, Pi.smul_apply, smul_eq_mul]
  ring

theorem gram_p : G p = (6 : ℝ) • p - (4 : ℝ) • a := by
  rw [p, map_smul, G_cast]
  funext e
  simp only [gram_p_int, a, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem gram_z : G z = p := by
  rw [z, map_add, map_smul, map_smul, gram_p, gram_a]
  funext e
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem gram_k : G k = z := by
  rw [k, map_add, map_smul, map_smul, gram_z, gram_a, z]
  funext e
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem p_physical : p ∈ fineSpace := by
  rw [← gram_z]
  exact gram_mem_physical z

theorem z_physical : z ∈ fineSpace := by
  rw [← gram_k]
  exact gram_mem_physical k

theorem projectedLift_formula : projectedLift c = p := by
  have hi : incidence p = incidence (normalizedLift c) := by
    rw [p_formula, map_sub, map_smul, badGradient_fine_closed, smul_zero, sub_zero]
  have hd : incidence (p - projectedLift c) = 0 := by
    rw [map_sub, hi, projectedLift_incidence, sub_self]
  have hp : p - projectedLift c ∈ fineSpace :=
    fineSpace.sub_mem p_physical (projectedLift_physical c)
  exact (sub_eq_zero.mp (dotProduct_self_eq_zero.mp (hp _ hd))).symm

theorem average_p : average p = (1/12 : ℝ) • c := by
  rw [p_formula, map_sub, map_smul, average_normalizedLift]
  change (1/8 : ℝ) • c - (1/24 : ℝ) • c = _
  funext q
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem average_a : average a = (1/16 : ℝ) • c := by
  rw [a, map_smul, c_cast]
  funext q
  simp only [Pi.smul_apply, smul_eq_mul, average_cast]
  have h : 2 * (averageZ aZ q : ℝ) = (averageZ (gradient badPotentialZ) q : ℝ) := by
    exact_mod_cast average_a_int q
  linarith

theorem average_z : average z = (5/144 : ℝ) • c := by
  rw [z, map_add, map_smul, map_smul, average_p, average_a]
  funext q
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end OperatorDerivativeRewrite.Foundation.PeriodicFineEnergyWitness
