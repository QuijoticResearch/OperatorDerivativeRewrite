import Foundation.PeriodicCoarsePhysicalInverse
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual fine Hilbert projection removes precisely closed fields and preserves curl energy. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicFinePhysicalProjection
open PeriodicInteriorGaugeKernel PeriodicCoarseCurl
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

abbrev Fine := EuclideanSpace ℝ Edge

def raw : Fine ≃ₗ[ℝ] (Edge → ℝ) := WithLp.linearEquiv 2 ℝ _

def fineIncidence : Fine →ₗ[ℝ] (Face → ℝ) := incidence.comp raw.toLinearMap

def closed : Submodule ℝ Fine := LinearMap.ker fineIncidence

def physical : Submodule ℝ Fine := closedᗮ

def project : Fine →L[ℝ] Fine := physical.starProjection

theorem closed_iff (x : Fine) : x ∈ closed ↔ incidence (raw x) = 0 := Iff.rfl

theorem inner_raw (x y : Fine) : inner ℝ x y = dotProduct (raw x) (raw y) := by
  rw [PiLp.inner_apply]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro e _
  change inner ℝ (x e) (y e) = x e * y e
  simp [RCLike.inner_apply, mul_comm]

theorem physical_iff (x : Fine) : x ∈ physical ↔
    ∀ g : Edge → ℝ, incidence g = 0 → dotProduct (raw x) g = 0 := by
  change x ∈ closedᗮ ↔ _
  rw [Submodule.mem_orthogonal']
  constructor
  · intro hx g hg
    have h := hx (raw.symm g) ((closed_iff _).mpr (by simpa using hg))
    rw [inner_raw, raw.apply_symm_apply] at h
    exact h
  · intro hx y hy
    rw [inner_raw]
    exact hx (raw y) ((closed_iff _).mp hy)

theorem project_mem (x : Fine) : project x ∈ physical :=
  (physical.orthogonalProjectionOnto x).property

theorem project_difference_closed (x : Fine) : x - project x ∈ closed := by
  have he : project x = x - closed.starProjection x :=
    closed.starProjection_orthogonal_val x
  rw [he, sub_sub_cancel]
  exact (closed.orthogonalProjectionOnto x).property

theorem project_incidence (x : Fine) : incidence (raw (project x)) = incidence (raw x) := by
  have h := (closed_iff _).mp (project_difference_closed x)
  rw [map_sub, map_sub, sub_eq_zero] at h
  exact h.symm

theorem project_energy (x : Fine) : fineEnergy (raw (project x)) = fineEnergy (raw x) := by
  unfold fineEnergy
  rw [project_incidence]

theorem project_norm_le (x : Fine) : ‖project x‖ ≤ ‖x‖ :=
  physical.norm_starProjection_apply_le x

theorem project_eq_self {x : Fine} (hx : x ∈ physical) : project x = x :=
  physical.starProjection_eq_self_iff.mpr hx

theorem project_idempotent (x : Fine) : project (project x) = project x :=
  project_eq_self (project_mem x)

end OperatorDerivativeRewrite.Foundation.PeriodicFinePhysicalProjection
