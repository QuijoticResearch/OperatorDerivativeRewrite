import Foundation.PeriodicCoarseGradientRank

/-! Actual closed dimension nineteen and curl rank forty-five on the coarse periodic lattice. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseHodgeRanks
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseGaugeDiagnostics PeriodicCoarseWalshBasis PeriodicCoarseClosedClasses
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem gradient_le_closed : LinearMap.range coarseGradient ≤ LinearMap.ker coarseIncidence := by
  rintro _ ⟨φ, rfl⟩
  change coarseIncidence (coarseGradient φ) = 0
  funext p
  exact coarseCurl_gradient φ _ _ _

def closedMap : LinearMap.ker coarseIncidence →ₗ[ℝ] CoarseGaugeQuotient :=
  (LinearMap.range coarseGradient).mkQ.comp (LinearMap.ker coarseIncidence).subtype

theorem closedMap_range : LinearMap.range closedMap = closedClasses := by
  ext q
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.val, f.property, rfl⟩
  · rintro ⟨f, hf, hq⟩
    exact ⟨⟨f,hf⟩, hq⟩

theorem closedMap_kernel : LinearMap.ker closedMap =
    (LinearMap.range coarseGradient).comap (LinearMap.ker coarseIncidence).subtype := by
  ext f
  change (Submodule.Quotient.mk f.val : CoarseGaugeQuotient) = 0 ↔
    f.val ∈ LinearMap.range coarseGradient
  exact Submodule.Quotient.mk_eq_zero _

theorem closedMap_kernel_finrank : Module.finrank ℝ (LinearMap.ker closedMap) = 15 := by
  rw [closedMap_kernel, (Submodule.comapSubtypeEquivOfLe gradient_le_closed).finrank_eq]
  exact PeriodicCoarseGradientRank.gradient_range_finrank

theorem closed_finrank : Module.finrank ℝ (LinearMap.ker coarseIncidence) = 19 := by
  have h := LinearMap.finrank_range_add_finrank_ker closedMap
  rw [closedMap_range, closedClasses_finrank, closedMap_kernel_finrank] at h
  omega

theorem curl_range_finrank : Module.finrank ℝ (LinearMap.range coarseIncidence) = 45 := by
  have h := LinearMap.finrank_range_add_finrank_ker coarseIncidence
  rw [closed_finrank, Module.finrank_fintype_fun_eq_card, edge_card] at h
  omega

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseHodgeRanks
