import Foundation.PeriodicPathCochain
import Foundation.PeriodicCoarseGaugeDiagnostics

/-! A genuine coarse/fine retraction on gradient quotients via path integration. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicPathGaugeQuotient
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseGaugeDiagnostics PeriodicPathCochain
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem path_gradient_compatible :
    LinearMap.range gradientMap ≤ (LinearMap.range coarseGradient).comap pathMap := by
  rintro f ⟨φ, rfl⟩
  change pathMap (gradientMap φ) ∈ LinearMap.range coarseGradient
  rw [pathMap_gradient]
  exact ⟨samplePotential φ, rfl⟩

theorem lift_gradient_compatible :
    LinearMap.range coarseGradient ≤ (LinearMap.range gradientMap).comap flatLift := by
  rintro c ⟨φ, rfl⟩
  change flatLift (coarseGradient φ) ∈ LinearMap.range gradientMap
  rw [flatLift_gradient]
  exact ⟨fun v => φ (coarseBlock v), rfl⟩

def quotientPath : FineGaugeQuotient →ₗ[ℝ] CoarseGaugeQuotient :=
  (LinearMap.range gradientMap).mapQ (LinearMap.range coarseGradient)
    pathMap path_gradient_compatible

def quotientLift : CoarseGaugeQuotient →ₗ[ℝ] FineGaugeQuotient :=
  (LinearMap.range coarseGradient).mapQ (LinearMap.range gradientMap)
    flatLift lift_gradient_compatible

theorem quotientPath_mk (f : Edge → ℝ) :
    quotientPath (Submodule.Quotient.mk f) = Submodule.Quotient.mk (pathMap f) := rfl

theorem quotientLift_mk (c : CoarseEdge → ℝ) :
    quotientLift (Submodule.Quotient.mk c) = Submodule.Quotient.mk (flatLift c) := rfl

theorem quotientPath_lift (q : CoarseGaugeQuotient) : quotientPath (quotientLift q) = q := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range coarseGradient) q
  rw [quotientLift_mk, quotientPath_mk, pathMap_flatLift]

theorem quotient_retraction : quotientPath.comp quotientLift = LinearMap.id := by
  apply LinearMap.ext
  exact quotientPath_lift

theorem quotientPath_surjective : Function.Surjective quotientPath :=
  fun q => ⟨quotientLift q, quotientPath_lift q⟩

theorem quotientLift_injective : Function.Injective quotientLift := by
  intro q r h
  have hp := congrArg quotientPath h
  simpa only [quotientPath_lift] using hp

theorem pathMap_ne_average : pathMap ≠ average := by
  intro h
  have hp : pathMap badGradient ∈ LinearMap.range coarseGradient :=
    path_gradient_compatible ⟨badPotential, rfl⟩
  rw [h] at hp
  exact averaged_bad_not_gradient hp

def quotientProjection : FineGaugeQuotient →ₗ[ℝ] FineGaugeQuotient :=
  quotientLift.comp quotientPath

theorem quotientProjection_idempotent (q : FineGaugeQuotient) :
    quotientProjection (quotientProjection q) = quotientProjection q := by
  change quotientLift (quotientPath (quotientLift (quotientPath q))) =
    quotientLift (quotientPath q)
  rw [quotientPath_lift]

theorem quotientProjection_fixed (q : CoarseGaugeQuotient) :
    quotientProjection (quotientLift q) = quotientLift q := by
  change quotientLift (quotientPath (quotientLift q)) = _
  rw [quotientPath_lift]

end OperatorDerivativeRewrite.Foundation.PeriodicPathGaugeQuotient
