import Foundation.PeriodicCoarseClosedReconstruction

/-! All closed coarse gradient classes are exactly the four harmonic classes. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseClosedClasses
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseGaugeDiagnostics PeriodicPathHarmonic PeriodicCoarseWalshBasis
open PeriodicCoarseClosedReconstruction
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def closedClasses : Submodule ℝ CoarseGaugeQuotient :=
  (LinearMap.ker coarseIncidence).map (LinearMap.range coarseGradient).mkQ

theorem harmonic_incidence_zero (a : Direction → ℝ) : coarseIncidence (harmonicField a) = 0 := by
  funext p
  exact harmonic_curl_zero a _ _ _

theorem closedClasses_eq_harmonicRange : closedClasses = LinearMap.range harmonicClass := by
  ext q
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨harmonicVector f, (closed_class f hf).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨harmonicField a, harmonic_incidence_zero a, rfl⟩

theorem closedClasses_finrank : Module.finrank ℝ closedClasses = 4 := by
  rw [closedClasses_eq_harmonicRange]
  exact harmonicClass_range_finrank

def harmonicEquiv : (Direction → ℝ) ≃ₗ[ℝ] closedClasses :=
  (LinearEquiv.ofInjective harmonicClass harmonicClass_injective).trans
    (LinearEquiv.ofEq (LinearMap.range harmonicClass) closedClasses
      closedClasses_eq_harmonicRange.symm)

theorem harmonicEquiv_apply (a : Direction → ℝ) :
    (harmonicEquiv a : CoarseGaugeQuotient) = harmonicClass a := by
  rfl

theorem closed_exact_iff_harmonic_zero (f : Field) (hf : coarseIncidence f = 0) :
    f ∈ LinearMap.range coarseGradient ↔ harmonicVector f = 0 := by
  rw [← Submodule.Quotient.mk_eq_zero (LinearMap.range coarseGradient), closed_class f hf]
  constructor
  · intro h
    apply harmonicClass_injective
    simpa using h
  · rintro h
    rw [h, map_zero]

theorem closed_classes_equal_iff (f g : Field) (hf : coarseIncidence f = 0)
    (hg : coarseIncidence g = 0) :
    (Submodule.Quotient.mk f : CoarseGaugeQuotient) = Submodule.Quotient.mk g ↔
      harmonicVector f = harmonicVector g := by
  rw [closed_class f hf, closed_class g hg]
  exact harmonicClass_injective.eq_iff

theorem closed_exact_iff_zeroMean (f : Field) (hf : coarseIncidence f = 0) :
    f ∈ LinearMap.range coarseGradient ↔ ∀ i : Direction, (∑ q : CoarseVertex, f (q,i)) = 0 := by
  rw [closed_exact_iff_harmonic_zero f hf]
  constructor
  · intro h i
    have hi := congrFun h i
    rw [harmonicVector_mean] at hi
    change (1/16 : ℝ) * (∑ q : CoarseVertex, f (q,i)) = 0 at hi
    linarith
  · intro h
    funext i
    rw [harmonicVector_mean, h i, mul_zero]
    rfl

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseClosedClasses
