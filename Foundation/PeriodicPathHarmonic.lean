import Foundation.PeriodicPathGaugeQuotient
import Foundation.PeriodicCoarseEnergy
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Four independent closed non-exact classes survive the actual path retraction. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicPathHarmonic
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseGaugeDiagnostics PeriodicCoarseEnergy
open PeriodicPathCochain PeriodicPathGaugeQuotient
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem coarseShift_twice : ∀ (q : CoarseVertex) (i : Direction),
    coarseShift (coarseShift q i) i = q := by decide

theorem gradient_cycle_zero (φ : CoarseVertex → ℝ) (q : CoarseVertex) (i : Direction) :
    coarseGradient φ (q,i) + coarseGradient φ (coarseShift q i,i) = 0 := by
  change (φ (coarseShift q i) - φ q) +
    (φ (coarseShift (coarseShift q i) i) - φ (coarseShift q i)) = 0
  rw [coarseShift_twice]
  ring

def harmonicField : (Direction → ℝ) →ₗ[ℝ] (CoarseEdge → ℝ) :=
  LinearMap.pi (fun e => LinearMap.proj e.2)

theorem harmonicField_apply (a : Direction → ℝ) (e : CoarseEdge) :
    harmonicField a e = a e.2 := rfl

theorem harmonic_curl_zero (a : Direction → ℝ) (q : CoarseVertex) (i j : Direction) :
    coarseCurl (harmonicField a) q i j = 0 := by
  simp only [coarseCurl, harmonicField_apply]
  ring

theorem harmonic_energy_zero (a : Direction → ℝ) : coarseEnergy (harmonicField a) = 0 := by
  unfold coarseEnergy
  have h (p : CoarseFace) : coarseIncidence (harmonicField a) p = 0 :=
    harmonic_curl_zero a _ _ _
  simp [h]

theorem harmonic_gradient_iff (a : Direction → ℝ) :
    harmonicField a ∈ LinearMap.range coarseGradient ↔ a = 0 := by
  constructor
  · rintro ⟨φ, hφ⟩
    funext i
    have h := gradient_cycle_zero φ coarseOrigin i
    rw [hφ] at h
    change a i + a i = 0 at h
    change a i = 0
    linarith
  · rintro rfl
    simp

def harmonicClass : (Direction → ℝ) →ₗ[ℝ] CoarseGaugeQuotient :=
  (LinearMap.range coarseGradient).mkQ.comp harmonicField

theorem harmonicClass_mk (a : Direction → ℝ) :
    harmonicClass a = Submodule.Quotient.mk (harmonicField a) := rfl

theorem harmonicClass_injective : Function.Injective harmonicClass := by
  intro a b h
  have hz : harmonicClass (a-b) = 0 := by rw [map_sub, h, sub_self]
  rw [harmonicClass_mk] at hz
  have hr := (Submodule.Quotient.mk_eq_zero _).mp hz
  exact sub_eq_zero.mp ((harmonic_gradient_iff (a-b)).mp hr)

theorem harmonicClass_range_finrank : Module.finrank ℝ (LinearMap.range harmonicClass) = 4 := by
  rw [LinearMap.finrank_range_of_inj harmonicClass_injective]
  exact Module.finrank_fin_fun ℝ

def liftedHarmonicClass : (Direction → ℝ) →ₗ[ℝ] FineGaugeQuotient :=
  quotientLift.comp harmonicClass

theorem liftedHarmonicClass_mk (a : Direction → ℝ) :
    liftedHarmonicClass a = Submodule.Quotient.mk (flatLift (harmonicField a)) := by
  change quotientLift (harmonicClass a) = _
  rw [harmonicClass_mk, quotientLift_mk]

theorem liftedHarmonicClass_injective : Function.Injective liftedHarmonicClass :=
  quotientLift_injective.comp harmonicClass_injective

theorem liftedHarmonicClass_range_finrank :
    Module.finrank ℝ (LinearMap.range liftedHarmonicClass) = 4 := by
  rw [LinearMap.finrank_range_of_inj liftedHarmonicClass_injective]
  exact Module.finrank_fin_fun ℝ

theorem lifted_harmonic_closed (a : Direction → ℝ) :
    incidence (flatLift (harmonicField a)) = 0 := by
  funext p
  change curl (flatLift (harmonicField a)) p.val.1 p.val.2.1 p.val.2.2 = 0
  rw [flatLift_curl _ _ _ _ (ne_of_lt p.property)]
  simp [harmonic_curl_zero]

theorem lifted_harmonic_energy_zero (a : Direction → ℝ) :
    fineEnergy (flatLift (harmonicField a)) = 0 := by
  simp [fineEnergy, lifted_harmonic_closed]

theorem lifted_harmonic_not_exact (a : Direction → ℝ) (ha : a ≠ 0) :
    flatLift (harmonicField a) ∉ LinearMap.range gradientMap := by
  intro h
  have hp : pathMap (flatLift (harmonicField a)) ∈ LinearMap.range coarseGradient :=
    path_gradient_compatible h
  rw [pathMap_flatLift] at hp
  exact ha ((harmonic_gradient_iff a).mp hp)

end OperatorDerivativeRewrite.Foundation.PeriodicPathHarmonic
