import Foundation.IBMPhysicalWhiteNoiseObstruction
import Mathlib.Analysis.Normed.Module.DoubleDual

/-! A physical negative-Sobolev extension of actual scenery Wiener pairings.
Tests retain their physical dual norm, not the ambient Gaussian L2 norm.
Only the closed real physical kernel space has a faithful stochastic meaning. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalWeakWiener
open InfiniteGaussian GaussianTimeHilbert IBMPhysicalNoiseRealization
local instance : NormedSpace ℝ H^{(-1 : ℝ)}(ℝ) := NormedSpace.restrictScalars ℝ ℂ _

abbrev Kernel := H^{(-1 : ℝ)}(ℝ)
abbrev Tests := StrongDual ℝ Kernel

def kernelTest : Tests →L[ℝ] TimeHilbert :=
  (InnerProductSpace.toDual ℝ TimeHilbert).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (IBMPhysicalNegativeEmbedding.embedding.precomp ℝ)

theorem kernelTest_pairing (L : Tests) (u : TimeHilbert) :
    inner ℝ (kernelTest L) u = L (IBMPhysicalNegativeEmbedding.embedding u) := by
  exact InnerProductSpace.toDual_symm_apply
    (x := u) (y := L.comp IBMPhysicalNegativeEmbedding.embedding)

def testNoise : Tests →L[ℝ] GaussianL2 := physicalNoise.toContinuousLinearMap.comp kernelTest

def native : GaussianL2 →L[ℝ] StrongDual ℝ Tests :=
  (testNoise.precomp ℝ).comp (innerSL ℝ)

def integral : Kernel →L[ℝ] StrongDual ℝ Tests :=
  NormedSpace.inclusionInDoubleDual ℝ Kernel

theorem native_apply (F : GaussianL2) (L : Tests) :
    native F L = inner ℝ F (testNoise L) := rfl

theorem integral_apply (U : Kernel) (L : Tests) : integral U L = L U := rfl

theorem integral_norm (U : Kernel) : ‖integral U‖ = ‖U‖ :=
  (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map U

theorem actual_pairing (u : TimeHilbert) (L : Tests) :
    native (physicalNoise u) L = L (IBMPhysicalNegativeEmbedding.embedding u) := by
  change inner ℝ (physicalNoise u) (physicalNoise (kernelTest L)) = _
  rw [physicalNoise.inner_map_map, real_inner_comm, kernelTest_pairing]

theorem native_agreement (u : TimeHilbert) :
    native (physicalNoise u) = integral (IBMPhysicalNegativeEmbedding.embedding u) := by
  ext L
  exact actual_pairing u L

theorem expectation_pairing (u : TimeHilbert) (L : Tests) :
    (∫ X, physicalNoise u X * testNoise L X ∂gaussianProduct) =
      L (IBMPhysicalNegativeEmbedding.embedding u) := by
  rw [← actual_pairing u L, native_apply, L2_inner_eq_integral]
  simp only [Real.inner_apply]

def physicalSpace : Submodule ℝ Kernel :=
  IBMPhysicalNegativeEmbedding.embedding.range.topologicalClosure

/-- Coincident actual Gaussian tests give the same action on the closed
real physical kernel space. No imaginary or invisible channel is added. -/
theorem annihilator (U : Kernel) (hU : U ∈ physicalSpace) (L : Tests)
    (hL : testNoise L = 0) : L U = 0 := by
  have hk : kernelTest L = 0 := physicalNoise.injective (by
    change physicalNoise (kernelTest L) = 0 at hL
    simpa only [map_zero] using hL)
  have hr : IBMPhysicalNegativeEmbedding.embedding.range ≤ L.ker := by
    rintro v ⟨u, rfl⟩
    change L (IBMPhysicalNegativeEmbedding.embedding u) = 0
    rw [← kernelTest_pairing, hk, inner_zero_left]
  exact (IBMPhysicalNegativeEmbedding.embedding.range.topologicalClosure_minimal
    hr L.isClosed_ker) hU

theorem actual_test_consistency (U : Kernel) (hU : U ∈ physicalSpace)
    (L M : Tests) (h : testNoise L = testNoise M) : integral U L = integral U M := by
  have hz : testNoise (L-M) = 0 := by rw [map_sub, h, sub_self]
  have hh := annihilator U hU (L-M) hz
  exact sub_eq_zero.mp hh

theorem unique_on_physicalSpace (A : Kernel →L[ℝ] StrongDual ℝ Tests)
    (hA : ∀ u : TimeHilbert,
      A (IBMPhysicalNegativeEmbedding.embedding u) = native (physicalNoise u))
    (U : Kernel) (hU : U ∈ physicalSpace) : A U = integral U := by
  have hr : IBMPhysicalNegativeEmbedding.embedding.range ≤ (A-integral).ker := by
    rintro v ⟨u, rfl⟩
    change A (IBMPhysicalNegativeEmbedding.embedding u)-
      integral (IBMPhysicalNegativeEmbedding.embedding u) = 0
    rw [hA, native_agreement, sub_self]
  have hz := (IBMPhysicalNegativeEmbedding.embedding.range.topologicalClosure_minimal
    hr (A-integral).isClosed_ker) hU
  exact sub_eq_zero.mp hz

theorem integral_tendsto {U : ℕ → Kernel} {V : Kernel}
    (h : Tendsto U atTop (nhds V)) :
    Tendsto (fun n => integral (U n)) atTop (nhds (integral V)) :=
  integral.continuous.tendsto V |>.comp h

theorem actual_native_limit {u : ℕ → TimeHilbert} {V : Kernel}
    (h : Tendsto (fun n => IBMPhysicalNegativeEmbedding.embedding (u n))
      atTop (nhds V)) :
    Tendsto (fun n => native (physicalNoise (u n))) atTop (nhds (integral V)) := by
  simpa only [native_agreement] using integral_tendsto h

theorem dirac_native_limit :
    Tendsto (fun n => native (physicalNoise (IBMPhysicalWhiteNoiseObstruction.profile n)))
      atTop (nhds (integral (IBMPhysicalDirac.dirac 0))) :=
  actual_native_limit IBMPhysicalWhiteNoiseObstruction.profile_hminus_tendsto

theorem dirac_mem_physicalSpace : IBMPhysicalDirac.dirac 0 ∈ physicalSpace := by
  apply IBMPhysicalNegativeEmbedding.embedding.range.isClosed_topologicalClosure.mem_of_tendsto
    IBMPhysicalWhiteNoiseObstruction.profile_hminus_tendsto
  exact Filter.Eventually.of_forall fun n =>
    IBMPhysicalNegativeEmbedding.embedding.range.le_topologicalClosure (by
      exact ⟨IBMPhysicalWhiteNoiseObstruction.profile n, rfl⟩)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalWeakWiener
