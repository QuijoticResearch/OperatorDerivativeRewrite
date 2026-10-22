import Foundation.IBMNativeGeneratorChain

/-! Actual L1 divergence densities tested on bounded original-domain observables. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeWeakL1Divergence
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMNativeFieldMultiplier IBMNativeContractionDomain IBMNativeProductOperators
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

theorem product_integrable (a b : JointL2) :
    Integrable (fun ω => a ω * b ω) IBMSourceLaws.jointMeasure := by
  apply (L2.integrable_inner b a).congr
  exact ae_of_all _ fun ω => by
    change inner ℝ (b ω) (a ω) = a ω * b ω
    rw [Real.inner_apply,mul_comm]

theorem pairing_integrable (V U : JointFieldSpace) :
    Integrable (pairingFunction V U) IBMSourceLaws.jointMeasure :=
  (L2.integrable_inner (coordinate 0 (V 0)) (coordinate 0 (U 0))).add
    (L2.integrable_inner (coordinate 1 (V 1)) (coordinate 1 (U 1)))

theorem product_mean (a b : JointL2) :
    (∫ ω, a ω * b ω ∂IBMSourceLaws.jointMeasure) = inner ℝ a b := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    change a ω * b ω = inner ℝ (a ω) (b ω)
    rw [Real.inner_apply]

theorem pairing_mean (V U : JointFieldSpace) :
    (∫ ω, pairingFunction V U ω ∂IBMSourceLaws.jointMeasure) = inner ℝ V U := by
  have h0 := L2.integrable_inner (𝕜 := ℝ) (coordinate 0 (V 0)) (coordinate 0 (U 0))
  have h1 := L2.integrable_inner (𝕜 := ℝ) (coordinate 1 (V 1)) (coordinate 1 (U 1))
  exact (integral_add h0 h1).trans
    ((congrArg₂ (fun x y : ℝ => x+y) (L2.inner_def _ _).symm (L2.inner_def _ _).symm).trans
      (IBMObservableClockKernel.coordinate_inner V U).symm)

theorem bounded_times_integrable (v : JointL2)
    (hv : MemLp (v : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (q : IBMSourceLaws.JointSample → ℝ) (hq : Integrable q IBMSourceLaws.jointMeasure) :
    Integrable (fun ω => v ω * q ω) IBMSourceLaws.jointMeasure :=
  memLp_one_iff_integrable.mp (mul_memLp (r := 1) hv (memLp_one_iff_integrable.mpr hq))

theorem pairing_integral (V U : JointFieldSpace) (v : JointL2)
    (hv : MemLp (v : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    (∫ ω, v ω * pairingFunction V U ω ∂IBMSourceLaws.jointMeasure) =
      inner ℝ (multiply v hv U) V := by
  rw [IBMObservableClockKernel.coordinate_inner]
  simp only [multiply_channel,channel_coordinate]
  exact sum_integral (coordinate 0 (V 0)) (coordinate 1 (V 1))
    (coordinate 0 (U 0)) (coordinate 1 (U 1)) v hv

theorem triple_pairing (z q a b : JointL2)
    (hq : q =ᵐ[IBMSourceLaws.jointMeasure] fun ω => a ω * b ω) :
    inner ℝ z q = ∫ ω, b ω * (a ω * z ω) ∂IBMSourceLaws.jointMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hq] with ω hω
  rw [hω,Real.inner_apply]
  ring

theorem weighted_sub_integral (v : JointL2)
    (hv : MemLp (v : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (a b : IBMSourceLaws.JointSample → ℝ)
    (ha : Integrable a IBMSourceLaws.jointMeasure) (hb : Integrable b IBMSourceLaws.jointMeasure) :
    (∫ ω, v ω * (a ω-b ω) ∂IBMSourceLaws.jointMeasure) =
      (∫ ω, v ω * a ω ∂IBMSourceLaws.jointMeasure) -
      ∫ ω, v ω * b ω ∂IBMSourceLaws.jointMeasure := by
  simp_rw [mul_sub]
  exact integral_sub (bounded_times_integrable v hv a ha) (bounded_times_integrable v hv b hb)

def weakDensity (g : jointDerivative.domain) (u : jointDivergence.domain)
    (ω : IBMSourceLaws.JointSample) : ℝ :=
  (((g : IntrinsicSpace) : JointL2) ω) * ((jointDivergence u : IntrinsicSpace) : JointL2) ω -
    pairingFunction (jointDerivative g) u ω

theorem weakDensity_integrable (g : jointDerivative.domain) (u : jointDivergence.domain) :
    Integrable (weakDensity g u) IBMSourceLaws.jointMeasure :=
  (product_integrable ((g : IntrinsicSpace) : JointL2)
    ((jointDivergence u : IntrinsicSpace) : JointL2)).sub (pairing_integrable (jointDerivative g) u)

theorem weakDensity_mean_zero (g : jointDerivative.domain) (u : jointDivergence.domain) :
    (∫ ω, weakDensity g u ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  have he := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense u g
  have hp := (product_mean ((g : IntrinsicSpace) : JointL2)
    ((jointDivergence u : IntrinsicSpace) : JointL2)).trans (real_inner_comm _ _)
  have hq := (pairing_mean (jointDerivative g) u).trans (real_inner_comm _ _)
  have hs := integral_sub (product_integrable ((g : IntrinsicSpace) : JointL2)
    ((jointDivergence u : IntrinsicSpace) : JointL2)) (pairing_integrable (jointDerivative g) u)
  change (∫ ω, weakDensity g u ω ∂IBMSourceLaws.jointMeasure) = _ at hs
  have he' : inner ℝ ((jointDivergence u : IntrinsicSpace) : JointL2)
      ((g : IntrinsicSpace) : JointL2) = inner ℝ (u : JointFieldSpace) (jointDerivative g) := he
  linarith

theorem weak_pairing (g v : jointDerivative.domain) (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ B)
    (hv : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((v : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (u : jointDivergence.domain) :
    inner ℝ (multiply ((g : IntrinsicSpace) : JointL2) (bounded_memLp g B hg) u)
      (jointDerivative v) =
      ∫ ω, (((v : IntrinsicSpace) : JointL2) ω) * weakDensity g u ω
        ∂IBMSourceLaws.jointMeasure := by
  obtain ⟨q,hq,he⟩ := weak_divergence g v B C hB hC hg hv u
  have hl := triple_pairing ((jointDivergence u : IntrinsicSpace) : JointL2)
    ((q : IntrinsicSpace) : JointL2) ((g : IntrinsicSpace) : JointL2)
    ((v : IntrinsicSpace) : JointL2) hq
  have hr := pairing_integral (jointDerivative g) u ((v : IntrinsicSpace) : JointL2)
    (bounded_memLp v C hv)
  have hs := weighted_sub_integral ((v : IntrinsicSpace) : JointL2) (bounded_memLp v C hv)
    (fun ω => (((g : IntrinsicSpace) : JointL2) ω) *
      ((jointDivergence u : IntrinsicSpace) : JointL2) ω)
    (pairingFunction (jointDerivative g) u)
    (product_integrable _ _) (pairing_integrable _ _)
  change (∫ ω, (((v : IntrinsicSpace) : JointL2) ω) * weakDensity g u ω
    ∂IBMSourceLaws.jointMeasure) = _ at hs
  have he' : inner ℝ (jointDivergence u) (q : IntrinsicSpace) =
      inner ℝ (multiply ((g : IntrinsicSpace) : JointL2) (bounded_memLp g B hg) u)
        (jointDerivative v) +
      inner ℝ (multiply ((v : IntrinsicSpace) : JointL2) (bounded_memLp v C hv) u)
        (jointDerivative g) := he
  have hl' : inner ℝ (jointDivergence u) (q : IntrinsicSpace) = _ := hl
  linarith

end OperatorDerivativeRewrite.Foundation.IBMNativeWeakL1Divergence
