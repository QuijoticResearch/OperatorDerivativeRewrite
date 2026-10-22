import Foundation.IBMNativeWeightedDivergence

/-! The actual total-contraction L2 domain, without separate bounded gradients. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeContractionDomain
open InfiniteGaussian (CoefficientSpace)
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMNativeFieldMultiplier
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

def pairingFunction (V u : JointFieldSpace) (ω : IBMSourceLaws.JointSample) : ℝ :=
  inner ℝ (coordinate 0 (V 0) ω) (coordinate 0 (u 0) ω) +
  inner ℝ (coordinate 1 (V 1) ω) (coordinate 1 (u 1) ω)

def correction (V u : JointFieldSpace)
    (h : MemLp (pairingFunction V u) 2 IBMSourceLaws.jointMeasure) : JointL2 :=
  h.toLp (pairingFunction V u)

theorem correction_ae (V u : JointFieldSpace)
    (h : MemLp (pairingFunction V u) 2 IBMSourceLaws.jointMeasure) :
    correction V u h =ᵐ[IBMSourceLaws.jointMeasure] pairingFunction V u := h.coeFn_toLp

theorem channel_integral (v u : JointVectorL2) (g : JointL2)
    (hg : MemLp (g : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    (∫ ω, g ω * inner ℝ (v ω) (u ω) ∂IBMSourceLaws.jointMeasure) =
      inner ℝ (boundedMultiplier g hg u) v := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMultiplier_coeFn g hg u] with ω hm
  rw [hm,real_inner_smul_left,real_inner_comm (u ω) (v ω)]

theorem channel_integrable (v u : JointVectorL2) (g : JointL2)
    (hg : MemLp (g : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    Integrable (fun ω => g ω * inner ℝ (v ω) (u ω)) IBMSourceLaws.jointMeasure :=
  memLp_one_iff_integrable.mp
    (mul_memLp (r := 1) hg (inner_memLp (r := 1) (Lp.memLp v) (Lp.memLp u)))

theorem sum_integral (v0 v1 u0 u1 : JointVectorL2) (g : JointL2)
    (hg : MemLp (g : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    (∫ ω, g ω * (inner ℝ (v0 ω) (u0 ω) + inner ℝ (v1 ω) (u1 ω))
      ∂IBMSourceLaws.jointMeasure) =
      inner ℝ (boundedMultiplier g hg u0) v0 + inner ℝ (boundedMultiplier g hg u1) v1 := by
  simp_rw [mul_add]
  exact (integral_add (channel_integrable v0 u0 g hg) (channel_integrable v1 u1 g hg)).trans
    (congrArg₂ (fun a b : ℝ => a+b) (channel_integral v0 u0 g hg)
      (channel_integral v1 u1 g hg))

theorem correction_pairing (V u : JointFieldSpace)
    (h : MemLp (pairingFunction V u) 2 IBMSourceLaws.jointMeasure) (g : JointL2)
    (hg : MemLp (g : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    inner ℝ (correction V u h) g = inner ℝ (multiply g hg u) V := by
  have he : inner ℝ (correction V u h) g =
      ∫ ω, g ω * pairingFunction V u ω ∂IBMSourceLaws.jointMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [correction_ae V u h] with ω hc
    rw [hc,Real.inner_apply]
    ring
  have hs := sum_integral (coordinate 0 (V 0)) (coordinate 1 (V 1))
    (coordinate 0 (u 0)) (coordinate 1 (u 1)) g hg
  have h0 := channel_coordinate 0 g hg (u 0)
  have h1 := channel_coordinate 1 g hg (u 1)
  calc
    _ = inner ℝ (boundedMultiplier g hg (coordinate 0 (u 0))) (coordinate 0 (V 0)) +
        inner ℝ (boundedMultiplier g hg (coordinate 1 (u 1))) (coordinate 1 (V 1)) := he.trans hs
    _ = inner ℝ (coordinate 0 (channelMultiplier 0 g hg (u 0))) (coordinate 0 (V 0)) +
        inner ℝ (coordinate 1 (channelMultiplier 1 g hg (u 1))) (coordinate 1 (V 1)) :=
      congrArg₂ (fun a b : ℝ => a+b)
        (congrArg (fun z : JointVectorL2 => inner ℝ z (coordinate 0 (V 0))) h0.symm)
        (congrArg (fun z : JointVectorL2 => inner ℝ z (coordinate 1 (V 1))) h1.symm)
    _ = inner ℝ (channelMultiplier 0 g hg (u 0)) (V 0) +
        inner ℝ (channelMultiplier 1 g hg (u 1)) (V 1) :=
      congrArg₂ (fun a b : ℝ => a+b) ((coordinate 0).inner_map_map _ _)
        ((coordinate 1).inner_map_map _ _)
    _ = _ := by simp only [PiLp.inner_apply,Fin.sum_univ_two,multiply_channel]

theorem bounded_field_domain (V u : JointFieldSpace)
    (hu : ∀ i : Fin 2, MemLp (coordinate i (u i) :
      IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure) :
    MemLp (pairingFunction V u) 2 IBMSourceLaws.jointMeasure :=
  (inner_memLp (Lp.memLp (coordinate 0 (V 0))) (hu 0)).add
    (inner_memLp (Lp.memLp (coordinate 1 (V 1))) (hu 1))

theorem four_four_domain (V u : JointFieldSpace)
    (hV : ∀ i : Fin 2, MemLp (coordinate i (V i) :
      IBMSourceLaws.JointSample → CoefficientSpace) 4 IBMSourceLaws.jointMeasure)
    (hu : ∀ i : Fin 2, MemLp (coordinate i (u i) :
      IBMSourceLaws.JointSample → CoefficientSpace) 4 IBMSourceLaws.jointMeasure) :
    MemLp (pairingFunction V u) 2 IBMSourceLaws.jointMeasure :=
  (inner_memLp (hV 0) (hu 0)).add (inner_memLp (hV 1) (hu 1))

end OperatorDerivativeRewrite.Foundation.IBMNativeContractionDomain
