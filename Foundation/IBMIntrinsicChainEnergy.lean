import Foundation.IBMIntrinsicChainRule

/-! Original-coordinate chain fields and native energy control for actual IBM observables. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicChainEnergy
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMIntrinsicChainRule
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

def vectorSwap : JointVectorL2 →ₗᵢ[ℝ] JointVectorL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.swap measurePreserving_swap

theorem vectorSwap_ae (g : JointVectorL2) :
    vectorSwap g =ᵐ[IBMSourceLaws.jointMeasure] fun ω => g ω.swap :=
  Lp.coeFn_compMeasurePreserving g measurePreserving_swap

def sourceField (g : FieldSpace) : JointVectorL2 := vectorSwap (uncurryField g)

theorem swap_chain_ae (x : JointL2) (g G : JointVectorL2) (a : ℝ → ℝ)
    (h : G =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      a (ProductL2Curry.swap gaussianProduct gaussianProduct x ω) • g ω) :
    vectorSwap G =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a (x ω) • vectorSwap g ω := by
  have ht := (measurePreserving_swap (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp h
  have hx := (measurePreserving_swap (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct x)
  filter_upwards [vectorSwap_ae G, vectorSwap_ae g, ht,hx]
      with ω hG hg ht hx
  simp only [Function.comp_def] at ht hx
  rw [hG,ht,hx,hg]
  rfl

theorem channel_chain_bound (x : JointL2) (g G : FieldSpace) (a : ℝ → ℝ) (B : ℝ)
    (hB : ∀ z, ‖a z‖ ≤ B)
    (h : uncurryField G =ᵐ[IBMSourceLaws.jointMeasure] fun ω => a (x ω) • uncurryField g ω) :
    ‖G‖ ≤ B * ‖g‖ := by
  rw [← uncurryField_norm G, ← uncurryField_norm g]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [h] with ω hω
  rw [hω,norm_smul]
  exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

theorem joint_norm_sq (g : JointFieldSpace) : ‖g‖ ^ 2 = ‖g 0‖ ^ 2 + ‖g 1‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fin.sum_univ_two]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

theorem joint_chain_bound (f F : jointDerivative.domain) (a : ℝ → ℝ) (B : ℝ)
    (hB : ∀ z, ‖a z‖ ≤ B)
    (hc : uncurryField (jointDerivative F 1) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a (((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 1) ω)
    (hs : uncurryField (jointDerivative F 0) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a (ProductL2Curry.swap gaussianProduct gaussianProduct
        ((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 0) ω) :
    ‖jointDerivative F‖ ≤ B * ‖jointDerivative f‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg (a 0)).trans (hB 0)
  have hcB := channel_chain_bound ((f : IntrinsicSpace) : JointL2)
    (jointDerivative f 1) (jointDerivative F 1) a B hB hc
  have hsB := channel_chain_bound (ProductL2Curry.swap gaussianProduct gaussianProduct
    ((f : IntrinsicSpace) : JointL2)) (jointDerivative f 0) (jointDerivative F 0) a B hB hs
  have h0 : ‖jointDerivative F 0‖ ^ 2 ≤ B ^ 2 * ‖jointDerivative f 0‖ ^ 2 := by
    nlinarith [norm_nonneg (jointDerivative F 0), norm_nonneg (jointDerivative f 0)]
  have h1 : ‖jointDerivative F 1‖ ^ 2 ≤ B ^ 2 * ‖jointDerivative f 1‖ ^ 2 := by
    nlinarith [norm_nonneg (jointDerivative F 1), norm_nonneg (jointDerivative f 1)]
  have hF := joint_norm_sq (jointDerivative F)
  have hf := joint_norm_sq (jointDerivative f)
  nlinarith [norm_nonneg (jointDerivative F), norm_nonneg (jointDerivative f),
    mul_nonneg hB0 (norm_nonneg (jointDerivative f))]

theorem bounded_chain_energy (f : jointDerivative.domain)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : jointDerivative.domain,
      ((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => φ (((f : IntrinsicSpace) : JointL2) ω)) ∧
      uncurryField (jointDerivative F 1) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => dφ (((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 1) ω) ∧
      sourceField (jointDerivative F 0) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => dφ (((f : IntrinsicSpace) : JointL2) ω) • sourceField (jointDerivative f 0) ω) ∧
      ‖jointDerivative F‖ ≤ B * ‖jointDerivative f‖ := by
  obtain ⟨F,hF,hclock,hsource⟩ := bounded_chain f φ dφ hd hc A B hA hB
  exact ⟨F,hF,hclock,swap_chain_ae ((f : IntrinsicSpace) : JointL2)
    (uncurryField (jointDerivative f 0)) (uncurryField (jointDerivative F 0)) dφ hsource,
      joint_chain_bound f F dφ B hB hclock hsource⟩

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicChainEnergy
