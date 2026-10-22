import Foundation.IBMIntrinsicCorrectionField

/-! The ORIGINAL intrinsic IBM domain is stable under bounded coefficients
with bounded native derivatives, even when the second domain factor is unbounded. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicDomainMultiplier
open InfiniteGaussian (CoefficientSpace)
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicGraphDual
open IBMNativeFieldMultiplier IBMNativeProductOperators IBMIntrinsicWeakLeibniz
open IBMIntrinsicDualMultiplier IBMIntrinsicCorrectionField
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative

variable (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
  (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
  (hDf : ∀ i : Fin 2, MemLp (coordinate i (jointDerivative f i) :
    IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)

def productGradient (g : jointDerivative.domain) : JointFieldSpace :=
  multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) (jointDerivative g) +
    correctionField (jointDerivative f) hDf ((g : IntrinsicSpace) : JointL2)

include hC hf hDf

theorem productGradient_embedded (g : jointDerivative.domain) :
    embed (productGradient f C hf hDf g) =
      weakDerivative (scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf)
        (g : IntrinsicSpace)) := by
  have hm : dualMultiplier f C hC hf hDf (weakDerivative (g : IntrinsicSpace)) =
      embed (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) (jointDerivative g)) :=
    (congrArg (dualMultiplier f C hC hf hDf) (original_graph g).symm).trans
      (dualMultiplier_embed f C hC hf hDf (jointDerivative g))
  exact (embed.map_add _ _).trans
    ((congrArg₂ (fun x y : StrongDual ℝ Tests => x+y) hm
      (correctionFunctional_embed f C hC hf hDf (g : IntrinsicSpace))).symm.trans
        (full_dual_leibniz f C hC hf hDf (g : IntrinsicSpace)).symm)

theorem product_mem_domain (g : jointDerivative.domain) :
    scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf) (g : IntrinsicSpace) ∈
      jointDerivative.domain :=
  (representable_iff_domain _).mp
    ⟨productGradient f C hf hDf g, productGradient_embedded f C hC hf hDf g⟩

def productElement (g : jointDerivative.domain) : jointDerivative.domain :=
  ⟨scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf) (g : IntrinsicSpace),
    product_mem_domain f C hC hf hDf g⟩

theorem productElement_actual_ae (g : jointDerivative.domain) :
    (((productElement f C hC hf hDf g : jointDerivative.domain) : IntrinsicSpace) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        (((f : IntrinsicSpace) : JointL2) ω) * (((g : IntrinsicSpace) : JointL2) ω) :=
  scalarMultiplier_actual_ae _ _ _

theorem productElement_gradient (g : jointDerivative.domain) :
    jointDerivative (productElement f C hC hf hDf g) = productGradient f C hf hDf g := by
  apply embed_injective
  exact (original_graph _).trans (productGradient_embedded f C hC hf hDf g).symm

theorem productElement_gradient_ae (g : jointDerivative.domain) (i : Fin 2) :
    coordinate i (jointDerivative (productElement f C hC hf hDf g) i)
      =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        (((f : IntrinsicSpace) : JointL2) ω) • coordinate i (jointDerivative g i) ω +
        (((g : IntrinsicSpace) : JointL2) ω) • coordinate i (jointDerivative f i) ω := by
  have he : coordinate i (jointDerivative (productElement f C hC hf hDf g) i) =
      coordinate i (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf)
        (jointDerivative g) i) +
      coordinate i (correctionField (jointDerivative f) hDf ((g : IntrinsicSpace) : JointL2) i) :=
    (congrArg (fun W : JointFieldSpace => coordinate i (W i))
      (productElement_gradient f C hC hf hDf g)).trans ((coordinate i).map_add _ _)
  have heAE : coordinate i (jointDerivative (productElement f C hC hf hDf g) i)
      =ᵐ[IBMSourceLaws.jointMeasure]
        (show IBMIntrinsicChainRule.JointVectorL2 from
          coordinate i (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf)
            (jointDerivative g) i) +
          coordinate i (correctionField (jointDerivative f) hDf ((g : IntrinsicSpace) : JointL2) i)) :=
    Filter.Eventually.of_forall fun ω =>
      congrArg (fun z : IBMIntrinsicChainRule.JointVectorL2 => z ω) he
  exact heAE.trans ((Lp.coeFn_add _ _).trans
    ((multiply_ae _ _ _ i).add (correctionField_ae _ _ _ i)))

theorem productElement_gradient_norm (g : jointDerivative.domain) :
    ‖jointDerivative (productElement f C hC hf hDf g)‖ ≤
      ‖multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf)‖ * ‖jointDerivative g‖ +
      ‖correctionField (jointDerivative f) hDf‖ * ‖(g : IntrinsicSpace)‖ := by
  rw [productElement_gradient]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.le_opNorm _ _)
    (ContinuousLinearMap.le_opNorm _ _))

theorem productElement_graph_limit (g : jointDerivative.domain) (u : ℕ → jointDerivative.domain)
    (hu : Tendsto (fun n => (u n : IntrinsicSpace)) atTop (𝓝 (g : IntrinsicSpace)))
    (hDu : Tendsto (fun n => jointDerivative (u n)) atTop (𝓝 (jointDerivative g))) :
    Tendsto (fun n => (productElement f C hC hf hDf (u n) : IntrinsicSpace)) atTop
      (𝓝 (productElement f C hC hf hDf g : IntrinsicSpace)) ∧
    Tendsto (fun n => jointDerivative (productElement f C hC hf hDf (u n))) atTop
      (𝓝 (jointDerivative (productElement f C hC hf hDf g))) := by
  constructor
  · exact (scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf)).continuous.tendsto _ |>.comp hu
  · have hv : Tendsto (fun n => ((u n : IntrinsicSpace) : JointL2)) atTop
        (𝓝 ((g : IntrinsicSpace) : JointL2)) :=
      IntrinsicSpace.subtypeL.continuous.tendsto _ |>.comp hu
    have hm := (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf)).continuous.tendsto _ |>.comp hDu
    have hc := (correctionField (jointDerivative f) hDf).continuous.tendsto _ |>.comp hv
    simpa only [productElement_gradient, productGradient, Function.comp_def] using hm.add hc

theorem product_stochastic_IBP (g : jointDerivative.domain) (v : jointDivergence.domain) :
    inner ℝ (productGradient f C hf hDf g) v =
      ∫ ω, (((f : IntrinsicSpace) : JointL2) ω) * (((g : IntrinsicSpace) : JointL2) ω) *
        ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂IBMSourceLaws.jointMeasure := by
  exact (congrArg (fun F : StrongDual ℝ Tests => F (testOf v))
    (productGradient_embedded f C hC hf hDf g)).trans
      (actual_pairing _ _ (productElement_actual_ae f C hC hf hDf g) v)

theorem product_stochastic_integrable (g : jointDerivative.domain) (v : jointDivergence.domain) :
    Integrable (fun ω => (((f : IntrinsicSpace) : JointL2) ω) * (((g : IntrinsicSpace) : JointL2) ω) *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω) IBMSourceLaws.jointMeasure :=
  actual_pairing_integrable _ _ (productElement_actual_ae f C hC hf hDf g) v

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicDomainMultiplier
