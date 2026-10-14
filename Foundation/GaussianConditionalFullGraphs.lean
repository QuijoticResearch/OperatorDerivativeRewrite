import Foundation.GaussianJointRecoveryIntertwining

/-! Joint observed projection intertwines both actual full closed source graphs. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianConditionalFullGraphs
open InfiniteGaussian GaussianNumberSectors GaussianConditionalGraph GaussianSourceHodge
open GaussianDivergenceRecovery GaussianQuadraticSourceHodge GaussianJointSourceProjection
open GaussianJointRecoveryIntertwining

theorem projectedGradient_eq_number_recovery (n : ℕ) (f : GaussianL2) :
    projectedGradient n f=(n : ℝ) • recovery (projection n f) := by
  have hr := recovery_divergence_gradientProjection _ _ (projectedGradient_graph n f).2
  change recovery ((n : ℝ) • projection n f)=gradientProjection (projectedGradient n f) at hr
  have hm : projectedGradient n f∈gradientRange :=
    (mem_gradientRange_iff _).mpr ⟨projection n f,(projectedGradient_graph n f).1⟩
  have he : gradientProjection (projectedGradient n f)=projectedGradient n f :=
    gradientRange.starProjection_eq_self_iff.mpr hm
  rw [he,recovery_smul] at hr
  exact hr.symm

theorem projectedGradient_joint_commute {I : Type*} (h : I → CoefficientSpace) (n : ℕ) (f : GaussianL2) :
    jointConditional h (projectedGradient n f)=projectedGradient n (conditionalProjection h f) := by
  rw [projectedGradient_eq_number_recovery,map_smul,joint_recovery_conditional,
    ← projection_conditional_commute,← projectedGradient_eq_number_recovery]

theorem conditional_derivative_graph {I : Type*} (h : I → CoefficientSpace)
    {f : GaussianL2} {g : GaussianVectorL2} (hg : (f,g)∈closedCylindricalDerivative.graph) :
    (conditionalProjection h f,jointConditional h g)∈closedCylindricalDerivative.graph := by
  have hs := (jointConditional h).hasSum (projectedGradient_hasSum hg)
  change HasSum (fun n => jointConditional h (projectedGradient n f)) (jointConditional h g) at hs
  simp only [projectedGradient_joint_commute] at hs
  exact closedCylindricalDerivative_isClosed.mem_of_tendsto
    ((projection_hasSum (conditionalProjection h f)).prodMk_nhds hs)
    (Eventually.of_forall (finite_projection_graph (conditionalProjection h f)))

theorem conditional_divergence_graph {I : Type*} (h : I → CoefficientSpace)
    {v : GaussianVectorL2} {f : GaussianL2} (hg : (v,f)∈hilbertDivergence.graph) :
    (jointConditional h v,conditionalProjection h f)∈hilbertDivergence.graph := by
  change (jointConditional h v,conditionalProjection h f)∈closedCylindricalDerivative.adjoint.graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint closedCylindricalDerivative_dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro a b hab
  have hi := GaussianNumberSectors.graph_duality (conditional_derivative_graph h hab) hg
  rw [jointConditional_inner] at hi
  have hc := (generated h).inner_starProjection_left_eq_right a f
  change inner ℝ (conditionalProjection h a) f=inner ℝ a (conditionalProjection h f) at hc
  change inner ℝ b (jointConditional h v)-inner ℝ a (conditionalProjection h f)=0
  rw [← hc,← hi,sub_self]

theorem joint_preserves_gradientRange {I : Type*} (h : I → CoefficientSpace)
    {v : GaussianVectorL2} (hv : v∈gradientRange) : jointConditional h v∈gradientRange := by
  obtain ⟨f,hf⟩ := (mem_gradientRange_iff v).mp hv
  exact (mem_gradientRange_iff _).mpr ⟨conditionalProjection h f,conditional_derivative_graph h hf⟩

theorem joint_gradientProjection_commute {I : Type*} (h : I → CoefficientSpace) (v : GaussianVectorL2) :
    gradientProjection (jointConditional h v)=jointConditional h (gradientProjection v) := by
  apply gradientRange.eq_starProjection_of_mem_of_inner_eq_zero
    (joint_preserves_gradientRange h (gradientProjection_mem v))
  intro w hw
  rw [← map_sub,jointConditional_inner]
  exact gradientRange.starProjection_inner_eq_zero v _ (joint_preserves_gradientRange h hw)

theorem conditional_domain_values {I : Type*} (h : I → CoefficientSpace)
    (f : closedCylindricalDerivative.domain) :
    closedCylindricalDerivative (conditionalDomain h f)=jointConditional h (closedCylindricalDerivative f) := by
  exact closedCylindricalDerivative.mem_graph_snd_inj
    (closedCylindricalDerivative.mem_graph (conditionalDomain h f))
    (conditional_derivative_graph h (closedCylindricalDerivative.mem_graph f)) rfl

end OperatorDerivativeRewrite.Foundation.GaussianConditionalFullGraphs
