import Foundation.IBMRandomTimeHilbert
import Foundation.IBMConstructedSources
import Foundation.BochnerClosedOperator

/-! The actual unmollified IBM coordinate has a square-integrable partial
scenery derivative. This is not a joint clock derivative or intrinsic-core
density theorem. The original closed derivative is used in each scenery fiber. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMUnmollifiedSourceDerivative
open InfiniteGaussian IBMRandomTimeHilbert IBMContinuousScenery
open GaussianBrownianSobolevField GaussianPastFirstChaos GaussianHilbertProcess
open SeparableHilbertEmbedding FractionalSpectralKernel
attribute [local instance] spectralSpace_secondCountable

theorem source_gradient_graph (r : ℝ) :
    (sourceScenery r, firstChaosGradient (sourceScenery r)) ∈
      closedCylindricalDerivative.graph := by
  have h := sourceDirection_closedDerivative_graph (IBMFiniteScenerySmoothing.direction r)
  change (firstChaosEmbedding (hilbertEmbedding SpectralSpace
      (IBMFiniteScenerySmoothing.direction r)),
    firstChaosGradient (firstChaosEmbedding (hilbertEmbedding SpectralSpace
      (IBMFiniteScenerySmoothing.direction r)))) ∈ _
  rw [firstChaosGradient_apply]
  exact h

theorem source_gradient_norm (r : ℝ) :
    ‖firstChaosGradient (sourceScenery r)‖ = ‖sourceScenery r‖ := by
  exact firstChaosGradient_norm _

/-- The partial scenery gradient is a genuine Bochner-L² clock field. -/
def gradient (t : ℝ≥0) : Lp GaussianVectorL2 2 gaussianProduct :=
  firstChaosGradient.compLp (randomSourceL2 t)

theorem gradient_ae (t : ℝ≥0) :
    gradient t =ᵐ[gaussianProduct] fun ω =>
      Lp.const 2 gaussianProduct
        (hilbertEmbedding SpectralSpace
          (IBMFiniteScenerySmoothing.direction |GaussianTimeProcess.process t ω|)) := by
  filter_upwards [firstChaosGradient.coeFn_compLp (randomSourceL2 t),
    (randomSourceClass_memLp t).coeFn_toLp] with ω hg hu
  change gradient t ω = _ at hg
  change randomSourceL2 t ω = randomSourceClass t ω at hu
  rw [hg, hu]
  exact firstChaosGradient_apply _

/-- No mollification or derivative-domain assumption is imposed on IBM. -/
theorem randomSource_graph (t : ℝ≥0) :
    (randomSourceL2 t, gradient t) ∈
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  filter_upwards [firstChaosGradient.coeFn_compLp (randomSourceL2 t),
    (randomSourceClass_memLp t).coeFn_toLp] with ω hg hu
  change gradient t ω = firstChaosGradient (randomSourceL2 t ω) at hg
  change randomSourceL2 t ω = randomSourceClass t ω at hu
  rw [hg, hu]
  exact source_gradient_graph _

theorem randomSource_domain (t : ℝ≥0) :
    randomSourceL2 t ∈
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).domain :=
  LinearPMap.mem_domain_iff.mpr ⟨gradient t, randomSource_graph t⟩

/-- The norm identity is on actual clock/scenery Bochner classes. -/
theorem gradient_norm (t : ℝ≥0) : ‖gradient t‖ = ‖randomSourceL2 t‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [firstChaosGradient.coeFn_compLp (randomSourceL2 t),
    (randomSourceClass_memLp t).coeFn_toLp] with ω hg hu
  change ‖gradient t ω‖ = ‖randomSourceL2 t ω‖
  change gradient t ω = firstChaosGradient (randomSourceL2 t ω) at hg
  change randomSourceL2 t ω = randomSourceClass t ω at hu
  rw [hg, hu]
  exact source_gradient_norm _

def mollifiedGradient (n : ℕ) (t : ℝ≥0) : Lp GaussianVectorL2 2 gaussianProduct :=
  firstChaosGradient.compLp (randomMollifiedL2 n t)

theorem randomMollified_graph (n : ℕ) (t : ℝ≥0) :
    (randomMollifiedL2 n t, mollifiedGradient n t) ∈
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  filter_upwards [firstChaosGradient.coeFn_compLp (randomMollifiedL2 n t),
    (randomMollifiedClass_memLp n t).coeFn_toLp] with ω hg hu
  change mollifiedGradient n t ω = firstChaosGradient (randomMollifiedL2 n t ω) at hg
  change randomMollifiedL2 n t ω = randomMollifiedClass n t ω at hu
  rw [hg, hu]
  change (wholeLineScenery (IBMMollifier.kernel n) _,
    firstChaosGradient (wholeLineScenery (IBMMollifier.kernel n) _)) ∈ _
  rw [IBMJointMollifierGaussian.wholeLineScenery_eq_sourceEmbedding]
  change (firstChaosEmbedding (hilbertEmbedding SpectralSpace _),
    firstChaosGradient (firstChaosEmbedding (hilbertEmbedding SpectralSpace _))) ∈ _
  rw [firstChaosGradient_apply]
  exact sourceDirection_closedDerivative_graph _

/-- Both coordinates of the genuine partial-derivative graph converge in
Bochner L². This is stronger than convergence of the observable alone. -/
theorem graph_tendsto (t : ℝ≥0) :
    Tendsto (fun n => (randomMollifiedL2 n t, mollifiedGradient n t)) atTop
      (𝓝 (randomSourceL2 t, gradient t)) := by
  have hu := randomMollifiedL2_tendsto t
  have hv := (firstChaosGradient.compLpL 2 gaussianProduct).continuous.tendsto
    (randomSourceL2 t) |>.comp hu
  exact hu.prodMk_nhds hv

/-- The constructed continuous-path IBM sections represent the same
unmollified source classes almost everywhere in the clock variable. -/
theorem actual_section_ae (t : ℝ≥0) : ∀ᵐ ωY ∂gaussianProduct,
    (fun ωX => IBMConstructedSources.ibmValue t (ωX, ωY)) =ᵐ[gaussianProduct]
      randomSourceClass t ωY := by
  filter_upwards [IBMConstructedSources.clockPath_coordinate_ae t] with ωY hy
  filter_upwards [IBMConstructedSources.sceneryPath_coordinate_ae
    |GaussianTimeProcess.process t ωY|] with ωX hx
  change IBMConstructedSources.sceneryPath ωX
    |IBMConstructedSources.clockPath ωY t| = _
  rw [hy, hx]
  rfl

/-- Thus almost every actual unmollified IBM section is scenery-Sobolev.
This says nothing about membership in the intersection with the clock domain. -/
theorem actual_section_domain (t : ℝ≥0) : ∀ᵐ ωY ∂gaussianProduct,
    ∃ h : MemLp (fun ωX => IBMConstructedSources.ibmValue t (ωX, ωY)) 2 gaussianProduct,
      h.toLp _ ∈ closedCylindricalDerivative.domain := by
  filter_upwards [actual_section_ae t] with ωY hy
  have hm := (Lp.memLp (randomSourceClass t ωY)).ae_eq hy.symm
  refine ⟨hm, ?_⟩
  have he : hm.toLp _ = randomSourceClass t ωY := by
    apply Lp.ext
    exact hm.coeFn_toLp.trans hy
  rw [he]
  exact LinearPMap.mem_domain_iff.mpr ⟨_, source_gradient_graph _⟩

end OperatorDerivativeRewrite.Foundation.IBMUnmollifiedSourceDerivative
