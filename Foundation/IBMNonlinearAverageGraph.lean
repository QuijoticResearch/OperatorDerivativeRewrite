import Foundation.GaussianClosedChainRule
import Foundation.IBMClockAverageGraph

/-! Bounded nonlinear intrinsic IBM averages in both genuine partial Gaussian
derivative domains, with the native source/clock factor order preserved. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearAverageGraph
open InfiniteGaussian IBMTimeAveragedObservable
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

abbrev JointVectorL2 := Lp CoefficientSpace 2 IBMSourceLaws.jointMeasure

theorem swap_swap (f : JointL2) :
    ProductL2Curry.swap gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct f) = f := by
  apply Lp.ext
  have ha := measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    (ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct f)
  filter_upwards [ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct
    (ProductL2Curry.swap gaussianProduct gaussianProduct f), ha] with ω h1 h2
  exact h1.trans h2

theorem nativeAverage_source_representation (T : ℝ) :
    ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct (nativeAverage T)) = sourceAverage T := by
  change ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
    (ProductL2Curry.swap gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct
        ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm (sourceAverage T)))) = _
  have he := swap_swap
    ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm (sourceAverage T))
  exact (congrArg (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct) he).trans
    (LinearIsometryEquiv.apply_symm_apply _ _)

attribute [local irreducible] nativeAverage sourceAverage IBMConstructedSources.clockPath

/-- The SAME actual bounded nonlinear IBM-observable random variable belongs
to both partial domains. Clock graphs use source-outside/clock-inside sections;
source graphs use clock-outside/source-inside sections. -/
theorem nativeAverage_bounded_chain {T : ℝ} (hT : 0 ≤ T)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : JointL2, ∃ Gclock Gsource : JointVectorL2,
      F ∈ IntrinsicSpace ∧
      (ProductL2Curry.curry gaussianProduct gaussianProduct F,
        ProductL2Curry.curry gaussianProduct gaussianProduct Gclock) ∈
          (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph ∧
      (ProductL2Curry.curry gaussianProduct gaussianProduct
          (ProductL2Curry.swap gaussianProduct gaussianProduct F),
        ProductL2Curry.curry gaussianProduct gaussianProduct Gsource) ∈
          (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph ∧
      F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ (nativeAverage T ω) := by
  classical
  obtain ⟨hclock, _⟩ := IBMClockAverageGraph.nativeAverage_clock_domain hT
  let gc := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
    (IBMClockAverageGraph.clockDerivative ⟨_, hclock⟩)
  have hcg : (ProductL2Curry.curry gaussianProduct gaussianProduct (nativeAverage T),
      ProductL2Curry.curry gaussianProduct gaussianProduct gc) ∈
        (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph := by
    change (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct (nativeAverage T),
      ProductL2Curry.curryEquiv gaussianProduct gaussianProduct gc) ∈ _
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact IBMClockAverageGraph.clockDerivative.mem_graph ⟨_, hclock⟩
  obtain ⟨F, Gclock, hFc, hF, _⟩ := GaussianClosedChainRule.bounded_product_chain_graph
    (nativeAverage T) gc hcg φ dφ hd hc A B hA hB
  let gs := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
    (sourceGradient (sourceAverage T))
  have hsg : (ProductL2Curry.curry gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct (nativeAverage T)),
      ProductL2Curry.curry gaussianProduct gaussianProduct gs) ∈
        (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph := by
    change (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct (nativeAverage T)),
      ProductL2Curry.curryEquiv gaussianProduct gaussianProduct gs) ∈ _
    rw [nativeAverage_source_representation, LinearIsometryEquiv.apply_symm_apply]
    exact sourceAverage_source_graph T
  obtain ⟨Fs, Gsource, hFs, hFsae, _⟩ := GaussianClosedChainRule.bounded_product_chain_graph
    (ProductL2Curry.swap gaussianProduct gaussianProduct (nativeAverage T)) gs hsg
    φ dφ hd hc A B hA hB
  have he : ProductL2Curry.swap gaussianProduct gaussianProduct F = Fs := by
    apply Lp.ext
    have hs := measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hF
    filter_upwards [ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct F,
      ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct (nativeAverage T), hs, hFsae]
      with ω h1 h2 h3 h4
    rw [h1, h4, h2]
    exact h3
  have hobs : AEStronglyMeasurable[IBMConditionalObservable.observableSigma
      IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath]
      (nativeAverage T) IBMSourceLaws.jointMeasure :=
    mem_lpMeas_iff_aestronglyMeasurable.mp (nativeAverage_intrinsic T)
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  refine ⟨F, Gclock, Gsource, ?_, hFc, ?_, hF⟩
  · exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      ((hφ.comp_aestronglyMeasurable hobs).congr hF.symm)
  · rwa [he]

end OperatorDerivativeRewrite.Foundation.IBMNonlinearAverageGraph
