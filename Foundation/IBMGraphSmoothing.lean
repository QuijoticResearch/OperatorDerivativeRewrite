import Foundation.IBMUniformSmoothing

/-! Uniform convergence of the actual full closed IBM scenery derivative graphs. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
open IBMMollifier InfiniteGaussian FractionalSpectralKernel
open SeparableHilbertEmbedding GaussianHilbertProcess GaussianBrownianSobolevField
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

def concreteCoefficient (n : ℕ) (x : ℝ) : CoefficientSpace :=
  kernelCoefficient (x - (bump n).rOut) (x + (bump n).rOut) x (kernel n)

def sourceCoefficient (x : ℝ) : CoefficientSpace :=
  hilbertEmbedding SpectralSpace (IBMFiniteScenerySmoothing.direction x)

theorem concreteCoefficient_error_norm (n : ℕ) (x : ℝ) :
    ‖concreteCoefficient n x - sourceCoefficient x‖ =
      ‖wholeLineScenery (kernel n) x - sourceScenery x‖ := by
  rw [wholeLineScenery_eq_kernelScenery
    (x - (bump n).rOut) (x + (bump n).rOut) x (kernel n)
    (concreteMollifier_support n x), kernelScenery_eq_embedding]
  unfold concreteCoefficient sourceCoefficient kernelCoefficient sourceScenery
  rw [← (hilbertEmbedding SpectralSpace).map_sub,
    (hilbertEmbedding SpectralSpace).norm_map,
    ← (isonormalEmbedding SpectralSpace).map_sub,
    (isonormalEmbedding SpectralSpace).norm_map]

theorem concreteCoefficient_uniform_norm_le (n : ℕ) (x : ℝ) :
    ‖concreteCoefficient n x - sourceCoefficient x‖ ≤
      Real.sqrt (bump n).rOut := by
  rw [concreteCoefficient_error_norm]
  exact concreteMollifier_uniform_norm_le n x

theorem concreteCoefficient_tendstoUniformly :
    TendstoUniformly (fun n x => concreteCoefficient n x)
      sourceCoefficient atTop := by
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (bump n).rOut)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp bump_outer_tendsto_zero
  refine Metric.tendstoUniformly_iff.2 ?_
  intro ε hε
  filter_upwards [hroot.eventually (eventually_lt_nhds hε)] with n hn x
  have hb := concreteCoefficient_uniform_norm_le n x
  simpa only [dist_eq_norm, norm_sub_rev] using lt_of_le_of_lt hb hn

def concreteDerivative (n : ℕ) (x : ℝ) : GaussianVectorL2 :=
  Lp.const 2 gaussianProduct (concreteCoefficient n x)

def sourceDerivative (x : ℝ) : GaussianVectorL2 :=
  Lp.const 2 gaussianProduct (sourceCoefficient x)

theorem concreteDerivative_error_norm (n : ℕ) (x : ℝ) :
    ‖concreteDerivative n x - sourceDerivative x‖ =
      ‖concreteCoefficient n x - sourceCoefficient x‖ := by
  change ‖(Lp.constL 2 gaussianProduct ℝ : CoefficientSpace →L[ℝ] GaussianVectorL2)
    (concreteCoefficient n x) -
    (Lp.constL 2 gaussianProduct ℝ : CoefficientSpace →L[ℝ] GaussianVectorL2)
    (sourceCoefficient x)‖ = _
  rw [← map_sub]
  change ‖Lp.const 2 gaussianProduct
    (concreteCoefficient n x - sourceCoefficient x)‖ = _
  rw [Lp.norm_const' 2 gaussianProduct
    (concreteCoefficient n x - sourceCoefficient x) (by norm_num) (by norm_num)]
  simp

theorem concreteDerivative_uniform_norm_le (n : ℕ) (x : ℝ) :
    ‖concreteDerivative n x - sourceDerivative x‖ ≤
      Real.sqrt (bump n).rOut := by
  rw [concreteDerivative_error_norm]
  exact concreteCoefficient_uniform_norm_le n x

theorem concreteDerivative_tendstoUniformly :
    TendstoUniformly (fun n x => concreteDerivative n x)
      sourceDerivative atTop := by
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (bump n).rOut)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp bump_outer_tendsto_zero
  refine Metric.tendstoUniformly_iff.2 ?_
  intro ε hε
  filter_upwards [hroot.eventually (eventually_lt_nhds hε)] with n hn x
  have hb := concreteDerivative_uniform_norm_le n x
  simpa only [dist_eq_norm, norm_sub_rev] using lt_of_le_of_lt hb hn

def concreteGraph (n : ℕ) (x : ℝ) : GaussianL2 × GaussianVectorL2 :=
  (wholeLineScenery (kernel n) x, concreteDerivative n x)

theorem concreteGraph_mem (n : ℕ) (x : ℝ) :
    concreteGraph n x ∈ closedCylindricalDerivative.graph := by
  exact wholeLineScenery_closedDerivative_graph
    (x - (bump n).rOut) (x + (bump n).rOut) x (kernel n)
    (concreteMollifier_support n x)

theorem concreteGraph_error_norm (n : ℕ) (x : ℝ) :
    ‖concreteGraph n x - sourceGraph x‖ =
      ‖wholeLineScenery (kernel n) x - sourceScenery x‖ := by
  simp only [concreteGraph, sourceGraph, Prod.mk_sub_mk, Prod.norm_mk]
  change max ‖wholeLineScenery (kernel n) x - sourceScenery x‖
    ‖concreteDerivative n x - sourceDerivative x‖ = _
  rw [concreteDerivative_error_norm, concreteCoefficient_error_norm]
  exact max_self _

theorem concreteGraph_uniform_norm_le (n : ℕ) (x : ℝ) :
    ‖concreteGraph n x - sourceGraph x‖ ≤
      Real.sqrt (bump n).rOut := by
  rw [concreteGraph_error_norm]
  exact concreteMollifier_uniform_norm_le n x

theorem concreteGraph_tendstoUniformly :
    TendstoUniformly (fun n x => concreteGraph n x) sourceGraph atTop := by
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (bump n).rOut)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp bump_outer_tendsto_zero
  refine Metric.tendstoUniformly_iff.2 ?_
  intro ε hε
  filter_upwards [hroot.eventually (eventually_lt_nhds hε)] with n hn x
  have hb := concreteGraph_uniform_norm_le n x
  simpa only [dist_eq_norm, norm_sub_rev] using lt_of_le_of_lt hb hn

end OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
