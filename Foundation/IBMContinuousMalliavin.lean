import Foundation.IBMWholeLineSmoothing
import Foundation.GaussianPastFirstChaos

/-! Full closed source derivative of continuous Gaussian scenery convolutions. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
open InfiniteGaussian FractionalSpectralKernel GaussianHilbertProcess
open SeparableHilbertEmbedding GaussianPastFirstChaos GaussianBrownianSobolevField
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

def kernelCoefficient (a b x : ℝ) (ρ : ℝ → ℝ) : CoefficientSpace :=
  hilbertEmbedding SpectralSpace (kernelDirection a b x ρ)

/-- The deterministic Malliavin coefficient is itself the Bochner integral
of the original scenery directions in the ambient Gaussian Hilbert space. -/
theorem kernelCoefficient_eq_integral (a b x : ℝ) (ρ : ℝ → ℝ) :
    kernelCoefficient a b x ρ =
      ∫ r in Set.Icc a b,
        ρ (x - r) • hilbertEmbedding SpectralSpace (IBMFiniteScenerySmoothing.direction r) := by
  unfold kernelCoefficient kernelDirection
  have h := (hilbertEmbedding SpectralSpace).integral_comp_comm
    (μ := volume.restrict (Set.Icc a b))
    (fun r : ℝ => ρ (x - r) • IBMFiniteScenerySmoothing.direction r)
  simpa only [map_smul] using h.symm

/-- The complete first-chaos range of the Brownian scenery Hilbert space
lies in the full closed source derivative graph, with constant gradient. -/
theorem sourceDirection_closedDerivative_graph (v : SpectralSpace) :
    (isonormalEmbedding SpectralSpace v,
      Lp.const 2 gaussianProduct (hilbertEmbedding SpectralSpace v)) ∈
        closedCylindricalDerivative.graph := by
  let h := hilbertEmbedding SpectralSpace v
  have hp := projection_closedDerivative_graph (firstChaosEmbedding h)
  have hproj : projection (firstChaosEmbedding h) = firstChaosEmbedding h := by
    unfold projection
    have he := congrArg (fun L : CoefficientSpace →L[ℝ] CoefficientSpace => L h)
      firstChaosEmbedding.adjoint_comp_self
    change firstChaosEmbedding.toContinuousLinearMap.adjoint (firstChaosEmbedding h) = h at he
    change firstChaosEmbedding
      (firstChaosEmbedding.toContinuousLinearMap.adjoint (firstChaosEmbedding h)) =
        firstChaosEmbedding h
    rw [he]
  rw [hproj, firstChaosGradient_apply] at hp
  simpa [isonormalEmbedding, h] using hp

/-- The actual full closed source Malliavin derivative of the continuous
Bochner scenery convolution is its deterministic Hilbert coefficient. -/
theorem kernelScenery_closedDerivative_graph (a b x : ℝ) (ρ : ℝ → ℝ) :
    (kernelScenery a b x ρ,
      Lp.const 2 gaussianProduct (kernelCoefficient a b x ρ)) ∈
        closedCylindricalDerivative.graph := by
  rw [kernelScenery_eq_embedding]
  exact sourceDirection_closedDerivative_graph (kernelDirection a b x ρ)

/-- Under explicit shifted support, the whole-line Gaussian L² convolution
lies in the full closed source derivative graph with the integrated kernel. -/
theorem wholeLineScenery_closedDerivative_graph (a b x : ℝ) (ρ : ℝ → ℝ)
    (hsupp : ∀ r, r ∉ Set.Icc a b → ρ (x - r) = 0) :
    (wholeLineScenery ρ x,
      Lp.const 2 gaussianProduct (kernelCoefficient a b x ρ)) ∈
        closedCylindricalDerivative.graph := by
  rw [wholeLineScenery_eq_kernelScenery a b x ρ hsupp]
  exact kernelScenery_closedDerivative_graph a b x ρ

theorem wholeLineScenery_derivative_domain (a b x : ℝ) (ρ : ℝ → ℝ)
    (hsupp : ∀ r, r ∉ Set.Icc a b → ρ (x - r) = 0) :
    wholeLineScenery ρ x ∈ closedCylindricalDerivative.domain :=
  LinearPMap.mem_domain_iff.mpr
    ⟨_, wholeLineScenery_closedDerivative_graph a b x ρ hsupp⟩

theorem wholeLineScenery_derivative_apply (a b x : ℝ) (ρ : ℝ → ℝ)
    (hsupp : ∀ r, r ∉ Set.Icc a b → ρ (x - r) = 0)
    (hdom : wholeLineScenery ρ x ∈ closedCylindricalDerivative.domain) :
    closedCylindricalDerivative ⟨wholeLineScenery ρ x, hdom⟩ =
      Lp.const 2 gaussianProduct (kernelCoefficient a b x ρ) :=
  closedCylindricalDerivative.mem_graph_snd_inj
    (closedCylindricalDerivative.mem_graph ⟨wholeLineScenery ρ x, hdom⟩)
    (wholeLineScenery_closedDerivative_graph a b x ρ hsupp) rfl

def sourceGraph (r : ℝ) : GaussianL2 × GaussianVectorL2 :=
  (sourceScenery r,
    Lp.const 2 gaussianProduct
      (hilbertEmbedding SpectralSpace (IBMFiniteScenerySmoothing.direction r)))

theorem sourceGraph_mem_derivative_graph (r : ℝ) :
    sourceGraph r ∈ closedCylindricalDerivative.graph := by
  change (isonormalEmbedding SpectralSpace (IBMFiniteScenerySmoothing.direction r),
      Lp.const 2 gaussianProduct
        (hilbertEmbedding SpectralSpace (IBMFiniteScenerySmoothing.direction r))) ∈
      closedCylindricalDerivative.graph
  exact sourceDirection_closedDerivative_graph _

theorem sourceGraph_continuous : Continuous sourceGraph := by
  have hcoeff : Continuous (fun r : ℝ =>
      hilbertEmbedding SpectralSpace (IBMFiniteScenerySmoothing.direction r)) :=
    (hilbertEmbedding SpectralSpace).continuous.comp direction_continuous
  exact sourceScenery_continuous.prodMk
    ((Lp.constL 2 gaussianProduct ℝ).continuous.comp hcoeff)

theorem weightedSourceGraph_integrableOn (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    IntegrableOn (fun r : ℝ => ρ (x - r) • sourceGraph r) (Set.Icc a b) volume :=
  ((hρ.comp (continuous_const.sub continuous_id)).smul sourceGraph_continuous).integrableOn_Icc

/-- Graph-norm Bochner integration of the source first-chaos graph produces
exactly the convolution and its full closed Malliavin derivative. -/
theorem integral_weighted_sourceGraph (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    (∫ r in Set.Icc a b, ρ (x - r) • sourceGraph r) =
      (kernelScenery a b x ρ,
        Lp.const 2 gaussianProduct (kernelCoefficient a b x ρ)) := by
  have hcoeff : IntegrableOn (fun r : ℝ => ρ (x - r) •
      hilbertEmbedding SpectralSpace (IBMFiniteScenerySmoothing.direction r))
      (Set.Icc a b) volume := by
    have hc : Continuous (fun r : ℝ => ρ (x - r) •
        hilbertEmbedding SpectralSpace (IBMFiniteScenerySmoothing.direction r)) := by
      exact (hρ.comp (continuous_const.sub continuous_id)).smul
        ((hilbertEmbedding SpectralSpace).continuous.comp direction_continuous)
    exact hc.integrableOn_Icc
  have hvector : IntegrableOn (fun r : ℝ => ρ (x - r) •
      Lp.const 2 gaussianProduct
        (hilbertEmbedding SpectralSpace (IBMFiniteScenerySmoothing.direction r)))
      (Set.Icc a b) volume := by
    have hc : Continuous (fun r : ℝ => ρ (x - r) •
        Lp.const 2 gaussianProduct
          (hilbertEmbedding SpectralSpace (IBMFiniteScenerySmoothing.direction r))) := by
      exact (hρ.comp (continuous_const.sub continuous_id)).smul
        ((Lp.constL 2 gaussianProduct ℝ).continuous.comp
          ((hilbertEmbedding SpectralSpace).continuous.comp direction_continuous))
    exact hc.integrableOn_Icc
  have hpair := integral_pair (weightedScenery_integrableOn a b x hρ) hvector
  have hconst := (Lp.constL 2 gaussianProduct ℝ).integral_comp_comm
    (μ := volume.restrict (Set.Icc a b)) hcoeff
  simp only [sourceGraph, Prod.smul_mk] at hpair ⊢
  rw [hpair]
  congr 1
  rw [kernelCoefficient_eq_integral]
  simpa only [Lp.constL_apply, map_smul] using hconst

theorem weightedSourceGraph_integral_mem_derivative_graph
    (a b x : ℝ) {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    (∫ r in Set.Icc a b, ρ (x - r) • sourceGraph r) ∈
      closedCylindricalDerivative.graph := by
  rw [integral_weighted_sourceGraph a b x hρ]
  exact kernelScenery_closedDerivative_graph a b x ρ

end OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
