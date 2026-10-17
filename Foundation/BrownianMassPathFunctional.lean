import Foundation.BrownianMassContinuousLimit
import Foundation.BrownianRandomMassClock
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! The already constructed actual local mass admits a Borel realization as
an entire continuous-path functional of Brownian motion, modulo one null set. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianMassPathFunctional
open InfiniteGaussian IBMConstructedSources BrownianSmoothMassPath
open BrownianMassContinuousLimit BrownianMassFastSubsequence
open SmoothAbsoluteApproximation RealSteklovApprox
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

@[instance_reducible] def pathSigma : MeasurableSpace SampleSpace :=
  MeasurableSpace.comap clockPath inferInstance

theorem pathSigma_le : pathSigma ≤ (inferInstance : MeasurableSpace SampleSpace) :=
  clockPath_measurable.comap_le

theorem approximation_measurable (n : ℕ) :
    Measurable[pathSigma] (BrownianSmoothMassPath.path n) := by
  letI : MeasurableSpace SampleSpace := pathSigma
  apply ContinuousMap.measurable_iff_eval.mpr
  intro T
  have hB : Measurable clockPath := comap_measurable clockPath
  have hr : Measurable (fun z : SampleSpace × ℝ => rate (width n) z.1 z.2) := by
    exact (curvature_continuous (width_pos n)).measurable.comp
      (continuous_eval.measurable.comp
        ((hB.comp measurable_fst).prodMk measurable_snd.real_toNNReal))
  have hi := hr.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 (T : ℝ)))
  change Measurable (fun ω => (1 / 2 : ℝ) * ∫ s in 0..(T : ℝ), rate (width n) ω s)
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact hi.measurable.const_mul (1 / 2 : ℝ)

theorem limit_raw_measurable :
    AEStronglyMeasurable[pathSigma] limitPath gaussianProduct := by
  refine ⟨fun ω => limUnder atTop (fun j => BrownianSmoothMassPath.path (subsequence j) ω),?_,?_⟩
  · letI : MeasurableSpace SampleSpace := pathSigma
    exact StronglyMeasurable.limUnder
      (fun j => (approximation_measurable (subsequence j)).stronglyMeasurable)
  · filter_upwards [limitPath_tendsto] with ω hω
    exact hω.limUnder_eq.symm

theorem exists_path_functional : ∃ F : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ),
    Measurable F ∧ limitPath =ᵐ[gaussianProduct] (fun ω => F (clockPath ω)) := by
  obtain ⟨g,hg,he⟩ := limit_raw_measurable
  obtain ⟨F,hF,hgF⟩ := hg.exists_eq_measurable_comp
  exact ⟨F,hF.measurable,by simpa only [hgF,Function.comp_def] using he⟩

def functional : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := Classical.choose exists_path_functional

theorem functional_measurable : Measurable functional :=
  (Classical.choose_spec exists_path_functional).1

theorem functional_agrees : ∀ᵐ ω ∂gaussianProduct,
    functional (clockPath ω) = limitPath ω :=
  (Classical.choose_spec exists_path_functional).2.symm

theorem mass_agrees : ∀ᵐ ω ∂gaussianProduct, ∀ t : ℝ≥0,
    BrownianRandomMassClock.mass ω t = (functional (clockPath ω) t).toNNReal := by
  filter_upwards [functional_agrees,BrownianRandomMassClock.mass_agrees] with ω hf hm t
  rw [hf,← hm t,Real.toNNReal_coe]

end OperatorDerivativeRewrite.Foundation.BrownianMassPathFunctional
