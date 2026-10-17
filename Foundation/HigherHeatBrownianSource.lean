import Foundation.HigherHeatGaussianConfigurations
import Foundation.IBMConstructedSources

/-! An actual continuous centered Brownian path source with the heat normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatBrownianSource
open InfiniteGaussian IBMConstructedSources HigherHeatContinuousCylinders
open HigherHeatGaussianConfigurations
attribute [local irreducible] IBMConstructedSources.clockPath

def sourcePath (T : ℝ≥0) (ω : SampleSpace) : Path :=
  ⟨⟨fun t : ℝ => clockPath ω ((2*T)*t.toNNReal)-clockPath ω 0,by
      exact ((clockPath ω).continuous.comp (by fun_prop)).sub continuous_const⟩,by simp⟩

theorem sourcePath_measurable (T : ℝ≥0) : Measurable (sourcePath T) := by
  have hm : Measurable (fun ω : SampleSpace => (sourcePath T ω).val) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact ((ContinuousMap.measurable_eval _).comp clockPath_measurable).sub
      ((ContinuousMap.measurable_eval 0).comp clockPath_measurable)
  exact hm.subtype_mk

def sourceMeasure (T : ℝ≥0) : Measure Path := gaussianProduct.map (sourcePath T)

instance sourceMeasure_probability (T : ℝ≥0) : IsProbabilityMeasure (sourceMeasure T) := by
  unfold sourceMeasure
  infer_instance

theorem sourcePath_hasLaw (T : ℝ≥0) : HasLaw (sourcePath T) (sourceMeasure T) gaussianProduct :=
  ⟨(sourcePath_measurable T).aemeasurable,rfl⟩

def increment (n : ℕ) (s : ℝ≥0) (i : Fin n) (ω : SampleSpace) : ℝ :=
  clockPath ω (((i.val+1 : ℕ) : ℝ≥0)*(2*s))-clockPath ω ((i.val : ℝ≥0)*(2*s))

theorem increment_measurable (n : ℕ) (s : ℝ≥0) (i : Fin n) : Measurable (increment n s i) :=
  ((ContinuousMap.measurable_eval _).comp clockPath_measurable).sub
    ((ContinuousMap.measurable_eval _).comp clockPath_measurable)

theorem step_distance (s : ℝ≥0) (k : ℕ) :
    nndist ((((k+1 : ℕ) : ℝ≥0)*(2*s) : ℝ≥0) : ℝ) (((k : ℝ≥0)*(2*s) : ℝ≥0) : ℝ)=2*s := by
  apply NNReal.eq
  change dist ((((k+1 : ℕ) : ℝ≥0)*(2*s) : ℝ≥0) : ℝ) (((k : ℝ≥0)*(2*s) : ℝ≥0) : ℝ)=(2*s : ℝ≥0)
  rw [Real.dist_eq]
  push_cast
  rw [show ((k : ℝ)+1)*(2*(s : ℝ))-(k : ℝ)*(2*(s : ℝ))=2*(s : ℝ) by ring]
  exact abs_of_nonneg (by positivity)

theorem increment_hasLaw (n : ℕ) (s : ℝ≥0) (i : Fin n) :
    HasLaw (increment n s i) (gaussianReal 0 (2*s)) gaussianProduct := by
  have h := clock_isBrownian.toIsPreBrownianReal.hasLaw_sub
    (((i.val+1 : ℕ) : ℝ≥0)*(2*s)) ((i.val : ℝ≥0)*(2*s))
  change HasLaw (increment n s i)
    (gaussianReal 0 (nndist ((((i.val+1 : ℕ) : ℝ≥0)*(2*s) : ℝ≥0) : ℝ)
      (((i.val : ℝ≥0)*(2*s) : ℝ≥0) : ℝ))) gaussianProduct at h
  rwa [step_distance s i.val] at h

theorem increments_independent (n : ℕ) (s : ℝ≥0) : iIndepFun (increment n s) gaussianProduct := by
  have ht : Monotone (fun i : Fin (n+1) => (i.val : ℝ≥0)*(2*s)) := by
    intro i j hij
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast hij
  have h := clock_isBrownian.toIsPreBrownianReal.hasIndepIncrements n _ ht
  have he : (fun (i : Fin n) (ω : SampleSpace) =>
      clockPath ω ((i.succ.val : ℝ≥0)*(2*s))-clockPath ω ((i.castSucc.val : ℝ≥0)*(2*s))) =
      increment n s := by
    funext i ω
    rfl
  rwa [he] at h

theorem increments_hasLaw (n : ℕ) (s : ℝ≥0) :
    HasLaw (fun ω : SampleSpace => fun i : Fin n => increment n s i ω)
      (gaussianIncrements (fun _ : Fin n => s)) gaussianProduct := by
  refine ⟨(Measurable.of_eval (fun i => increment_measurable n s i)).aemeasurable,?_⟩
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (increment_measurable n s i).aemeasurable)
    (increments_independent n s)]
  unfold gaussianIncrements
  congr 1
  funext i
  exact (increment_hasLaw n s i).map_eq

end OperatorDerivativeRewrite.Foundation.HigherHeatBrownianSource
