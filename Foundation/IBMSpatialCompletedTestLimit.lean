import Foundation.IBMSpatialLipschitzTestLimit

/-! Completed supremum-norm spatial test domain. Extended finite operators
still act on actual bounded continuous representatives and converge in clock L1. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialCompletedTestLimit
open InfiniteGaussian IBMSpatialBoundedTestOperator IBMSpatialLipschitzTestLimit

/-- Use the norm-induced uniformity explicitly so downstream instance search
shares the completion structure with its normed-group instances. -/
abbrev Completed := @UniformSpace.Completion Core
  (inferInstance : SeminormedAddCommGroup Core).toUniformSpace

def inclusion : Core →ₗᵢ[ℝ] Tests where
  toLinearMap := lipschitzTests.subtype
  norm_map' := fun _ => rfl

def realize : Completed →ₗᵢ[ℝ] Tests := inclusion.fromCompletion

theorem realize_coe (F : Core) : realize (F:Completed) = (F:Tests) :=
  LinearIsometry.fromCompletion_apply_coe inclusion F

def finiteOperator (T : ℝ≥0) (N : ℕ) : Completed →L[ℝ] Values :=
  (IBMSpatialLipschitzTestLimit.finiteOperator T N).fromCompletion

def limitOperator (T : ℝ≥0) (hT : 0 < T) : Completed →L[ℝ] Values :=
  (IBMSpatialLipschitzTestLimit.limitOperator T hT).fromCompletion

theorem finite_coe (T : ℝ≥0) (N : ℕ) (F : Core) :
    finiteOperator T N (F:Completed) = IBMSpatialLipschitzTestLimit.finiteOperator T N F :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

theorem limit_coe (T : ℝ≥0) (hT : 0 < T) (F : Core) :
    limitOperator T hT (F:Completed) = IBMSpatialLipschitzTestLimit.limitOperator T hT F :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

theorem finite_actual_operator (T : ℝ≥0) (N : ℕ) (z : Completed) :
    finiteOperator T N z = IBMSpatialBoundedTestOperator.operator T N (realize z) := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq (finiteOperator T N).continuous
      ((IBMSpatialBoundedTestOperator.operator T N).continuous.comp realize.continuous)
  · intro F
    rw [finite_coe,realize_coe]
    rfl

theorem finite_actual (T : ℝ≥0) (N : ℕ) (z : Completed) :
    finiteOperator T N z =ᵐ[gaussianProduct] finiteValue (realize z) T N := by
  rw [finite_actual_operator]
  exact value_actual (realize z) T N

theorem finite_bound (T : ℝ≥0) (N : ℕ) (z : Completed) :
    ‖finiteOperator T N z‖ ≤ (T:ℝ)*‖z‖ := by
  rw [finite_actual_operator]
  have hb := value_norm_bound (realize z) T N
  rwa [realize.norm_map] at hb

theorem limit_bound (T : ℝ≥0) (hT : 0 < T) (z : Completed) :
    ‖limitOperator T hT z‖ ≤ (T:ℝ)*‖z‖ := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_le (limitOperator T hT).continuous.norm (continuous_const.mul continuous_norm)
  · intro F
    rw [limit_coe,UniformSpace.Completion.norm_coe]
    exact limitValue_norm T hT F

theorem completed_tendsto (T : ℝ≥0) (hT : 0 < T) (z : Completed) :
    Tendsto (fun N => finiteOperator T N z) atTop (𝓝 (limitOperator T hT z)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hδ : 0 < ε/(3*((T:ℝ)+1)) := by positivity
  obtain ⟨F,hF⟩ := (UniformSpace.Completion.denseRange_coe :
    DenseRange (fun F : Core => (F:Completed))).exists_dist_lt z hδ
  have hd : ‖z-(F:Completed)‖ < ε/(3*((T:ℝ)+1)) := by simpa only [dist_eq_norm] using hF
  have hs : (T:ℝ)*‖z-(F:Completed)‖ < ε/3 := by
    have hh := (lt_div_iff₀ (show 0 < 3*((T:ℝ)+1) by positivity)).mp hd
    nlinarith [norm_nonneg (z-(F:Completed))]
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (core_tendsto T hT F) (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hc : ‖finiteOperator T n (F:Completed)-limitOperator T hT (F:Completed)‖ < ε/3 := by
    simpa only [finite_coe,limit_coe,IBMSpatialLipschitzTestLimit.limit_apply,dist_eq_norm] using hN n hn
  have ha := finite_bound T n (z-(F:Completed))
  have hb := limit_bound T hT ((F:Completed)-z)
  rw [norm_sub_rev (F:Completed) z] at hb
  have he : finiteOperator T n z-limitOperator T hT z =
      finiteOperator T n (z-(F:Completed))+
        (finiteOperator T n (F:Completed)-limitOperator T hT (F:Completed))+
          limitOperator T hT ((F:Completed)-z) := by
    simp only [map_sub]
    abel
  rw [dist_eq_norm,he]
  have ht := norm_add_le (finiteOperator T n (z-(F:Completed))+
    (finiteOperator T n (F:Completed)-limitOperator T hT (F:Completed)))
      (limitOperator T hT ((F:Completed)-z))
  have ht' := norm_add_le (finiteOperator T n (z-(F:Completed)))
    (finiteOperator T n (F:Completed)-limitOperator T hT (F:Completed))
  linarith

end OperatorDerivativeRewrite.Foundation.IBMSpatialCompletedTestLimit
