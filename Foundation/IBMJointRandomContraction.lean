import Foundation.IBMWeakRandomEvaluation
import Foundation.IBMRawIntegralSourceCalculus

/-! Source-section pairing retains the clock variable in genuine L1. This is
not conditional expectation onto the intrinsic IBM observable sigma algebra. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMJointRandomContraction
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators

def weight (u : ValueSpace) : GaussianL2 :=
  (Lp.memLp u).norm.toLp (fun Y => ‖u Y‖)

theorem weight_actual (u : ValueSpace) :
    weight u =ᵐ[gaussianProduct] fun Y => ‖u Y‖ := MemLp.coeFn_toLp _

theorem weight_norm (u : ValueSpace) : ‖weight u‖ = ‖u‖ := by
  rw [weight,Lp.norm_toLp,eLpNorm_norm _ (Lp.aestronglyMeasurable u)]
  rfl

def sectionFunctional (u : ValueSpace) (Y : SampleSpace) : GaussianL2 →L[ℝ] ℝ := innerSL ℝ (u Y)

theorem section_measurable (u : ValueSpace) (x : GaussianL2) :
    Measurable (fun Y => sectionFunctional u Y x) := by
  have hc : Continuous (fun z : GaussianL2 => inner ℝ z x) :=
    continuous_id.inner continuous_const
  exact (hc.comp_stronglyMeasurable (Lp.stronglyMeasurable u)).measurable

theorem section_bound (u : ValueSpace) : ∀ᵐ Y ∂gaussianProduct, ∀ x : GaussianL2,
    ‖sectionFunctional u Y x‖ ≤ ‖weight u Y‖*‖x‖ := by
  filter_upwards [weight_actual u] with Y hY
  intro x
  rw [hY,norm_norm]
  change ‖inner ℝ (u Y) x‖ ≤ ‖u Y‖*‖x‖
  exact norm_inner_le_norm (u Y) x

def sourceOperator (u : ValueSpace) : ValueSpace →L[ℝ] Lp ℝ 1 gaussianProduct :=
  IBMWeakRandomEvaluation.operator (sectionFunctional u) (section_measurable u)
    (weight u) (section_bound u)

theorem source_actual (u v : ValueSpace) :
    sourceOperator u v =ᵐ[gaussianProduct] fun Y => inner ℝ (u Y) (v Y) :=
  IBMWeakRandomEvaluation.value_actual (sectionFunctional u) (section_measurable u)
    (weight u) (section_bound u) v

theorem source_bound (u v : ValueSpace) : ‖sourceOperator u v‖ ≤ ‖u‖*‖v‖ := by
  change ‖IBMWeakRandomEvaluation.value (sectionFunctional u) (section_measurable u)
    (weight u) (section_bound u) v‖ ≤ _
  simpa only [weight_norm] using IBMWeakRandomEvaluation.value_bound
    (sectionFunctional u) (section_measurable u) (weight u) (section_bound u) v

theorem source_expectation (u v : ValueSpace) :
    L1.integralCLM (sourceOperator u v) = inner ℝ u v := by
  rw [← L1.integral_eq,L1.integral_eq_integral,L2_inner_eq_integral]
  exact integral_congr_ae (source_actual u v)

def jointOperator (u : ValueSpace) : JointL2 →L[ℝ] Lp ℝ 1 gaussianProduct :=
  (sourceOperator u).comp sourceUnitary.toLinearIsometry.toContinuousLinearMap

theorem joint_actual (u : ValueSpace) (q : JointL2) :
    jointOperator u q =ᵐ[gaussianProduct] fun Y => inner ℝ (u Y) (sourceUnitary q Y) :=
  source_actual u (sourceUnitary q)

theorem joint_realization (u v : ValueSpace) :
    jointOperator u (jointRealization v) = sourceOperator u v := by
  change sourceOperator u (sourceUnitary (jointRealization v)) = _
  rw [IBMRawIntegralSourceCalculus.source_curry]

theorem joint_bound (u : ValueSpace) (q : JointL2) :
    ‖jointOperator u q‖ ≤ ‖u‖*‖q‖ := by
  simpa only [jointOperator,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.norm_map] using source_bound u (sourceUnitary q)

theorem joint_expectation (u : ValueSpace) (q : JointL2) :
    L1.integralCLM (jointOperator u q) = inner ℝ (jointRealization u) q := by
  change L1.integralCLM (sourceOperator u (sourceUnitary q)) = _
  rw [source_expectation]
  calc
    inner ℝ u (sourceUnitary q) =
        inner ℝ (sourceUnitary (jointRealization u)) (sourceUnitary q) := by
      rw [IBMRawIntegralSourceCalculus.source_curry]
    _ = _ := sourceUnitary.inner_map_map _ _

end OperatorDerivativeRewrite.Foundation.IBMJointRandomContraction
