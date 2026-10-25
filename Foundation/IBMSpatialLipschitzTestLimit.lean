import Foundation.IBMSpatialBoundedTestOperator

/-! Bounded Lipschitz spatial tests carry the INHERITED supremum norm.
The actual diagonal occupation limit is a bounded linear operator there. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialLipschitzTestLimit
open InfiniteGaussian IBMSpatialBoundedTestOperator IBMSpatialKernelOccupation

def lipschitzTests : Submodule ℝ Tests where
  carrier := {F | ∃ K : ℝ≥0, LipschitzWith K F}
  zero_mem' := ⟨0,LipschitzWith.const 0⟩
  add_mem' := by
    rintro F G ⟨K,hF⟩ ⟨L,hG⟩
    refine ⟨K+L,?_⟩
    change LipschitzWith (K+L) (fun z => F z+G z)
    exact hF.add hG
  smul_mem' := by
    rintro c F ⟨K,hF⟩
    refine ⟨‖c‖₊*K,?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖c*F x-c*F y‖ ≤ (‖c‖₊*K:ℝ≥0)*dist x y
    rw [← mul_sub,norm_mul]
    simpa only [NNReal.coe_mul,coe_nnnorm,mul_assoc,dist_eq_norm] using
      mul_le_mul_of_nonneg_left (hF.norm_sub_le x y) (norm_nonneg c)

abbrev Core := lipschitzTests

def constant (c : ℝ) : Core := ⟨BoundedContinuousFunction.const _ c,0,LipschitzWith.const c⟩

def bound (F : Core) : ℝ≥0 := Classical.choose F.property

theorem bound_lipschitz (F : Core) : LipschitzWith (bound F) (F:Tests) := Classical.choose_spec F.property

def finiteOperator (T : ℝ≥0) (N : ℕ) : Core →L[ℝ] Values :=
  (IBMSpatialBoundedTestOperator.operator T N).comp lipschitzTests.subtypeL

def limitValue (T : ℝ≥0) (F : Core) : Values := occupation (F:Tests) (bound_lipschitz F) T

theorem finite_apply (T : ℝ≥0) (N : ℕ) (F : Core) :
    finiteOperator T N F = value (F:Tests) T N := rfl

theorem core_tendsto (T : ℝ≥0) (hT : 0 < T) (F : Core) :
    Tendsto (fun N => finiteOperator T N F) atTop (𝓝 (limitValue T F)) := by
  have h := action_tendsto (F:Tests) (bound_lipschitz F) ‖(F:Tests)‖ (F:Tests).norm_coe_le_norm T hT
  exact h.congr' (Eventually.of_forall fun N => (value_old_action (F:Tests) (bound_lipschitz F) T N).symm)

theorem limitValue_add (T : ℝ≥0) (hT : 0 < T) (F G : Core) :
    limitValue T (F+G) = limitValue T F+limitValue T G := by
  have h := (core_tendsto T hT F).add (core_tendsto T hT G)
  have h' : Tendsto (fun N => finiteOperator T N (F+G)) atTop
      (𝓝 (limitValue T F+limitValue T G)) := by simpa only [map_add] using h
  exact tendsto_nhds_unique (core_tendsto T hT (F+G)) h'

theorem limitValue_smul (T : ℝ≥0) (hT : 0 < T) (c : ℝ) (F : Core) :
    limitValue T (c • F) = c • limitValue T F := by
  have h := (core_tendsto T hT F).const_smul c
  have h' : Tendsto (fun N => finiteOperator T N (c • F)) atTop
      (𝓝 (c • limitValue T F)) := by simpa only [map_smul] using h
  exact tendsto_nhds_unique (core_tendsto T hT (c • F)) h'

theorem limitValue_norm (T : ℝ≥0) (hT : 0 < T) (F : Core) :
    ‖limitValue T F‖ ≤ (T:ℝ)*‖F‖ := by
  have h := IBMSpatialKernelUniformBound.occupation_norm_bound (F:Tests) (bound_lipschitz F)
    ‖(F:Tests)‖ (F:Tests).norm_coe_le_norm T hT
  change ‖occupation (F:Tests) (bound_lipschitz F) T‖ ≤ (T:ℝ)*‖(F:Tests)‖
  simpa only [mul_comm] using h

def limitOperator (T : ℝ≥0) (hT : 0 < T) : Core →L[ℝ] Values :=
  ({ toFun := limitValue T
     map_add' := limitValue_add T hT
     map_smul' := limitValue_smul T hT } : Core →ₗ[ℝ] Values).mkContinuous
       (T:ℝ) (limitValue_norm T hT)

theorem limit_apply (T : ℝ≥0) (hT : 0 < T) (F : Core) : limitOperator T hT F = limitValue T F := rfl

theorem finite_norm_bound (T : ℝ≥0) (N : ℕ) (F : Core) :
    ‖finiteOperator T N F‖ ≤ (T:ℝ)*‖F‖ := value_norm_bound (F:Tests) T N

theorem limit_norm_bound (T : ℝ≥0) (hT : 0 < T) : ‖limitOperator T hT‖ ≤ (T:ℝ) :=
  (limitOperator T hT).opNorm_le_bound T.coe_nonneg (limitValue_norm T hT)

end OperatorDerivativeRewrite.Foundation.IBMSpatialLipschitzTestLimit
