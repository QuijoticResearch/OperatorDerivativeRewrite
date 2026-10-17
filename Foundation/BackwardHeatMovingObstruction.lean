import Foundation.MovingPathCharacterMeasurability
import Foundation.FourierPathFutureIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! An actual backward heat character is jointly continuous but not Bochner-measurable in uniform path norm. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.BackwardHeatMovingObstruction
open MovingPathCharacters MovingPathCharacterMeasurability HigherHeatContinuousCylinders
open HigherHeatCylinderFourier

def coefficient (m : ℕ) (t : ℝ) : ℂ := HigherHeatL2.symbol m (1-t.toNNReal) 1

theorem coefficient_continuous (m : ℕ) : Continuous (coefficient m) := by
  unfold coefficient HigherHeatL2.symbol
  fun_prop

theorem coefficient_ne_zero (m : ℕ) (t : ℝ) : coefficient m t ≠ 0 := by
  simp [coefficient, HigherHeatL2.symbol]

def backward (m : ℕ) (t : ℝ) : Path →ᵇ ℂ := coefficient m t • character t

theorem joint_continuous (m : ℕ) : Continuous (fun z : ℝ × Path => backward m z.1 z.2) := by
  change Continuous (fun z : ℝ × Path => coefficient m z.1 * character z.1 z.2)
  exact ((coefficient_continuous m).comp continuous_fst).mul MovingPathCharacters.joint_continuous

theorem current_coordinate (m : ℕ) (t : ℝ) (ω η : Path) (h : ω.val t = η.val t) :
    backward m t ω = backward m t η := by
  change coefficient m t * phase 1 (ω.val t) = coefficient m t * phase 1 (η.val t)
  rw [h]

theorem actual_kernel (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (ω : Path) :
    backward m t ω = ∫ᵛ y, phase 1 (ω.val t + y)
      ∂<•HigherHeatSignedLaws.law m hm (1-t.toNNReal)
        (tsub_pos_iff_lt.mpr (show t.toNNReal < (1 : ℝ≥0) from by
          apply NNReal.coe_lt_coe.mp
          rw [Real.coe_toNNReal _ ht.1.le]
          exact ht.2)) := by
  rw [FourierPathFutureIntegral.shifted_signed_integral]
  change coefficient m t * phase 1 (ω.val t) = phase 1 (ω.val t) * coefficient m t
  ring

theorem not_aestronglyMeasurable (m : ℕ) :
    ¬ AEStronglyMeasurable (backward m) intervalMeasure :=
  nonzero_smul_not_aestronglyMeasurable (coefficient m) (coefficient_continuous m).measurable
    (coefficient_ne_zero m)

theorem no_Lp_representative (m : ℕ) (p : ℝ≥0∞) (f : Lp (Path →ᵇ ℂ) p intervalMeasure) :
    ¬ (backward m =ᵐ[intervalMeasure] (f : ℝ → (Path →ᵇ ℂ))) := by
  intro he
  exact not_aestronglyMeasurable m ((Lp.aestronglyMeasurable f).congr he.symm)

theorem scalar_norm_bound (m : ℕ) (z : ℝ × Path) : ‖backward m z.1 z.2‖ ≤ 1 := by
  change ‖coefficient m z.1 * phase 1 (z.2.val z.1)‖ ≤ 1
  rw [norm_mul, phase_norm, mul_one]
  exact HigherHeatL2.symbol_norm_le _ _ _

theorem scalar_product_memLp (m : ℕ) (p : ℝ≥0∞) (μ : Measure Path) [IsFiniteMeasure μ] :
    MemLp (fun z : ℝ × Path => backward m z.1 z.2) p (intervalMeasure.prod μ) := by
  letI : IsFiniteMeasure intervalMeasure := by unfold intervalMeasure; infer_instance
  have hc : MemLp (fun _ : ℝ × Path => (1 : ℂ)) p (intervalMeasure.prod μ) := memLp_const 1
  apply hc.mono (joint_continuous m).measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by simpa using scalar_norm_bound m z)

end OperatorDerivativeRewrite.Foundation.BackwardHeatMovingObstruction
