import Foundation.BrownianClockMeasureTransport
import Foundation.BrownianZeroOccupation

/-! Physical-time zero occupation of the actual Brownian mass time change.
This is a pathwise measure result, not a transition-kernel or flow assertion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianStickyOccupation
open InfiniteGaussian IBMConstructedSources BrownianMassStieltjesSupport
open BrownianRandomMassClock BrownianMassRandomTimeChange BrownianClockMeasureTransport

theorem ordinaryTime_cut (E : Set ℝ≥0) (hE : MeasurableSet E) (T : ℝ≥0) :
    ordinaryTime (E ∩ Iic T) =
      ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))) (Real.toNNReal ⁻¹' E) := by
  rw [ordinaryTime, Measure.map_apply continuous_real_toNNReal.measurable
    (hE.inter measurableSet_Iic),
    Measure.restrict_apply ((hE.inter measurableSet_Iic).preimage
      continuous_real_toNNReal.measurable),
    Measure.restrict_apply (hE.preimage continuous_real_toNNReal.measurable)]
  congr 1
  rw [preimage_inter, inter_assoc, positive_preimage_Iic]

theorem brownian_zero_ordinary : ∀ᵐ ω ∂gaussianProduct,
    ordinaryTime {s : ℝ≥0 | clockPath ω s = 0} = 0 := by
  filter_upwards [BrownianZeroOccupation.zero_set_measure] with ω hω
  let Z : Set ℝ≥0 := {s | clockPath ω s = 0}
  have hZ : MeasurableSet Z :=
    isClosed_eq (clockPath ω).continuous continuous_const |>.measurableSet
  have hn (n : ℕ) : ordinaryTime (Z ∩ Iic (n : ℝ≥0)) = 0 := by
    rw [ordinaryTime_cut Z hZ]
    exact hω n
  have hsub : Z ⊆ ⋃ n : ℕ, Z ∩ Iic (n : ℝ≥0) := by
    intro s hs
    obtain ⟨n, hn⟩ := exists_nat_gt (s : ℝ)
    exact mem_iUnion.mpr ⟨n, hs, by exact_mod_cast hn.le⟩
  exact measure_mono_null hsub (measure_iUnion_null hn)

theorem zero_occupation : ∀ᵐ ω ∂gaussianProduct, ∀ κ T : ℝ≥0,
    ordinaryTime ({t : ℝ≥0 | changedPath κ ω t = 0} ∩ Iic T) =
      (κ : ℝ≥0∞) * (mass ω (inverse κ ω T) : ℝ≥0∞) := by
  filter_upwards [brownian_zero_ordinary, concentrated_on_zeros] with ω ho hm κ T
  let Z : Set ℝ≥0 := {s | clockPath ω s = 0}
  let E : Set ℝ≥0 := {t | changedPath κ ω t = 0} ∩ Iic T
  have hE : MeasurableSet E :=
    (isClosed_eq (changedPath κ ω).continuous continuous_const).measurableSet.inter
      measurableSet_Iic
  have hp : forward κ ω ⁻¹' E = Z ∩ Iic (inverse κ ω T) := by
    change forward κ ω ⁻¹' ({t | changedPath κ ω t = 0} ∩ Iic T) = _
    rw [preimage_inter, forward_preimage_Iic]
    congr 1
    ext s
    simp only [mem_preimage, mem_ofPred_eq, recover_original, Z]
  have hmass : massMeasure ω (Z ∩ Iic (inverse κ ω T)) =
      massMeasure ω (Iic (inverse κ ω T)) := by
    rw [inter_comm]
    apply measure_inter_conull
    exact hm
  have hord : ordinaryTime (Z ∩ Iic (inverse κ ω T)) = 0 :=
    measure_mono_null inter_subset_left ho
  have h := congrArg (fun μ : Measure ℝ≥0 => μ E) (forward_map_clockMeasure κ ω)
  rw [Measure.map_apply (forward_continuous κ ω).measurable hE, hp,
    clockMeasure, Measure.add_apply, Measure.smul_apply, hord, zero_add,
    hmass, massMeasure_Iic, smul_eq_mul] at h
  exact h.symm

theorem zero_occupation_gap : ∀ᵐ ω ∂gaussianProduct, ∀ κ T : ℝ≥0,
    ordinaryTime ({t : ℝ≥0 | changedPath κ ω t = 0} ∩ Iic T) =
      ENNReal.ofReal ((T : ℝ) - inverse κ ω T) := by
  filter_upwards [zero_occupation] with ω hω κ T
  rw [hω]
  have hb := inverse_balance κ ω T
  have he : (T : ℝ) - inverse κ ω T = (κ : ℝ) * mass ω (inverse κ ω T) := by
    linarith
  rw [he, ← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul]

theorem zero_occupation_real : ∀ᵐ ω ∂gaussianProduct, ∀ κ T : ℝ≥0,
    ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)))
      {t : ℝ | changedPath κ ω t.toNNReal = 0} =
      ENNReal.ofReal ((T : ℝ) - inverse κ ω T) := by
  filter_upwards [zero_occupation_gap] with ω hω κ T
  have h := ordinaryTime_cut {t : ℝ≥0 | changedPath κ ω t = 0}
    (isClosed_eq (changedPath κ ω).continuous continuous_const).measurableSet T
  exact h.symm.trans (hω κ T)

end OperatorDerivativeRewrite.Foundation.BrownianStickyOccupation
