import Foundation.IBMActualMixedEnergyObstruction
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-! Full predictable measure identities and covariance total-variation control. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCovarianceVariationControl
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableRingContent
open IBMJointPredictableEnergyMeasure IBMPredictableCovarianceMeasure
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
local instance (F : JointL2) : IsFiniteMeasure (predictableMeasure F) := finite_measure F

def cover : ℕ → Set Space
  | 0 => origin univ
  | n+1 => rect 0 ((n+1 : ℕ) : ℝ≥0) univ

theorem cover_mem (n : ℕ) : cover n ∈ generators := by
  cases n with
  | zero => exact Or.inr ⟨univ, MeasurableSet.univ, rfl⟩
  | succ n => exact Or.inl (subset_supClosure (rect_mem 0 _ univ MeasurableSet.univ))

theorem cover_union : (⋃ n, cover n) = univ := by
  apply eq_univ_of_forall
  rintro ⟨r, ω⟩
  by_cases hz : r = 0
  · exact mem_iUnion.mpr ⟨0, ⟨hz, mem_univ ω⟩⟩
  · obtain ⟨n, hn⟩ := exists_nat_ge r
    exact mem_iUnion.mpr ⟨n+1, ⟨⟨pos_iff_ne_zero.mpr hz,
      hn.trans (by exact_mod_cast Nat.le_succ n)⟩, mem_univ ω⟩⟩

theorem predictable_measure_ext (μ ν : Measure Space) [IsFiniteMeasure μ]
    (h : ∀ E ∈ generators, μ E = ν E) : μ = ν :=
  Measure.ext_of_generateFrom_of_iUnion generators cover predictable_generation.symm
    (fun E hE H hH _ => generators_inter hE hH) cover_union cover_mem
    (fun _ => measure_ne_top _ _) h

theorem parallelogram (F G : JointL2) :
    predictableMeasure (F+G) + predictableMeasure (F-G) =
      (2 : ℝ≥0∞) • (predictableMeasure F + predictableMeasure G) := by
  apply predictable_measure_ext
  intro E hE
  rcases hE with hE | ⟨A, hA, rfl⟩
  · rw [Measure.add_apply, Measure.smul_apply, Measure.add_apply,
      predictableMeasure_generator (F+G) (Or.inl hE),
      predictableMeasure_generator (F-G) (Or.inl hE),
      predictableMeasure_generator F (Or.inl hE),
      predictableMeasure_generator G (Or.inl hE),
      content_energy (F+G) hE, content_energy (F-G) hE,
      content_energy F hE, content_energy G hE,
      ring_terminal_add, ring_terminal_sub]
    change ENNReal.ofReal (‖ringIntegral F E + ringIntegral G E‖^2) +
      ENNReal.ofReal (‖ringIntegral F E - ringIntegral G E‖^2) =
        2 * (ENNReal.ofReal (‖ringIntegral F E‖^2) + ENNReal.ofReal (‖ringIntegral G E‖^2))
    have hs : ‖ringIntegral F E + ringIntegral G E‖^2 +
        ‖ringIntegral F E - ringIntegral G E‖^2 =
          2*(‖ringIntegral F E‖^2+‖ringIntegral G E‖^2) := by
      rw [norm_add_sq_real, norm_sub_sq_real]
      ring
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), hs,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    norm_num
  · change (predictableMeasure (F+G) + predictableMeasure (F-G)) (origin A) =
      ((2 : ℝ≥0∞) • (predictableMeasure F + predictableMeasure G)) (origin A)
    simp only [Measure.add_apply, Measure.smul_apply,
      predictableMeasure_origin (F+G) A hA, predictableMeasure_origin (F-G) A hA,
      predictableMeasure_origin F A hA, predictableMeasure_origin G A hA,
      zero_add, smul_zero]

theorem homogeneity (c : ℝ) (F : JointL2) :
    predictableMeasure (c • F) = ENNReal.ofReal (c^2) • predictableMeasure F := by
  apply predictable_measure_ext
  intro E hE
  rcases hE with hE | ⟨A, hA, rfl⟩
  · have he : ringIntegral (c • F) E = c • ringIntegral F E :=
      (ringOperator_eq E _).symm.trans (((ringOperator E).map_smul c F).trans
        (congrArg (fun z : JointL2 => c • z) (ringOperator_eq E F)))
    rw [Measure.smul_apply, predictableMeasure_generator _ (Or.inl hE),
      predictableMeasure_generator F (Or.inl hE), content_energy _ hE, content_energy F hE,
      he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact ENNReal.ofReal_mul (sq_nonneg c)
  · change predictableMeasure (c • F) (origin A) =
      (ENNReal.ofReal (c^2) • predictableMeasure F) (origin A)
    simp only [Measure.smul_apply, predictableMeasure_origin (c • F) A hA,
      predictableMeasure_origin F A hA, smul_zero]

theorem measure_zero : predictableMeasure (0 : JointL2) = 0 := by
  simpa only [zero_smul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero] using
    homogeneity 0 (0 : JointL2)

theorem covariance_diagonal (F : JointL2) :
    covariance F F = (predictableMeasure F).toSignedMeasure := by
  ext E hE
  rw [covariance_apply F F hE, show F+F = (2 : ℝ) • F by module,
    sub_self, measure_zero, homogeneity, Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul, Measure.toSignedMeasure_apply_measurable hE]
  norm_num [measureReal_def]
  ring

theorem variation_bound (F G : JointL2) :
    (covariance F G).variation ≤ (1/2 : ℝ≥0∞) • (predictableMeasure F + predictableMeasure G) := by
  rw [covariance, VectorMeasure.variation_smul]
  grw [VectorMeasure.variation_sub_le]
  simp only [Measure.variation_toSignedMeasure, parallelogram]
  have hn : ‖(1/4 : ℝ)‖₊ = (1/4 : ℝ≥0) := by norm_num
  have hq : ((1/4 : ℝ≥0) : ℝ≥0∞) * 2 = (1/2 : ℝ≥0∞) := by
    calc
      _ = (((1/4 : ℝ≥0) * 2 : ℝ≥0) : ℝ≥0∞) := by
        simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
      _ = ((1/2 : ℝ≥0) : ℝ≥0∞) :=
        congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (by norm_num)
      _ = _ := by rw [ENNReal.coe_div (by norm_num)]; rfl
  rw [hn, ← Measure.coe_nnreal_smul, smul_smul]
  exact le_of_eq (congrArg (fun c : ℝ≥0∞ => c • (predictableMeasure F + predictableMeasure G)) hq)

theorem finite_variation (F G : JointL2) : IsFiniteMeasure (covariance F G).variation := by
  constructor
  apply lt_of_le_of_lt ((Measure.le_iff.mp (variation_bound F G)) univ MeasurableSet.univ)
  simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  finiteness

end OperatorDerivativeRewrite.Foundation.IBMCovarianceVariationControl
