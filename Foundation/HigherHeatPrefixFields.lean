import Foundation.HigherHeatCubicChannelLimit

/-! Time-prefix fields in the existing genuine L1 signed-dual field space. -/
noncomputable section
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPrefixFields
open MeasureTheory Set HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields
open HigherHeatPairedDualCausality HigherHeatDyadicTimeDensity

def segment (s t : ℝ) (a : Dual) : Field timeMeasure :=
  step timeMeasure (Ioc s t) measurableSet_Ioc (measure_ne_top _ _) a

theorem interval_measure (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    timeMeasure.real (Ioc s t) = t-s := by
  have hsub : Ioc s t ⊆ Icc (0:ℝ) 1 := fun _ hu => ⟨hs.trans hu.1.le, hu.2.trans ht⟩
  have he : timeMeasure (Ioc s t) = volume (Ioc s t) := by
    rw [timeMeasure, Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr hsub]
  rw [measureReal_def, he, ← measureReal_def, Real.volume_real_Ioc_of_le hst]

theorem segment_norm (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) (a : Dual) :
    ‖segment s t a‖ = ‖a‖*(t-s) := by
  rw [segment, step_norm, interval_measure s t hs hst ht]

theorem segment_sub (s t : ℝ) (a b : Dual) :
    segment s t a - segment s t b = segment s t (a-b) := by
  exact indicatorConstLp_sub (p := 1) (μ := timeMeasure)
    (hs := measurableSet_Ioc) (hμs := measure_ne_top _ _)

theorem prefix_split (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (a : Dual) :
    segment 0 t a = segment 0 s a + segment s t a := by
  have h := indicatorConstLp_disjoint_union (p := 1) (μ := timeMeasure)
    (measurableSet_Ioc (a := (0:ℝ)) (b := s)) (measurableSet_Ioc (a := s) (b := t))
    (measure_ne_top _ _) (measure_ne_top _ _)
    (Ioc_disjoint_Ioc_of_le (a := (0:ℝ)) (b := s) (c := s) (d := t) le_rfl) a
  simpa only [Ioc_union_Ioc_eq_Ioc hs hst, segment, HigherHeatWeakStepFields.step] using h

theorem prefix_difference (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (a b : Dual) :
    segment 0 t a - segment 0 s b = segment 0 s (a-b) + segment s t a := by
  rw [prefix_split s t hs hst, ← segment_sub]
  abel

theorem prefix_difference_bound (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
    (a b : Dual) :
    ‖segment 0 t a - segment 0 s b‖ ≤ ‖a-b‖*s + ‖a‖*(t-s) := by
  rw [prefix_difference s t hs hst]
  exact (norm_add_le _ _).trans_eq (by
    rw [segment_norm 0 s le_rfl hs (hst.trans ht), segment_norm s t hs hst ht, sub_zero])

theorem prefix_lipschitz (f : Interval → Dual) (C B : ℝ≥0)
    (hf : LipschitzWith C f) (hB : ∀ t, ‖f t‖ ≤ (B : ℝ)) :
    LipschitzWith (C+B) (fun t : Interval => segment 0 (t:ℝ) (f t)) := by
  have ho (s t : Interval) (hst : (s:ℝ) ≤ t) :
      dist (segment 0 (t:ℝ) (f t)) (segment 0 (s:ℝ) (f s)) ≤
        ((C+B:ℝ≥0):ℝ)*dist t s := by
    have hdn : ‖f t-f s‖ ≤ (C:ℝ)*((t:ℝ)-s) := by
      simpa only [dist_eq_norm, Subtype.dist_eq, Real.dist_eq, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hst)] using hf.dist_le_mul t s
    have hh := mul_le_mul_of_nonneg_left s.property.2
      (mul_nonneg C.coe_nonneg (sub_nonneg.mpr hst))
    calc
      _ = ‖segment 0 (t:ℝ) (f t)-segment 0 (s:ℝ) (f s)‖ := dist_eq_norm _ _
      _ ≤ ‖f t-f s‖*(s:ℝ) + ‖f t‖*((t:ℝ)-s) :=
        prefix_difference_bound s t s.property.1 hst t.property.2 (f t) (f s)
      _ ≤ ((C:ℝ)*((t:ℝ)-s))*(s:ℝ) + (B:ℝ)*((t:ℝ)-s) :=
        add_le_add (mul_le_mul_of_nonneg_right hdn s.property.1)
          (mul_le_mul_of_nonneg_right (hB t) (sub_nonneg.mpr hst))
      _ ≤ ((C:ℝ)+(B:ℝ))*((t:ℝ)-s) := by nlinarith
      _ = _ := by rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst)]; rfl
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rcases le_total (s:ℝ) (t:ℝ) with h | h
  · simpa only [dist_comm] using ho s t h
  · exact ho t s h

end OperatorDerivativeRewrite.Foundation.HigherHeatPrefixFields
