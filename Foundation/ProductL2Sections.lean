import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Actual L2 sections of a strongly measurable product field. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ProductL2Sections

private theorem measurable_of_dist {X Y : Type*} [MeasurableSpace X]
    [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : ∀ y, Measurable (fun x => dist (f x) y)) : Measurable f := by
  have hb : IsTopologicalBasis {s : Set Y | ∃ y r, s = Metric.ball y r} := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨y, r, rfl⟩
      exact Metric.isOpen_ball
    · intro y s hs hopen
      obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hs)
      exact ⟨Metric.ball y r, ⟨y, r, rfl⟩, Metric.mem_ball_self hr, hrs⟩
  rw [‹BorelSpace Y›.measurable_eq, hb.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro s ⟨y, r, rfl⟩
  exact measurableSet_lt (hf y) measurable_const

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] (ν : Measure Y) [SFinite ν]

theorem measurable_section_eLpNorm (f : X × Y → E) (hf : StronglyMeasurable f) :
    Measurable (fun x => eLpNorm (fun y => f (x, y)) 2 ν) := by
  have he (x : X) := eLpNorm_eq_lintegral_rpow_enorm_toReal
    (f := fun y => f (x, y)) (p := (2 : ℝ≥0∞)) (by simp) (by simp)
    ((hf.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (μ := ν))
  simp_rw [he]
  exact ((hf.enorm.pow_const (2 : ℝ≥0∞).toReal).lintegral_prod_right').pow_const _

open Classical in
def sectionL2 (f : X × Y → E) (x : X) : Lp E 2 ν :=
  if h : MemLp (fun y => f (x, y)) 2 ν then h.toLp _ else 0

omit [MeasurableSpace X] [SFinite ν] in
theorem sectionL2_coeFn (f : X × Y → E) (x : X)
    (h : MemLp (fun y => f (x, y)) 2 ν) :
    sectionL2 ν f x =ᵐ[ν] fun y => f (x, y) := by
  classical
  rw [sectionL2, dite_eq_left h]
  exact MemLp.coeFn_toLp h

theorem sectionL2_stronglyMeasurable [SecondCountableTopology (Lp E 2 ν)]
    (f : X × Y → E) (hf : StronglyMeasurable f) : StronglyMeasurable (sectionL2 ν f) := by
  classical
  let : MeasurableSpace (Lp E 2 ν) := borel (Lp E 2 ν)
  let : BorelSpace (Lp E 2 ν) := ⟨rfl⟩
  apply Measurable.stronglyMeasurable
  apply measurable_of_dist
  intro v
  have hm := measurable_section_eLpNorm ν f hf
  have hgood : MeasurableSet {x | MemLp (fun y => f (x, y)) 2 ν} :=
    measurableSet_lt hm measurable_const
  have hd := measurable_section_eLpNorm ν
    (fun z => f z - v z.2)
    (hf.sub ((Lp.stronglyMeasurable v).comp_measurable measurable_snd))
  have he : (fun x => dist (sectionL2 ν f x) v) =
      fun x => if MemLp (fun y => f (x, y)) 2 ν then
        (eLpNorm (fun y => f (x, y) - v y) 2 ν).toReal else ‖v‖ := by
    funext x
    by_cases h : MemLp (fun y => f (x, y)) 2 ν
    · simp only [sectionL2, dite_eq_left h, ite_eq_left h, dist_eq_norm, Lp.norm_def]
      congr 1
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub (h.toLp _) v, MemLp.coeFn_toLp h] with y hs hy
      simp only [hs, Pi.sub_apply, hy]
    · simp [sectionL2, h]
  rw [he]
  exact hd.ennreal_toReal.ite hgood measurable_const

theorem ae_memLp_sections (μ : Measure X) [SFinite μ] (f : Lp E 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => f (x, y)) 2 ν := by
  have hi := ((Lp.memLp f).norm.integrable_sq).prod_right_ae
  filter_upwards [hi] with x hx
  exact (memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable f).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hx

end OperatorDerivativeRewrite.Foundation.ProductL2Sections
