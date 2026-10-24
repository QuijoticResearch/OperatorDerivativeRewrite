import Foundation.IBMFoldedHeatEnergy
import Foundation.ProductL2Sections
import Foundation.GaussianTimeHilbert

/-! A genuinely strongly measurable spatial-L2 family of folded heat columns.
Zero remaining variance is totalized by zero, not by a singular Dirac. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedHeatField
open IBMFoldedHeatEnergy GaussianTimeHilbert
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

def scalar (z : (ℝ × ℝ≥0) × ℝ) : ℝ := folded z.1.1 z.1.2 z.2

theorem scalar_stronglyMeasurable : StronglyMeasurable scalar := by
  have h1 : Measurable (fun z : (ℝ × ℝ≥0) × ℝ =>
      gaussianPDFReal z.1.1 z.1.2 z.2) :=
    measurable_uncurry_gaussianPDFReal.comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have h2 : Measurable (fun z : (ℝ × ℝ≥0) × ℝ =>
      gaussianPDFReal (-z.1.1) z.1.2 z.2) :=
    measurable_uncurry_gaussianPDFReal.comp
      (measurable_fst.fst.neg.prodMk (measurable_fst.snd.prodMk measurable_snd))
  change StronglyMeasurable (fun z : (ℝ × ℝ≥0) × ℝ =>
    if z.2 ∈ Ioi (0 : ℝ) then
      gaussianPDFReal z.1.1 z.1.2 z.2-gaussianPDFReal (-z.1.1) z.1.2 z.2 else 0)
  exact (h1.sub h2).stronglyMeasurable.ite
    (measurable_snd measurableSet_Ioi) stronglyMeasurable_const

theorem folded_zero (b : ℝ) : folded b 0 = 0 := by
  funext x
  simp [folded, difference, gaussianPDFReal_zero_var]

theorem folded_memLp_all (b : ℝ) (v : ℝ≥0) : MemLp (folded b v) 2 volume := by
  by_cases hv : v = 0
  · rw [hv, folded_zero]
    exact MemLp.zero
  · exact folded_memLp b (pos_iff_ne_zero.mpr hv)

def column (p : ℝ × ℝ≥0) : TimeHilbert :=
  ProductL2Sections.sectionL2 (volume : Measure ℝ) scalar p

theorem column_stronglyMeasurable : StronglyMeasurable column :=
  ProductL2Sections.sectionL2_stronglyMeasurable volume scalar scalar_stronglyMeasurable

theorem column_coeFn (b : ℝ) (v : ℝ≥0) :
    column (b,v) =ᵐ[volume] folded b v :=
  ProductL2Sections.sectionL2_coeFn volume scalar (b,v) (folded_memLp_all b v)

theorem column_eq_spatial (b : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    column (b,v) = spatial b v hv := by
  apply Lp.ext
  exact (column_coeFn b v).trans (spatial_coeFn b hv).symm

theorem column_zero (b : ℝ) : column (b,0) = 0 := by
  apply Lp.ext
  exact ((column_coeFn b 0).trans (Eventually.of_forall fun x => congrFun (folded_zero b) x)).trans
    (Lp.coeFn_zero ℝ 2 volume).symm

theorem column_energy (b : ℝ) (v : ℝ≥0) :
    ‖column (b,v)‖^2 = (1-Real.exp (-b^2/v))/(2*Real.sqrt (Real.pi*v)) := by
  by_cases hv : v = 0
  · simp [hv, column_zero]
  · rw [column_eq_spatial b (pos_iff_ne_zero.mpr hv), spatial_energy]

end OperatorDerivativeRewrite.Foundation.IBMFoldedHeatField
