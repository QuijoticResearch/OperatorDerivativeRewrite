import Foundation.IBMClockGaussianTail
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! An explicitly constructed Gaussian half-line potential. Its derivative
identities do not yet assume occupation-mean identification. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockHeatPotential
open IBMClockGaussianTail InfiniteGaussian IBMConstructedSources

def heatKernel (t r : ℝ) : ℝ := density (r/Real.sqrt t)/Real.sqrt t

def potential (t r : ℝ) : ℝ :=
  4*(Real.sqrt t*density (r/Real.sqrt t)-r*tail (r/Real.sqrt t))

theorem heatKernel_eq_pdf {t : ℝ} (ht : 0 < t) (r : ℝ) :
    heatKernel t r = gaussianPDFReal 0 ⟨t,ht.le⟩ r := by
  have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  have he := gaussianPDFReal_inv_mul (μ := 0) (v := 1) hs r
  have hv : (NNReal.mk ((Real.sqrt t)^2) (sq_nonneg _))*1 = ⟨t,ht.le⟩ := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
    exact Real.sq_sqrt ht.le
  rw [mul_zero, hv, abs_of_pos (Real.sqrt_pos.mpr ht)] at he
  have h : density (r/Real.sqrt t) = Real.sqrt t*gaussianPDFReal 0 ⟨t,ht.le⟩ r := by
    simpa only [density, div_eq_mul_inv, mul_comm] using he
  rw [heatKernel, h]
  field_simp

theorem clock_heat_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : StronglyMeasurable f) (T : ℝ≥0) (hT : 0 < T) :
    (∫ ω, f (clockPath ω T) ∂gaussianProduct) = ∫ r, heatKernel T r • f r := by
  rw [clock_density_integral f hf T (ne_of_gt hT)]
  congr 1
  funext r
  rw [heatKernel_eq_pdf (NNReal.coe_pos.mpr hT)]
  rfl

theorem potential_spatial_hasDerivAt {t : ℝ} (ht : 0 < t) (r : ℝ) :
    HasDerivAt (potential t) (-4*tail (r/Real.sqrt t)) r := by
  have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  have hz := (hasDerivAt_id r).div_const (Real.sqrt t)
  have hp := (density_hasDerivAt (r/Real.sqrt t)).comp r hz
  have hq := (tail_hasDerivAt (r/Real.sqrt t)).comp r hz
  have he := ((hp.const_mul (Real.sqrt t)).sub ((hasDerivAt_id r).mul hq)).const_mul 4
  convert he using 1
  · rfl
  · simp only [Function.comp_apply, id_eq]
    field_simp
    ring

theorem slope_spatial_hasDerivAt {t : ℝ} (ht : 0 < t) (r : ℝ) :
    HasDerivAt (fun x => -4*tail (x/Real.sqrt t)) (4*heatKernel t r) r := by
  have he := ((tail_hasDerivAt (r/Real.sqrt t)).comp r
    ((hasDerivAt_id r).div_const (Real.sqrt t))).const_mul (-4 : ℝ)
  convert he using 1
  · rfl
  · unfold heatKernel
    ring

theorem potential_second_spatial {t : ℝ} (ht : 0 < t) (r : ℝ) :
    deriv (deriv (potential t)) r = 4*heatKernel t r := by
  have he : deriv (potential t) = fun x => -4*tail (x/Real.sqrt t) := by
    funext x
    exact (potential_spatial_hasDerivAt ht x).deriv
  rw [he]
  exact (slope_spatial_hasDerivAt ht r).deriv

theorem potential_time_hasDerivAt {t : ℝ} (ht : 0 < t) (r : ℝ) :
    HasDerivAt (fun s => potential s r) (2*heatKernel t r) t := by
  have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  have hroot := Real.hasDerivAt_sqrt (ne_of_gt ht)
  have hz := (hasDerivAt_const t r).div hroot hs
  have hp := (density_hasDerivAt (r/Real.sqrt t)).comp t hz
  have hq := (tail_hasDerivAt (r/Real.sqrt t)).comp t hz
  have he := ((hroot.mul hp).sub (hq.const_mul r)).const_mul 4
  convert he using 1
  · rfl
  · unfold heatKernel
    simp only [Function.comp_apply, Pi.div_apply]
    field_simp
    ring

theorem potential_zero (t : ℝ) : potential t 0 = 4*Real.sqrt t*density 0 := by
  simp [potential, mul_assoc]

theorem potential_slope_zero {t : ℝ} (ht : 0 < t) : deriv (potential t) 0 = -2 := by
  rw [(potential_spatial_hasDerivAt ht 0).deriv]
  norm_num [tail_zero]

end OperatorDerivativeRewrite.Foundation.IBMClockHeatPotential
