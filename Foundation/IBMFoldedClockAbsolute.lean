import Foundation.IBMActualIncrementMoments
import Foundation.IBMPhysicalL2Obstruction

/-! Exact folded-clock overlap moments from the ORIGINAL Gaussian clock.
No independent-copy or fractional-Brownian replacement law is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedClockAbsolute
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianHilbertProcess
open GaussianAbsoluteMoments SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

theorem absolute_isonormal (h : TimeHilbert) :
    (∫ ω, |isonormal TimeHilbert h ω| ∂gaussianProduct) = ‖h‖ * standardMoment 1 := by
  change (∫ ω, |firstChaosEmbedding (hilbertEmbedding TimeHilbert h) ω| ∂gaussianProduct) = _
  simpa only [(hilbertEmbedding TimeHilbert).norm_map,pow_one] using
    firstChaos_absolute_moment (hilbertEmbedding TimeHilbert h) 1

theorem clock_absolute (t : ℝ≥0) :
    (∫ ω, |process t ω| ∂gaussianProduct) = Real.sqrt t * standardMoment 1 := by
  have hn : ‖timeVector t‖ = Real.sqrt (t:ℝ) := by
    rw [← timeVector_norm_sq t,Real.sqrt_sq (norm_nonneg _)]
  change (∫ ω, |isonormal TimeHilbert (timeVector t) ω| ∂gaussianProduct) = _
  rw [absolute_isonormal,hn]

theorem clock_sum_absolute (s t : ℝ≥0) :
    (∫ ω, |process s ω+process t ω| ∂gaussianProduct) =
      Real.sqrt ((s:ℝ)+t+2*min (s:ℝ) t) * standardMoment 1 := by
  have ha : (fun ω => process s ω+process t ω) =ᵐ[gaussianProduct]
      isonormal TimeHilbert (timeVector s+timeVector t) :=
    (isonormal_add_ae (timeVector s) (timeVector t)).symm
  have hn : ‖timeVector s+timeVector t‖^2 = (s:ℝ)+t+2*min (s:ℝ) t := by
    rw [norm_add_sq_real,timeVector_norm_sq,timeVector_norm_sq,timeVector_inner]
    ring
  have hr : ‖timeVector s+timeVector t‖ = Real.sqrt ((s:ℝ)+t+2*min (s:ℝ) t) := by
    rw [← hn,Real.sqrt_sq (norm_nonneg _)]
  have he := integral_congr_ae (ha.fun_comp abs)
  simp only [Function.comp_def] at he
  rw [he,absolute_isonormal,hr]

theorem clock_sub_absolute (s t : ℝ≥0) :
    (∫ ω, |process s ω-process t ω| ∂gaussianProduct) =
      Real.sqrt |(t:ℝ)-s| * standardMoment 1 := by
  have ha : (fun ω => process s ω-process t ω) =ᵐ[gaussianProduct]
      isonormal TimeHilbert (timeVector s-timeVector t) :=
    (isonormal_sub_ae (timeVector s) (timeVector t)).symm
  have hn : ‖timeVector s-timeVector t‖^2 = |(t:ℝ)-s| := by
    rw [norm_sub_sq_real,timeVector_norm_sq,timeVector_norm_sq,timeVector_inner]
    rcases le_total (s:ℝ) t with h | h
    · rw [min_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · rw [min_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
      ring
  have hr : ‖timeVector s-timeVector t‖ = Real.sqrt |(t:ℝ)-s| := by
    rw [← hn,Real.sqrt_sq (norm_nonneg _)]
  have he := integral_congr_ae (ha.fun_comp abs)
  simp only [Function.comp_def] at he
  rw [he,absolute_isonormal,hr]

theorem min_absolute_identity (x y : ℝ) :
    min |x| |y| = |x|+|y|-(|x+y|+|x-y|)/2 := by
  simp only [abs_eq_max_neg,max_def,min_def]
  split_ifs <;> linarith

theorem clock_min_integrable (s t : ℝ≥0) :
    Integrable (fun ω => min |process s ω| |process t ω|) gaussianProduct := by
  have hc : Continuous (fun p : ℝ × ℝ => min |p.1| |p.2|) := by fun_prop
  have hm := hc.measurable.comp ((process_stronglyMeasurable s).measurable.prodMk
    (process_stronglyMeasurable t).measurable)
  apply (((process_memLp s 1 (by simp)).integrable (by simp)).abs).mono'
    hm.aestronglyMeasurable
  apply ae_of_all
  intro ω
  change ‖min |process s ω| |process t ω|‖ ≤ |process s ω|
  rw [Real.norm_of_nonneg (le_min (abs_nonneg _) (abs_nonneg _))]
  exact min_le_left _ _

theorem clock_min_absolute (s t : ℝ≥0) :
    (∫ ω, min |process s ω| |process t ω| ∂gaussianProduct) =
      standardMoment 1 * (Real.sqrt s + Real.sqrt t -
        (Real.sqrt ((s:ℝ)+t+2*min (s:ℝ) t) + Real.sqrt |(t:ℝ)-s|)/2) := by
  have hs : Integrable (process s) gaussianProduct :=
    (process_memLp s 1 (by simp)).integrable (by simp)
  have ht : Integrable (process t) gaussianProduct :=
    (process_memLp t 1 (by simp)).integrable (by simp)
  simp_rw [min_absolute_identity]
  change (∫ ω, ((fun ω => |process s ω|)+(fun ω => |process t ω|)) ω -
    ((fun ω => |(process s+process t) ω|)+(fun ω => |(process s-process t) ω|)) ω / 2
    ∂gaussianProduct) = _
  rw [integral_sub (hs.abs.add ht.abs) (((hs.add ht).abs.add (hs.sub ht).abs).div_const 2)]
  change (∫ ω, |process s ω|+|process t ω| ∂gaussianProduct) -
    (∫ ω, (|process s ω+process t ω|+|process s ω-process t ω|)/2 ∂gaussianProduct) = _
  rw [integral_add hs.abs ht.abs,integral_div]
  have he := integral_add (hs.add ht).abs (hs.sub ht).abs
  simp only [Pi.add_apply,Pi.sub_apply] at he
  rw [he,clock_absolute,clock_absolute,clock_sum_absolute,clock_sub_absolute]
  ring

end OperatorDerivativeRewrite.Foundation.IBMFoldedClockAbsolute
