import Foundation.IBMClockHeatOccupation
import Foundation.IBMMollifier
import Foundation.IBMPhysicalDerivativeKernel
import Foundation.IBMClockCubicTimeProjection
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Uniform smoothing by the genuine folded Gaussian transition law.
This is a transition estimate for the IBM clock, not a joint Sobolev-domain theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.IBMFoldedTransitionBound

def peak (v : ℝ≥0) : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹

theorem peak_nonneg (v : ℝ≥0) : 0 ≤ peak v := by unfold peak; positivity

theorem pdf_le_peak (a : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal a v x ≤ peak v := by
  unfold gaussianPDFReal peak
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))

theorem folded_integrable {k : ℝ → ℝ} (hc : Continuous k)
    (hi : Integrable k) (hn : ∀ x, 0 ≤ k x) :
    Integrable (fun x => k |x|) := by
  apply (hi.add hi.comp_neg).mono' (hc.comp continuous_abs).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change ‖k |x|‖ ≤ k x + k (-x)
    rw [Real.norm_eq_abs, abs_of_nonneg (hn _)]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (hn _)
    · rw [abs_of_nonpos hx]
      exact le_add_of_nonneg_left (hn _)

theorem folded_weight_integrable (a : ℝ) (v : ℝ≥0) {k : ℝ → ℝ}
    (hc : Continuous k) (hi : Integrable k) (hn : ∀ x, 0 ≤ k x) :
    Integrable (fun x => gaussianPDFReal a v x * k |x|) := by
  apply ((folded_integrable hc hi hn).const_mul (peak v)).mono'
    ((stronglyMeasurable_gaussianPDFReal a v).mul
      (hc.comp continuous_abs).stronglyMeasurable).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change ‖gaussianPDFReal a v x * k |x|‖ ≤ peak v * k |x|
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (hn _))]
    exact mul_le_mul_of_nonneg_right (pdf_le_peak a v x) (hn _)

/-- L1 to L-infinity estimate, uniform in the Gaussian mean and kernel width.
The nonzero variance hypothesis is essential for the density representation. -/
theorem folded_average_le (a : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {k : ℝ → ℝ}
    (hc : Continuous k) (hi : Integrable k) (hn : ∀ x, 0 ≤ k x) :
    (∫ x, k |x| ∂gaussianReal a v) ≤ 2 * peak v * ∫ x, k x := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  calc
    _ ≤ ∫ x, peak v * k |x| := integral_mono
      (folded_weight_integrable a v hc hi hn)
      ((folded_integrable hc hi hn).const_mul (peak v))
      (fun x => mul_le_mul_of_nonneg_right (pdf_le_peak a v x) (hn _))
    _ = peak v * (2 * ∫ x in Ioi (0 : ℝ), k x) := by
      rw [integral_const_mul, integral_comp_abs]
    _ ≤ peak v * (2 * ∫ x, k x) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (setIntegral_le_integral hi (ae_of_all _ hn)) (by norm_num))
      (peak_nonneg v)
    _ = _ := by ring

open IBMMollifier

theorem shifted_integrable (n : ℕ) (r : ℝ) :
    Integrable (fun x => kernel n (r-x)) :=
  ((kernel_smooth n).continuous.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
    ((kernel_compactSupport n).comp_homeomorph (Homeomorph.subLeft r))

theorem shifted_mass (n : ℕ) (r : ℝ) : (∫ x, kernel n (r-x)) = 1 := by
  have hneg := integral_neg_eq_self (fun x : ℝ => kernel n (r+x)) volume
  have hadd := integral_add_left_eq_self (μ := volume) (kernel n) r
  simpa only [sub_eq_add_neg] using hneg.trans (hadd.trans (kernel_integral n))

theorem mollifier_average_le (n : ℕ) (x a : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ y, kernel n (|y|-x) ∂gaussianReal a v) ≤ 2 * peak v := by
  have hc : Continuous (fun y => kernel n (y-x)) :=
    (kernel_smooth n).continuous.comp (continuous_id.sub continuous_const)
  have hi : Integrable (fun y => kernel n (y-x)) :=
    ((kernel_smooth n).continuous.integrable_of_hasCompactSupport
      (kernel_compactSupport n)).comp_sub_right x
  have hm : (∫ y, kernel n (y-x)) = 1 := by
    simpa only [sub_eq_neg_add] using
      (integral_add_left_eq_self (μ := volume) (kernel n) (-x)).trans (kernel_integral n)
  simpa only [hm, mul_one] using folded_average_le a hv hc hi (fun y => kernel_nonneg n _)

/-- Actual physical-space covariance of the two mollified white-noise columns. -/
def overlap (n m : ℕ) (r q : ℝ) : ℝ :=
  ∫ x, kernel n (r-x) * kernel m (q-x)

theorem overlap_nonneg (n m : ℕ) (r q : ℝ) : 0 ≤ overlap n m r q :=
  integral_nonneg fun _ => mul_nonneg (kernel_nonneg n _) (kernel_nonneg m _)

theorem overlap_eq_inner (n m : ℕ) (r q : ℝ) : overlap n m r q =
    inner ℝ (IBMPhysicalNoiseCalculus.convolutionKernel (deriv (kernel n)) r)
      (IBMPhysicalNoiseCalculus.convolutionKernel (deriv (kernel m)) q) := by
  rw [IBMPhysicalDerivativeKernel.derivative_eq_translated
    ((kernel_smooth n).of_le (by simp)) (kernel_compactSupport n),
    IBMPhysicalDerivativeKernel.derivative_eq_translated
      ((kernel_smooth m).of_le (by simp)) (kernel_compactSupport m), L2_inner_eq_integral]
  symm
  apply integral_congr_ae
  filter_upwards [IBMPhysicalDerivativeKernel.translatedClass_coeFn
    (kernel n) (kernel_smooth n).continuous (kernel_compactSupport n) r,
    IBMPhysicalDerivativeKernel.translatedClass_coeFn
      (kernel m) (kernel_smooth m).continuous (kernel_compactSupport m) q] with x hn hm
  simp only [hn, hm, Real.inner_apply]

theorem overlap_column_integrable (n m : ℕ) (r a : ℝ) (v : ℝ≥0) :
    Integrable (fun p : ℝ × ℝ => kernel n (r-p.1) * kernel m (|p.2|-p.1))
      (volume.prod (gaussianReal a v)) := by
  obtain ⟨M, hM⟩ := (kernel_smooth m).continuous.norm.bddAbove_range_of_hasCompactSupport
    (kernel_compactSupport m).norm
  have hbound := (shifted_integrable n r).mul_prod
    (integrable_const M : Integrable (fun _ : ℝ => M) (gaussianReal a v))
  have hc : Continuous (fun p : ℝ × ℝ => kernel n (r-p.1) * kernel m (|p.2|-p.1)) :=
    (((kernel_smooth n).continuous.comp (continuous_const.sub continuous_fst)).mul
      ((kernel_smooth m).continuous.comp (continuous_snd.abs.sub continuous_fst)))
  apply hbound.mono' hc.aestronglyMeasurable
  exact ae_of_all _ fun p => by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg n _)]
    exact mul_le_mul_of_nonneg_left (hM ⟨_, rfl⟩) (kernel_nonneg n _)

/-- Uniform in both mollifier widths and the first spatial location. Fubini is
discharged for the actual positive product kernel and the Gaussian clock law. -/
theorem overlap_average_le (n m : ℕ) (r a : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ y, overlap n m r |y| ∂gaussianReal a v) ≤ 2 * peak v := by
  have hf := overlap_column_integrable n m r a v
  change (∫ y, ∫ x, kernel n (r-x) * kernel m (|y|-x) ∂volume ∂gaussianReal a v) ≤ _
  rw [← integral_integral_swap hf]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∫ x, kernel n (r-x) * (2 * peak v) := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun x => mul_nonneg (kernel_nonneg n _)
          (integral_nonneg fun y => kernel_nonneg m _))
        ((shifted_integrable n r).mul_const _)
      exact ae_of_all _ fun x => mul_le_mul_of_nonneg_left
        (mollifier_average_le m x a hv) (kernel_nonneg n _)
    _ = _ := by rw [integral_mul_const, shifted_mass, one_mul]

theorem overlap_eq_coefficient_inner (n m : ℕ) (r q : ℝ) : overlap n m r q =
    inner ℝ (IBMGaussianSteinMoments.tripleCoefficient n r 1)
      (IBMGaussianSteinMoments.tripleCoefficient m q 1) := by
  rw [overlap_eq_inner]
  have hn := IBMPhysicalNoiseCalculus.triple_coefficient_physical n r 1
  have hm := IBMPhysicalNoiseCalculus.triple_coefficient_physical m q 1
  simp only [IBMJointMollifierGaussian.derivativeKernel, Fin.isValue] at hn hm
  rw [← hn, ← hm]
  exact (IBMPhysicalNoiseRealization.physicalToCoefficient.inner_map_map _ _).symm

theorem overlap_continuous (n m : ℕ) :
    Continuous (fun p : ℝ × ℝ => overlap n m p.1 p.2) := by
  simp_rw [overlap_eq_coefficient_inner]
  exact ((IBMClockCubicTimeProjection.tripleCoefficient_continuous n 1).comp continuous_fst).inner
    ((IBMClockCubicTimeProjection.tripleCoefficient_continuous m 1).comp continuous_snd)

theorem overlap_bounded (n m : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ r q, overlap n m r q ≤ M := by
  obtain ⟨M, hM⟩ := (kernel_smooth m).continuous.norm.bddAbove_range_of_hasCompactSupport
    (kernel_compactSupport m).norm
  refine ⟨M, (norm_nonneg (kernel m 0)).trans (hM ⟨0, rfl⟩), fun r q => ?_⟩
  calc
    _ ≤ ∫ x, kernel n (r-x) * M := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun x => mul_nonneg (kernel_nonneg n _) (kernel_nonneg m _))
        ((shifted_integrable n r).mul_const _)
      exact ae_of_all _ fun x => mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hM ⟨q-x, rfl⟩)) (kernel_nonneg n _)
    _ = M := by rw [integral_mul_const, shifted_mass, one_mul]

/-- The estimate at two actual Brownian-clock times, derived from the verified
independent increment law. No conditional-density assumption is supplied. -/
theorem clock_overlap_le (n m : ℕ) (s t : ℝ≥0) (hst : s < t) :
    (∫ ω, overlap n m |GaussianTimeProcess.process s ω| |GaussianTimeProcess.process t ω|
      ∂InfiniteGaussian.gaussianProduct) ≤ 2 * peak (nndist (t : ℝ) (s : ℝ)) := by
  open GaussianTimeProcess InfiniteGaussian in
  have hind : IndepFun (process s) (fun ω => process t ω - process s ω) gaussianProduct := by
    apply (process_disjoint_increments_independent 0 s s t (by positivity) le_rfl hst.le).congr
      ?_ (Filter.EventuallyEq.rfl)
    filter_upwards [process_zero_ae] with ω hω
    simp [hω]
  have hp := hind.hasLaw_prod (GaussianTimeProcess.process_hasLaw s)
    (GaussianTimeProcess.process_increment_hasLaw s t)
  let v : ℝ≥0 := nndist (t : ℝ) (s : ℝ)
  have hv : v ≠ 0 := by simpa [v] using (ne_of_gt hst)
  let F : ℝ × ℝ → ℝ := fun p => overlap n m |p.1| |p.1+p.2|
  have hF : Continuous F := (overlap_continuous n m).comp
    (continuous_fst.abs.prodMk (continuous_fst.add continuous_snd).abs)
  obtain ⟨M, hM0, hM⟩ := overlap_bounded n m
  have hi : Integrable F ((gaussianReal 0 s).prod (gaussianReal 0 v)) :=
    Integrable.of_bound hF.aestronglyMeasurable M (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (overlap_nonneg _ _ _ _)]
      exact hM _ _)
  have he : (∫ ω, overlap n m |GaussianTimeProcess.process s ω| |GaussianTimeProcess.process t ω|
      ∂InfiniteGaussian.gaussianProduct) = ∫ p, F p ∂(gaussianReal 0 s).prod (gaussianReal 0 v) := by
    convert hp.integral_comp hF.aestronglyMeasurable using 1
    congr 1
    funext ω
    simp [F]
  rw [he, integral_prod _ hi]
  calc
    _ ≤ ∫ _a : ℝ, 2 * peak v ∂gaussianReal 0 s := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun a => integral_nonneg fun b => overlap_nonneg n m |a| |a+b|)
        (integrable_const (2 * peak v))
      exact ae_of_all _ fun a => by
        have hl := gaussianReal_const_add (HasLaw.id (μ := gaussianReal 0 v)) a
        have hc : Continuous (fun y : ℝ => overlap n m |a| |y|) :=
          (overlap_continuous n m).comp (continuous_const.prodMk continuous_abs)
        have heq := hl.integral_comp hc.aestronglyMeasurable
        simp only [zero_add, Function.comp_def, id_eq] at heq
        change (∫ b, overlap n m |a| |a+b| ∂gaussianReal 0 v) ≤ _
        rw [heq]
        simpa using overlap_average_le n m |a| a hv
    _ = _ := by simp [v]

/-- The same bound for the actual continuous clock modification used in IBM. -/
theorem clockPath_overlap_le (n m : ℕ) (s t : ℝ≥0) (hst : s < t) :
    (∫ ω, overlap n m |IBMConstructedSources.clockPath ω s|
      |IBMConstructedSources.clockPath ω t| ∂InfiniteGaussian.gaussianProduct) ≤
      2 * peak (nndist (t : ℝ) (s : ℝ)) := by
  have he : (∫ ω, overlap n m |IBMConstructedSources.clockPath ω s|
      |IBMConstructedSources.clockPath ω t| ∂InfiniteGaussian.gaussianProduct) =
      ∫ ω, overlap n m |GaussianTimeProcess.process s ω| |GaussianTimeProcess.process t ω|
        ∂InfiniteGaussian.gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [IBMConstructedSources.clockPath_coordinate_ae s,
      IBMConstructedSources.clockPath_coordinate_ae t] with ω hs ht
    rw [hs, ht]
  rw [he]
  exact clock_overlap_le n m s t hst

end OperatorDerivativeRewrite.Foundation.IBMFoldedTransitionBound
