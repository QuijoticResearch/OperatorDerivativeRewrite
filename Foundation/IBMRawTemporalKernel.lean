import Foundation.IBMFoldedClockAbsolute
import Foundation.FractionalGaussianProcess

/-! Exact raw reflected-clock IBM temporal kernel and a verified comparison
with the existing H=1/4 fractional Gaussian covariance. Equal point variances
do not identify deterministic stochastic integration energies. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMRawTemporalKernel
open InfiniteGaussian IBMTimeAveragedObservable IBMRandomTimeHilbert IBMContinuousScenery
open IBMDeterministicRangeObstruction GaussianTimeProcess GaussianAbsoluteMoments
open IBMFoldedClockAbsolute
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def kernel (s t : ℝ≥0) : ℝ := standardMoment 1 *
  (Real.sqrt s + Real.sqrt t -
    (Real.sqrt ((s:ℝ)+t+2*min (s:ℝ) t) + Real.sqrt |(t:ℝ)-s|)/2)

theorem source_inner {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    inner ℝ (sourceScenery a) (sourceScenery b) = min a b := by
  have h := IBMTemporalCovarianceObstruction.scenery_pair_gap a b ha hb
  rw [inner_sub_right,real_inner_self_eq_norm_sq,sourceScenery_norm_sq,
    abs_of_nonneg ha] at h
  rcases le_total a b with hab | hba
  · rw [max_eq_right (sub_nonpos.mpr hab),min_eq_left hab] at *
    linarith
  · rw [max_eq_left (sub_nonneg.mpr hba),min_eq_right hba] at *
    linarith

theorem actual_inner (s t : ℝ≥0) : inner ℝ (observed s) (observed t) = kernel s t := by
  change inner ℝ (jointRealization (randomSourceL2 s))
    (jointRealization (randomSourceL2 t)) = _
  rw [jointRealization.inner_map_map,L2_inner_eq_integral]
  calc
    _ = ∫ ω, min |process s ω| |process t ω| ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [(randomSourceClass_memLp s).coeFn_toLp,
        (randomSourceClass_memLp t).coeFn_toLp] with ω hs ht
      change randomSourceL2 s ω = randomSourceClass s ω at hs
      change randomSourceL2 t ω = randomSourceClass t ω at ht
      rw [hs,ht]
      exact source_inner (abs_nonneg _) (abs_nonneg _)
    _ = _ := clock_min_absolute s t

theorem kernel_symm (s t : ℝ≥0) : kernel s t = kernel t s :=
  (actual_inner s t).symm.trans ((real_inner_comm _ _).trans (actual_inner t s))

theorem actual_product_integrable (s t : ℝ≥0) :
    Integrable (fun p => IBMConstructedSources.ibmValue s p *
      IBMConstructedSources.ibmValue t p) IBMSourceLaws.jointMeasure := by
  apply ((Lp.memLp (observed s)).integrable_mul (Lp.memLp (observed t))).congr
  filter_upwards [observed_ae s,observed_ae t] with p hs ht
  simp only [Pi.mul_apply,hs,ht]

theorem actual_product (s t : ℝ≥0) :
    (∫ p, IBMConstructedSources.ibmValue s p * IBMConstructedSources.ibmValue t p
      ∂IBMSourceLaws.jointMeasure) = kernel s t := by
  rw [← actual_inner,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [observed_ae s,observed_ae t] with p hs ht
  simp only [hs,ht,Real.inner_apply]

def quarterKernel (s t : ℝ≥0) : ℝ :=
  standardMoment 1 * ((Real.sqrt s+Real.sqrt t-Real.sqrt |(t:ℝ)-s|)/2)

theorem quarter_actual_covariance (s t : ℝ≥0) :
    quarterKernel s t = standardMoment 1 *
      cov[FractionalGaussianProcess.process (1/4) (by norm_num) (by norm_num) s,
        FractionalGaussianProcess.process (1/4) (by norm_num) (by norm_num) t;
        gaussianProduct] := by
  rw [FractionalGaussianProcess.process_covariance]
  norm_num only [show (2:ℝ)*(1/4)=1/2 by norm_num]
  simp only [← Real.sqrt_eq_rpow,quarterKernel]

theorem diagonal (t : ℝ≥0) : kernel t t = quarterKernel t t := by
  have hr : Real.sqrt ((t:ℝ)+t+2*min (t:ℝ) t) = 2*Real.sqrt t := by
    rw [min_self]
    have he : (t:ℝ)+t+2*t=4*t := by ring
    rw [he,Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
    norm_num
  simp only [kernel,quarterKernel,sub_self,abs_zero,Real.sqrt_zero,hr]
  ring

/-- Strictly greater off-diagonal kernel, despite identical point variances.
This is NOT a positive-semidefinite ordering of the covariance forms. -/
theorem off_diagonal_strict {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) :
    quarterKernel s t < kernel s t := by
  have hc := IBMPhysicalL2Obstruction.first_absolute_moment_pos
  have ha : 0 < Real.sqrt (s:ℝ) := Real.sqrt_pos.2 hs
  have hab : Real.sqrt (s:ℝ) < Real.sqrt (t:ℝ) := Real.sqrt_lt_sqrt s.property hst
  have hp := mul_pos ha (sub_pos.mpr hab)
  have hrad : 0 ≤ (s:ℝ)+t+2*s := by positivity
  have hr : Real.sqrt ((s:ℝ)+t+2*s) < Real.sqrt s+Real.sqrt t := by
    by_contra hn
    have hh := mul_self_le_mul_self (by positivity : 0 ≤ Real.sqrt (s:ℝ)+Real.sqrt (t:ℝ))
      (le_of_not_gt hn)
    have hs2 : (Real.sqrt (s:ℝ))^2 = (s:ℝ) := Real.sq_sqrt s.property
    have ht2 : (Real.sqrt (t:ℝ))^2 = (t:ℝ) := Real.sq_sqrt t.property
    have hr2 : (Real.sqrt ((s:ℝ)+t+2*s))^2 = (s:ℝ)+t+2*s := Real.sq_sqrt hrad
    nlinarith only [hp,hh,hs2,ht2,hr2]
  have hd : 0 < (Real.sqrt s+Real.sqrt t-Real.sqrt ((s:ℝ)+t+2*s))/2 := by linarith
  have hm := mul_pos hc hd
  unfold kernel quarterKernel
  rw [min_eq_left (show (s:ℝ)≤t from hst.le)]
  nlinarith

theorem pair_sum_energy (s t : ℝ≥0) :
    ‖observed s+observed t‖^2 = kernel s s + 2*kernel s t + kernel t t := by
  have hs := actual_inner s s
  have ht := actual_inner t t
  rw [real_inner_self_eq_norm_sq] at hs ht
  rw [norm_add_sq_real,hs,ht,actual_inner]

theorem sum_energy_exceeds_quarter {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) :
    quarterKernel s s+2*quarterKernel s t+quarterKernel t t < ‖observed s+observed t‖^2 := by
  rw [pair_sum_energy,diagonal,diagonal]
  linarith [off_diagonal_strict hs hst]

theorem difference_energy_below_quarter {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) :
    ‖observed t-observed s‖^2 <
      quarterKernel t t-2*quarterKernel s t+quarterKernel s s := by
  have hss := actual_inner s s
  have htt := actual_inner t t
  have hcross : inner ℝ (observed t) (observed s) = kernel s t :=
    (real_inner_comm _ _).trans (actual_inner s t)
  rw [real_inner_self_eq_norm_sq] at hss htt
  rw [norm_sub_sq_real,hss,htt,hcross,diagonal,diagonal]
  linarith [off_diagonal_strict hs hst]

/-- The explicit raw kernel is the ACTUAL energy of every finite deterministic
linear combination, not an assumed positive covariance model. -/
theorem finite_energy {ι : Type*} (A : Finset ι) (a : ι → ℝ) (τ : ι → ℝ≥0) :
    ‖∑ i ∈ A, a i • observed (τ i)‖^2 =
      ∑ i ∈ A, ∑ j ∈ A, a i * a j * kernel (τ i) (τ j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    actual_inner,mul_assoc]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [kernel_symm (τ j) (τ i)]

theorem kernel_positive {ι : Type*} (A : Finset ι) (a : ι → ℝ) (τ : ι → ℝ≥0) :
    0 ≤ ∑ i ∈ A, ∑ j ∈ A, a i * a j * kernel (τ i) (τ j) := by
  rw [← finite_energy A a τ]
  exact sq_nonneg _

end OperatorDerivativeRewrite.Foundation.IBMRawTemporalKernel
