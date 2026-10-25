import Foundation.IBMSourceEnergyGrowth
import Foundation.GaussianTimeStepIntegral
import Foundation.BrownianSignIntegral

/-! Discrete Tanaka control of the difference between ordinary and folded
clock total variations, for the actual Gaussian clock. -/
noncomputable section
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedVariationTanaka
open InfiniteGaussian GaussianTimeProcess GaussianPredictableStep BrownianSignIntegral

def crossingCorrection (x y : ℝ) : ℝ := |y-x|-|(|y|-|x|)|
def tanakaRemainder (x y : ℝ) : ℝ := |y|-|x|-signum x*(y-x)

theorem correction_nonneg (x y : ℝ) : 0 ≤ crossingCorrection x y :=
  sub_nonneg.mpr (abs_abs_sub_abs_le_abs_sub y x)

theorem correction_le_remainder (x y : ℝ) :
    crossingCorrection x y ≤ tanakaRemainder x y := by
  unfold crossingCorrection tanakaRemainder signum
  by_cases hx : 0 < x
  · rw [if_pos hx,abs_of_pos hx]
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
      ring_nf
      norm_num
    · have hy' : y < 0 := lt_of_not_ge hy
      rw [abs_of_neg hy',abs_of_neg (by linarith : y-x < 0)]
      nlinarith [neg_le_abs (-y-x)]
  · rw [if_neg hx]
    by_cases hx' : x < 0
    · rw [if_pos hx',abs_of_neg hx']
      by_cases hy : y ≤ 0
      · rw [abs_of_nonpos hy]
        have he : -y- -x = -(y-x) := by ring
        rw [he,abs_neg]
        ring_nf
        norm_num
      · have hy' : 0 < y := lt_of_not_ge hy
        rw [abs_of_pos hy',abs_of_pos (by linarith : 0 < y-x)]
        simp only [sub_neg_eq_add]
        nlinarith [neg_le_abs (y+x)]
    · have hz : x = 0 := by linarith
      simp [hz]

theorem remainder_nonneg (x y : ℝ) : 0 ≤ tanakaRemainder x y :=
  (correction_nonneg x y).trans (correction_le_remainder x y)

def signCoefficient (t : ℝ≥0) (a : Iic t → ℝ) : ℝ := signum (a ⟨t,by simp⟩)

theorem signCoefficient_measurable (t : ℝ≥0) : Measurable (signCoefficient t) :=
  signum_measurable.comp (measurable_pi_apply _)

theorem signCoefficient_memLp (t : ℝ≥0) :
    MemLp (pastCoefficient process t (signCoefficient t)) 2 gaussianProduct := by
  apply (memLp_const (1:ℝ)).mono' ?_ ?_
  · exact (signum_measurable.comp (process_stronglyMeasurable t).measurable).aestronglyMeasurable
  · exact ae_of_all _ fun Y => signum_bound (process t Y)

def signSum {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin n, signum (process (τ i.castSucc) Y)*(process (τ i.succ) Y-process (τ i.castSucc) Y)

theorem signSum_memLp {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) :
    MemLp (signSum τ) 2 gaussianProduct :=
  partitionIntegral_memLp process_isPreBrownian hτ
    (fun i => signCoefficient_measurable (τ i.castSucc))
    (fun i => signCoefficient_memLp (τ i.castSucc))

theorem signSum_square_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) :
    (∫ Y, (signSum τ Y)^2 ∂gaussianProduct) ≤ (τ (Fin.last n):ℝ)-τ 0 := by
  change (∫ Y, (partitionIntegral process τ (fun i => signCoefficient (τ i.castSucc)) Y)^2 ∂gaussianProduct) ≤ _
  rw [integral_partitionIntegral_sq process_isPreBrownian hτ
    (fun i => signCoefficient_measurable (τ i.castSucc))
    (fun i => signCoefficient_memLp (τ i.castSucc))]
  calc
    _ ≤ ∑ i : Fin n, ((τ i.succ:ℝ)-τ i.castSucc)*1 := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr (by exact_mod_cast hτ (Fin.castSucc_le_succ i)))
      calc
        _ ≤ ∫ _ : SampleSpace, (1:ℝ) ∂gaussianProduct := by
          apply integral_mono (signCoefficient_memLp _).integrable_sq (integrable_const _)
          intro Y
          change (signum (process (τ i.castSucc) Y))^2 ≤ 1
          have hb := signum_bound (process (τ i.castSucc) Y)
          rw [Real.norm_eq_abs] at hb
          simpa only [← sq,sq_abs,one_pow] using mul_self_le_mul_self (abs_nonneg _) hb
        _ = 1 := by simp
    _ = _ := by simp only [mul_one]; exact GaussianBrownianQuadraticVariation.sum_fin_differences (fun i => (τ i:ℝ))

end OperatorDerivativeRewrite.Foundation.IBMFoldedVariationTanaka
