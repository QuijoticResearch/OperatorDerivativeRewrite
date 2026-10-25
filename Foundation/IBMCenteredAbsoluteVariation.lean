import Foundation.IBMFoldedVariationTanaka

/-! Actual centered absolute Brownian increment sums, with no uncentered
variation bound asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCenteredAbsoluteVariation
open InfiniteGaussian GaussianTimeProcess

def increment (s t : ℝ≥0) (Y : SampleSpace) : ℝ := process t Y-process s Y
def meanAbs (s t : ℝ≥0) : ℝ := ∫ Y, |increment s t Y| ∂gaussianProduct
def centered (s t : ℝ≥0) (Y : SampleSpace) : ℝ := |increment s t Y|-meanAbs s t

theorem abs_memLp (s t : ℝ≥0) : MemLp (fun Y => |increment s t Y|) 2 gaussianProduct := by
  simpa only [Real.norm_eq_abs,GaussianPredictableStep.increment,increment] using (GaussianPredictableStep.increment_memLp process_isPreBrownian s t).norm

theorem centered_memLp (s t : ℝ≥0) : MemLp (centered s t) 2 gaussianProduct :=
  (abs_memLp s t).sub (memLp_const _)

theorem centered_mean (s t : ℝ≥0) : (∫ Y, centered s t Y ∂gaussianProduct) = 0 := by
  unfold centered
  rw [integral_sub ((abs_memLp s t).integrable (by norm_num)) (integrable_const _)]
  simp [meanAbs]

theorem centered_square (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ Y, (centered s t Y)^2 ∂gaussianProduct) = (t:ℝ)-s-(meanAbs s t)^2 := by
  have hi := (abs_memLp s t).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hs := (abs_memLp s t).integrable_sq
  have hs' : Integrable (fun Y => (increment s t Y)^2) gaussianProduct := by simpa only [sq_abs] using hs
  have he : (fun Y => (centered s t Y)^2) = fun Y =>
      (increment s t Y)^2-2*meanAbs s t*|increment s t Y|+(meanAbs s t)^2 := by
    funext Y
    unfold centered
    nlinarith [sq_abs (increment s t Y)]
  have hm : Integrable (fun Y => 2*meanAbs s t*|increment s t Y|) gaussianProduct := hi.const_mul _
  have hd : Integrable (fun Y => (increment s t Y)^2-2*meanAbs s t*|increment s t Y|) gaussianProduct := hs'.sub hm
  rw [he,integral_add hd (integrable_const ((meanAbs s t)^2)),
    integral_sub hs' hm,integral_const_mul]
  have hq := GaussianPredictableStep.integral_increment_sq process_isPreBrownian hst
  change (∫ Y, (increment s t Y)^2 ∂gaussianProduct) = (t:ℝ)-s at hq
  rw [hq]
  simp only [meanAbs,integral_const,probReal_univ,one_smul]
  ring

theorem centered_cross_zero (a b c d : ℝ≥0) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (∫ Y, centered a b Y*centered c d Y ∂gaussianProduct) = 0 := by
  have hi := (process_disjoint_increments_independent a b c d hab hbc hcd).comp
    ((continuous_abs.measurable).sub_const (meanAbs a b)) ((continuous_abs.measurable).sub_const (meanAbs c d))
  have he := hi.integral_fun_mul_eq_mul_integral (centered_memLp a b).aestronglyMeasurable
    (centered_memLp c d).aestronglyMeasurable
  change (∫ Y, centered a b Y*centered c d Y ∂gaussianProduct) =
    (∫ Y, centered a b Y ∂gaussianProduct)*(∫ Y, centered c d Y ∂gaussianProduct) at he
  rw [centered_mean,zero_mul] at he
  exact he

def centeredSum {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin n, centered (τ i.castSucc) (τ i.succ) Y

theorem centeredSum_memLp {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    MemLp (centeredSum τ) 2 gaussianProduct :=
  memLp_finsetSum _ fun i _ => centered_memLp _ _

theorem centeredSum_square_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) :
    (∫ Y, (centeredSum τ Y)^2 ∂gaussianProduct) ≤ (τ (Fin.last n):ℝ)-τ 0 := by
  let X (i : Fin n) := centered (τ i.castSucc) (τ i.succ)
  have hi (i j : Fin n) : Integrable (fun Y => X i Y*X j Y) gaussianProduct :=
    (centered_memLp _ _).integrable_mul (centered_memLp _ _)
  have hc (i j : Fin n) (hne : i ≠ j) : (∫ Y, X i Y*X j Y ∂gaussianProduct) = 0 := by
    have ho {i j : Fin n} (hij : i < j) : i.succ ≤ j.castSucc := by
      simp only [Fin.le_iff_val_le_val,Fin.lt_iff_val_lt_val,Fin.val_succ,Fin.val_castSucc] at *
      omega
    rcases lt_or_gt_of_ne hne with h | h
    · exact centered_cross_zero _ _ _ _ (hτ (Fin.castSucc_le_succ i)) (hτ (ho h)) (hτ (Fin.castSucc_le_succ j))
    · simpa only [mul_comm] using centered_cross_zero _ _ _ _ (hτ (Fin.castSucc_le_succ j)) (hτ (ho h)) (hτ (Fin.castSucc_le_succ i))
  have he : (∫ Y, (centeredSum τ Y)^2 ∂gaussianProduct) = ∑ i : Fin n, ∫ Y, (X i Y)^2 ∂gaussianProduct := by
    calc
      _ = ∫ Y, ∑ i : Fin n, ∑ j : Fin n, X i Y*X j Y ∂gaussianProduct := by
        apply integral_congr_ae
        exact ae_of_all _ fun Y => by
          simp only [centeredSum,X,pow_two,Finset.sum_mul,Finset.mul_sum]
          rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ j : Fin n, ∫ Y, X i Y*X j Y ∂gaussianProduct := by
        rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hi i j)]
        exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ (fun j _ => hi i j)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · simp only [pow_two]
        · intro j hj hji; exact hc i j hji.symm
        · simp
  rw [he]
  calc
    _ ≤ ∑ i : Fin n, ((τ i.succ:ℝ)-τ i.castSucc) := by
      apply Finset.sum_le_sum
      intro i hi
      have he := centered_square (τ i.castSucc) (τ i.succ) (hτ (Fin.castSucc_le_succ i))
      dsimp [X]
      rw [he]
      exact sub_le_self _ (sq_nonneg _)
    _ = _ := GaussianBrownianQuadraticVariation.sum_fin_differences (fun i => (τ i:ℝ))

end OperatorDerivativeRewrite.Foundation.IBMCenteredAbsoluteVariation
