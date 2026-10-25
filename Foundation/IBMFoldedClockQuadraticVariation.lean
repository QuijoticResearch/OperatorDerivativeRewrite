import Foundation.IBMProjectedGridEscapeCriterion

/-! Actual folded Brownian-clock quadratic variation in original clock L1.
Only the already verified origin-boundary and fourth-moment tail estimates
are needed to transfer the existing Brownian quadratic variation. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedClockQuadraticVariation
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMTerminalRiemannOccupation IBMRandomBoundaryEnergy IBMOriginBoundaryEnergy
open IBMClippedClockStrongLimit

def loss (x y : ℝ) : ℝ := (y-x)^2-(|y|-|x|)^2

theorem loss_nonneg (x y : ℝ) : 0 ≤ loss x y := by
  have h := abs_abs_sub_abs_le_abs_sub y x
  have hs := mul_self_le_mul_self (abs_nonneg (|y|-|x|)) h
  simp only [← sq,sq_abs] at hs
  unfold loss
  linarith

theorem loss_bound (x y : ℝ) : loss x y ≤ (y-x)^2 := by
  unfold loss
  nlinarith [sq_nonneg (|y|-|x|)]

theorem loss_crossing_bound (δ x y : ℝ) :
    loss x y ≤ (y-x)^2*(originBand δ (x,0)+(if δ < |y-x| then 1 else 0)) := by
  have hb := loss_bound x y
  have ho : 0 ≤ originBand δ (x,0) := by unfold originBand; split_ifs <;> norm_num
  by_cases hi : |y-x| ≤ δ
  · rw [if_neg (not_lt_of_ge hi)]
    by_cases hx : |x| ≤ δ
    · simpa only [originBand,if_pos hx,add_zero,mul_one] using hb
    · have hd : δ < |x| := lt_of_not_ge hx
      have he := abs_le.mp hi
      have hz : loss x y = 0 := by
        rcases le_total 0 x with hp | hn
        · have hy : 0 ≤ y := by rw [abs_of_nonneg hp] at hd; linarith [he.1]
          simp only [loss,abs_of_nonneg hp,abs_of_nonneg hy,sub_self]
        · have hy : y ≤ 0 := by rw [abs_of_nonpos hn] at hd; linarith [he.2]
          simp only [loss,abs_of_nonpos hn,abs_of_nonpos hy]
          ring
      rw [hz]
      positivity
  · rw [if_pos (lt_of_not_ge hi)]
    nlinarith [sq_nonneg (y-x)]

def rawSum (H : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (N+1), (process (uniformTime H N i.succ) Y-process (uniformTime H N i.castSucc) Y)^2

def foldedSum (H : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (N+1), (|process (uniformTime H N i.succ) Y|-|process (uniformTime H N i.castSucc) Y|)^2

def lossValue (H : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ := rawSum H N Y-foldedSum H N Y

theorem rawSum_integrable (H : ℝ≥0) (N : ℕ) : Integrable (rawSum H N) gaussianProduct :=
  ((Lp.memLp (quadraticVariation (uniformTime H N))).ae_eq
    (quadraticVariation_coeFn _ (uniformTime_monotone H N))).integrable (by norm_num)

theorem foldedSum_integrable (H : ℝ≥0) (N : ℕ) : Integrable (foldedSum H N) gaussianProduct := by
  apply integrable_finset_sum
  intro i hi
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using
    (((process_memLp (uniformTime H N i.succ) 2 (by norm_num)).norm).sub
      ((process_memLp (uniformTime H N i.castSucc) 2 (by norm_num)).norm)).integrable_sq

theorem lossValue_integrable (H : ℝ≥0) (N : ℕ) : Integrable (lossValue H N) gaussianProduct :=
  (rawSum_integrable H N).sub (foldedSum_integrable H N)

theorem lossValue_eq_sum (H : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    lossValue H N Y = ∑ i : Fin (N+1), loss
      (process (uniformTime H N i.castSucc) Y) (process (uniformTime H N i.succ) Y) := by
  unfold lossValue rawSum foldedSum loss
  rw [Finset.sum_sub_distrib]

theorem lossValue_nonneg (H : ℝ≥0) (N : ℕ) (Y : SampleSpace) : 0 ≤ lossValue H N Y := by
  rw [lossValue_eq_sum]
  exact Finset.sum_nonneg fun i _ => loss_nonneg _ _

theorem lossValue_bound (δ : ℝ) (H : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    lossValue H N Y ≤ weightedValue (originBand δ) H N Y+IBMClippedClockTail.value δ H N Y := by
  rw [lossValue_eq_sum]
  calc
    _ ≤ ∑ i : Fin (N+1), (process (uniformTime H N i.succ) Y-process (uniformTime H N i.castSucc) Y)^2*
      (originBand δ (process (uniformTime H N i.castSucc) Y,0)+
        (if δ < |process (uniformTime H N i.succ) Y-process (uniformTime H N i.castSucc) Y| then 1 else 0)) :=
      Finset.sum_le_sum fun i _ => loss_crossing_bound _ _ _
    _ = _ := by
      unfold weightedValue IBMClippedClockTail.value
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      unfold IBMClippedClockTail.cell originBand
      split_ifs <;> ring

def lossClass (H : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct := (lossValue_integrable H N).toL1 _

theorem lossClass_actual (H : ℝ≥0) (N : ℕ) : lossClass H N =ᵐ[gaussianProduct] lossValue H N :=
  (lossValue_integrable H N).coeFn_toL1

theorem lossClass_norm_bound (δ : ℝ) (H : ℝ≥0) (N : ℕ) :
    ‖lossClass H N‖ ≤ weightedMean (originBand δ) H N+
      ∫ Y, IBMClippedClockTail.value δ H N Y ∂gaussianProduct := by
  rw [lossClass,L1.norm_of_fun_eq_integral_norm]
  calc
    _ = ∫ Y, lossValue H N Y ∂gaussianProduct :=
      integral_congr_ae (ae_of_all _ fun Y => Real.norm_of_nonneg (lossValue_nonneg H N Y))
    _ ≤ ∫ Y, weightedValue (originBand δ) H N Y+IBMClippedClockTail.value δ H N Y ∂gaussianProduct :=
      integral_mono (lossValue_integrable H N)
        ((origin_energy_integrable δ H N).add (IBMClippedClockTail.value_integrable δ H N))
        (lossValue_bound δ H N)
    _ = _ := integral_add (origin_energy_integrable δ H N) (IBMClippedClockTail.value_integrable δ H N)

theorem lossClass_tendsto (H : ℝ≥0) (hH : 0 < H) : Tendsto (lossClass H) atTop (𝓝 0) := by
  have hm := (origin_weightedMean_tendsto IBMClippedClockTail.width IBMClippedClockTail.width_tendsto H hH).add
    (IBMClippedClockTail.width_mean_tendsto H)
  simp only [zero_add] at hm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using squeeze_zero (fun N => norm_nonneg (lossClass H N))
    (fun N => lossClass_norm_bound (IBMClippedClockTail.width N) H N) hm

def foldedClass (H : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct := (foldedSum_integrable H N).toL1 _

theorem foldedClass_actual (H : ℝ≥0) (N : ℕ) : foldedClass H N =ᵐ[gaussianProduct] foldedSum H N :=
  (foldedSum_integrable H N).coeFn_toL1

theorem foldedClass_identity (H : ℝ≥0) (N : ℕ) : foldedClass H N =
    clockL1 (quadraticVariation (uniformTime H N))-lossClass H N := by
  apply Lp.ext
  filter_upwards [foldedClass_actual H N,
    Lp.coeFn_sub (clockL1 (quadraticVariation (uniformTime H N))) (lossClass H N),
    clockL1_actual (quadraticVariation (uniformTime H N)),
    quadraticVariation_coeFn _ (uniformTime_monotone H N),lossClass_actual H N] with Y hf hs hl hq he
  rw [hf,hs,Pi.sub_apply,hl,hq,he]
  unfold lossValue rawSum foldedSum
  ring

theorem foldedClass_tendsto (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (foldedClass H) atTop (𝓝 (clockL1 ((H:ℝ) • gaussianOne))) := by
  have h := (clockL1_tendsto _ _ (uniform_quadraticVariation_tendsto H)).sub (lossClass_tendsto H hH)
  simp only [sub_zero] at h
  exact h.congr' (Eventually.of_forall fun N => (foldedClass_identity H N).symm)

theorem actual_absolute_error_tendsto (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => ∫ Y, |foldedSum H N Y-(H:ℝ)| ∂gaussianProduct) atTop (𝓝 0) := by
  have h := tendsto_iff_norm_sub_tendsto_zero.mp (foldedClass_tendsto H hH)
  apply h.congr'
  exact Eventually.of_forall fun N => by
    change ‖foldedClass H N-clockL1 ((H:ℝ) • gaussianOne)‖ = _
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (foldedClass H N) (clockL1 ((H:ℝ) • gaussianOne)),
      foldedClass_actual H N,clockL1_actual ((H:ℝ) • gaussianOne),
      Lp.coeFn_smul (H:ℝ) (gaussianOne:GaussianL2),gaussianOne_coeFn] with Y hs hf hl hm h1
    simp only [hs,Pi.sub_apply,hf,hl,hm,Pi.smul_apply,h1,smul_eq_mul,mul_one,Real.norm_eq_abs]

end OperatorDerivativeRewrite.Foundation.IBMFoldedClockQuadraticVariation
