import Foundation.IBMClockWeightedFoldedVariation

/-! Actual random spatial-kernel diagonal errors in original clock L2. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialClockKernelError
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation GaussianTaylorRemainder
open IBMSpatialKernelTesting IBMSpatialIncrementKernel

theorem cellPair_measurable (F : ℝ × ℝ → ℝ) (hF : Measurable F) :
    Measurable (fun q : ℝ × ℝ => cellPair F q.1 q.2) := by
  have hs : MeasurableSet {q : (ℝ × ℝ) × (ℝ × ℝ) |
      q.2 ∈ cellSet q.1.1 q.1.2 ×ˢ cellSet q.1.1 q.1.2} :=
    ((measurableSet_lt (measurable_fst.fst.min measurable_fst.snd) measurable_snd.fst).inter
      (measurableSet_le measurable_snd.fst (measurable_fst.fst.max measurable_fst.snd))).inter
    ((measurableSet_lt (measurable_fst.fst.min measurable_fst.snd) measurable_snd.snd).inter
      (measurableSet_le measurable_snd.snd (measurable_fst.fst.max measurable_fst.snd)))
  have hm : Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      rectangle (cellSet q.1.1 q.1.2) q.2*F q.2) := by
    exact (measurable_const.indicator hs).mul (hF.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

def error (F : ℝ × ℝ → ℝ) (s t : ℝ≥0) (Y : SampleSpace) : ℝ :=
  cellPair F |process s Y| |process t Y|-F (|process s Y|,|process s Y|)*
    (|process t Y|-|process s Y|)^2

theorem error_measurable (F : ℝ × ℝ → ℝ) (hF : Measurable F) (s t : ℝ≥0) :
    Measurable (error F s t) := by
  have hs := (process_stronglyMeasurable s).measurable.norm
  have ht := (process_stronglyMeasurable t).measurable.norm
  exact ((cellPair_measurable F hF).comp (hs.prodMk ht)).sub
    ((hF.comp (hs.prodMk hs)).mul ((ht.sub hs).pow_const 2))

theorem error_bound (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (s t : ℝ≥0) (Y : SampleSpace) :
    ‖error F s t Y‖ ≤ (K:ℝ)*|process t Y-process s Y|^3 :=
  (cell_diagonal_error F hF C hC |process s Y| |process t Y|).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (abs_abs_sub_abs_le_abs_sub _ _) 3) K.coe_nonneg)

theorem error_memLp (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (s t : ℝ≥0) (hst : s ≤ t) :
    MemLp (error F s t) 2 gaussianProduct := by
  apply (Lp.memLp (incrementCube s t)).of_le_mul
    (error_measurable F hF.continuous.measurable s t).aestronglyMeasurable (c:=(K:ℝ))
  filter_upwards [incrementCube_coeFn s t hst] with Y hc
  simpa only [hc,norm_pow,Real.norm_eq_abs] using error_bound F hF C hC s t Y

def cell (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (s t : ℝ≥0) (hst : s ≤ t) : GaussianL2 :=
  (error_memLp F hF C hC s t hst).toLp _

theorem cell_actual (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (s t : ℝ≥0) (hst : s ≤ t) :
    cell F hF C hC s t hst =ᵐ[gaussianProduct] error F s t := MemLp.coeFn_toLp _

theorem cell_norm_sq (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (s t : ℝ≥0) (hst : s ≤ t) :
    ‖cell F hF C hC s t hst‖^2 ≤ (K:ℝ)^2*15*((t:ℝ)-s)^3 := by
  have hb : ‖cell F hF C hC s t hst‖ ≤ (K:ℝ)*‖incrementCube s t‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [cell_actual F hF C hC s t hst,incrementCube_coeFn s t hst] with Y he hc
    simpa only [he,hc,norm_pow,Real.norm_eq_abs] using error_bound F hF C hC s t Y
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow,incrementCube_norm_sq s t hst,mul_assoc] using hs

def errorSum (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  ∑ i : Fin (N+1), cell F hF C hC (uniformTime T N i.castSucc) (uniformTime T N i.succ)
    (uniformTime_monotone T N (Fin.castSucc_le_succ i))

theorem errorSum_actual (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (T : ℝ≥0) (N : ℕ) :
    errorSum F hF C hC T N =ᵐ[gaussianProduct] fun Y => ∑ i : Fin (N+1),
      error F (uniformTime T N i.castSucc) (uniformTime T N i.succ) Y := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (N+1) =>
    cell F hF C hC (uniformTime T N i.castSucc) (uniformTime T N i.succ)
      (uniformTime_monotone T N (Fin.castSucc_le_succ i))),
    ae_all_iff.mpr (fun i : Fin (N+1) => cell_actual F hF C hC
      (uniformTime T N i.castSucc) (uniformTime T N i.succ)
      (uniformTime_monotone T N (Fin.castSucc_le_succ i)))] with Y hs hi
  change errorSum F hF C hC T N Y = _ at hs
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hi i

theorem errorSum_norm_sq (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (T : ℝ≥0) (N : ℕ) :
    ‖errorSum F hF C hC T N‖^2 ≤ (K:ℝ)^2*15*(T:ℝ)^3/(N+1) := by
  calc
    _ ≤ (N+1:ℝ)*∑ i : Fin (N+1),
        ‖cell F hF C hC (uniformTime T N i.castSucc) (uniformTime T N i.succ)
          (uniformTime_monotone T N (Fin.castSucc_le_succ i))‖^2 := by
      simpa only [errorSum,Nat.cast_add,Nat.cast_one] using norm_sum_sq_le
        (fun i : Fin (N+1) => cell F hF C hC (uniformTime T N i.castSucc)
          (uniformTime T N i.succ) (uniformTime_monotone T N (Fin.castSucc_le_succ i)))
    _ ≤ (N+1:ℝ)*∑ _i : Fin (N+1), (K:ℝ)^2*15*((T:ℝ)/(N+1))^3 := by
      gcongr with i
      simpa only [uniformTime_step] using cell_norm_sq F hF C hC
        (uniformTime T N i.castSucc) (uniformTime T N i.succ)
        (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      field_simp <;> ring

theorem errorSum_tendsto (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (T : ℝ≥0) :
    Tendsto (errorSum F hF C hC T) atTop (𝓝 0) := by
  have hr : Tendsto (fun N : ℕ => (K:ℝ)^2*15*(T:ℝ)^3/(N+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hn := squeeze_zero (fun N => sq_nonneg _) (errorSum_norm_sq F hF C hC T) hr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simp only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hs)

end OperatorDerivativeRewrite.Foundation.IBMSpatialClockKernelError
