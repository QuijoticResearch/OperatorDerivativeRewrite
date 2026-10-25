import Foundation.IBMNativeGridEscape
import Foundation.IBMRawGridWickLimit

/-! Smooth tests of the folded clock: Taylor error is controlled by the
ORIGINAL Gaussian cubic increments, without a smoothness claim at zero. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedSmoothQuadraticError
open InfiniteGaussian GaussianTimeProcess GaussianTaylorRemainder
open GaussianSmoothQuadraticVariation GaussianBrownianQuadraticVariation

theorem pointwise_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (x y : ℝ) :
    ‖quadraticError f |x| |y|‖ ≤ (A:ℝ)*B*|y-x|^3 := by
  exact (quadratic_error_bound f hf A B hA hB |x| |y|).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (abs_abs_sub_abs_le_abs_sub y x) 3) (by positivity))

theorem error_memLp (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B)
    (s t : ℝ≥0) (hst : s ≤ t) :
    MemLp (fun Y => quadraticError f |process s Y| |process t Y|) 2 gaussianProduct := by
  have hs := continuous_abs.measurable.comp (process_stronglyMeasurable s).measurable
  have ht := continuous_abs.measurable.comp (process_stronglyMeasurable t).measurable
  have hd := (hf.continuous_deriv (by norm_num)).measurable
  have hm : Measurable (fun Y => quadraticError f |process s Y| |process t Y|) :=
    ((hf.continuous.measurable.comp ht).sub (hf.continuous.measurable.comp hs)).pow_const 2 |>.sub
      (((hd.comp hs).pow_const 2).mul ((ht.sub hs).pow_const 2))
  apply (Lp.memLp (incrementCube s t)).of_le_mul hm.aestronglyMeasurable (c:=(A:ℝ)*B)
  filter_upwards [incrementCube_coeFn s t hst] with Y hc
  simpa only [hc,norm_pow,Real.norm_eq_abs] using pointwise_bound f hf A B hA hB (process s Y) (process t Y)

def cell (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B)
    (s t : ℝ≥0) (hst : s ≤ t) : GaussianL2 :=
  (error_memLp f hf A B hA hB s t hst).toLp _

theorem cell_actual (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B)
    (s t : ℝ≥0) (hst : s ≤ t) :
    cell f hf A B hA hB s t hst =ᵐ[gaussianProduct]
      fun Y => quadraticError f |process s Y| |process t Y| := MemLp.coeFn_toLp _

theorem cell_norm_sq (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ‖cell f hf A B hA hB s t hst‖^2 ≤ ((A:ℝ)*B)^2*15*((t:ℝ)-s)^3 := by
  have hb : ‖cell f hf A B hA hB s t hst‖ ≤ (A:ℝ)*B*‖incrementCube s t‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [cell_actual f hf A B hA hB s t hst,incrementCube_coeFn s t hst] with Y he hc
    simpa only [he,hc,norm_pow,Real.norm_eq_abs] using pointwise_bound f hf A B hA hB (process s Y) (process t Y)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow,incrementCube_norm_sq s t hst,mul_assoc] using hs

def errorSum (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B)
    (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  ∑ i : Fin (N+1), cell f hf A B hA hB (uniformTime T N i.castSucc)
    (uniformTime T N i.succ) (uniformTime_monotone T N (Fin.castSucc_le_succ i))

theorem errorSum_actual (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B)
    (T : ℝ≥0) (N : ℕ) : errorSum f hf A B hA hB T N =ᵐ[gaussianProduct]
      fun Y => ∑ i : Fin (N+1), quadraticError f |process (uniformTime T N i.castSucc) Y|
        |process (uniformTime T N i.succ) Y| := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (N+1) =>
    cell f hf A B hA hB (uniformTime T N i.castSucc) (uniformTime T N i.succ)
      (uniformTime_monotone T N (Fin.castSucc_le_succ i))),
    ae_all_iff.mpr (fun i : Fin (N+1) => cell_actual f hf A B hA hB
      (uniformTime T N i.castSucc) (uniformTime T N i.succ)
      (uniformTime_monotone T N (Fin.castSucc_le_succ i)))] with Y hs hi
  change errorSum f hf A B hA hB T N Y = _ at hs
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hi i

theorem errorSum_norm_sq (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B)
    (T : ℝ≥0) (N : ℕ) :
    ‖errorSum f hf A B hA hB T N‖^2 ≤ ((A:ℝ)*B)^2*15*(T:ℝ)^3/(N+1) := by
  calc
    _ ≤ (N+1:ℝ)*∑ i : Fin (N+1),
        ‖cell f hf A B hA hB (uniformTime T N i.castSucc) (uniformTime T N i.succ)
          (uniformTime_monotone T N (Fin.castSucc_le_succ i))‖^2 := by
      simpa only [errorSum,Nat.cast_add,Nat.cast_one] using norm_sum_sq_le
        (fun i : Fin (N+1) => cell f hf A B hA hB (uniformTime T N i.castSucc)
          (uniformTime T N i.succ) (uniformTime_monotone T N (Fin.castSucc_le_succ i)))
    _ ≤ (N+1:ℝ)*∑ _i : Fin (N+1), ((A:ℝ)*B)^2*15*((T:ℝ)/(N+1))^3 := by
      gcongr with i
      simpa only [uniformTime_step] using cell_norm_sq f hf A B hA hB
        (uniformTime T N i.castSucc) (uniformTime T N i.succ)
        (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      field_simp <;> ring

theorem errorSum_tendsto (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (T : ℝ≥0) :
    Tendsto (errorSum f hf A B hA hB T) atTop (𝓝 0) := by
  have hr : Tendsto (fun N : ℕ => ((A:ℝ)*B)^2*15*(T:ℝ)^3/(N+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hn := squeeze_zero (fun N => sq_nonneg _) (errorSum_norm_sq f hf A B hA hB T) hr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simp only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hs)

end OperatorDerivativeRewrite.Foundation.IBMFoldedSmoothQuadraticError
