import Foundation.IBMCenteredAbsoluteVariation

/-! Uniform second-moment control of the actual folding crossing correction.
No uncentered bound on Brownian total variation is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedVariationBound
open InfiniteGaussian GaussianTimeProcess IBMFoldedVariationTanaka

def correction {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin n, crossingCorrection (process (τ i.castSucc) Y) (process (τ i.succ) Y)

theorem correction_nonnegative {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (Y : SampleSpace) :
    0 ≤ correction τ Y := Finset.sum_nonneg fun i _ => correction_nonneg _ _

theorem correction_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (Y : SampleSpace) :
    correction τ Y ≤ |process (τ (Fin.last n)) Y|-|process (τ 0) Y|-signSum τ Y := by
  calc
    _ ≤ ∑ i : Fin n, tanakaRemainder (process (τ i.castSucc) Y) (process (τ i.succ) Y) :=
      Finset.sum_le_sum fun i _ => correction_le_remainder _ _
    _ = _ := by
      unfold tanakaRemainder signSum
      rw [Finset.sum_sub_distrib]
      rw [GaussianBrownianQuadraticVariation.sum_fin_differences (fun i => |process (τ i) Y|)]

theorem correction_memLp {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    MemLp (correction τ) 2 gaussianProduct := by
  apply memLp_finsetSum
  intro i hi
  exact (((process_memLp (τ i.succ) 2 (by norm_num)).sub
    (process_memLp (τ i.castSucc) 2 (by norm_num))).norm).sub
      ((((process_memLp (τ i.succ) 2 (by norm_num)).norm).sub
        ((process_memLp (τ i.castSucc) 2 (by norm_num)).norm)).norm)

theorem correction_square_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (h0 : τ 0 = 0) :
    (∫ Y, (correction τ Y)^2 ∂gaussianProduct) ≤ 4*(τ (Fin.last n):ℝ) := by
  have hf := (process_memLp (τ (Fin.last n)) 2 (by norm_num)).integrable_sq
  have hs := (signSum_memLp τ hτ).integrable_sq
  have hb : ∀ᵐ Y ∂gaussianProduct, (correction τ Y)^2 ≤
      2*((process (τ (Fin.last n)) Y)^2+(signSum τ Y)^2) := by
    filter_upwards [process_zero_ae] with Y hY
    have hc := correction_bound τ Y
    rw [h0,hY,abs_zero,sub_zero] at hc
    have hn := correction_nonnegative τ Y
    have he := mul_self_le_mul_self hn hc
    nlinarith [sq_abs (process (τ (Fin.last n)) Y),
      sq_nonneg (|process (τ (Fin.last n)) Y|+signSum τ Y)]
  have hi := integral_mono_ae (correction_memLp τ).integrable_sq ((hf.add hs).const_mul 2) hb
  rw [integral_const_mul] at hi
  simp only [Pi.add_apply] at hi
  rw [integral_add hf hs] at hi
  have he : (∫ Y, (process (τ (Fin.last n)) Y)^2 ∂gaussianProduct) = (τ (Fin.last n):ℝ) := by
    simpa only [pow_two,min_self] using process_product_integral (τ (Fin.last n)) (τ (Fin.last n))
  rw [he] at hi
  have hb := signSum_square_bound τ hτ
  rw [h0] at hb
  simp only [NNReal.coe_zero,sub_zero] at hb
  linarith

end OperatorDerivativeRewrite.Foundation.IBMFoldedVariationBound
