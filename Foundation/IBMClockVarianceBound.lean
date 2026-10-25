import Foundation.IBMFoldedVariationBound

/-! Actual finite clock corrections have a partition-independent variance
bound. The deterministic centering absorbs ordinary absolute variation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockVarianceBound
open InfiniteGaussian GaussianTimeProcess IBMFoldedVariationTanaka IBMFoldedVariationBound
open IBMCenteredAbsoluteVariation

def value {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (Y : SampleSpace) : ℝ :=
  (1/2:ℝ)*(|process (τ (Fin.last n)) Y|-|process (τ 0) Y|-
    ∑ i : Fin n, |(|process (τ i.succ) Y|-|process (τ i.castSucc) Y|)|)

def shift {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : ℝ :=
  ∑ i : Fin n, meanAbs (τ i.castSucc) (τ i.succ)

theorem value_memLp {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : MemLp (value τ) 2 gaussianProduct :=
  ((((process_memLp _ 2 (by norm_num)).norm).sub ((process_memLp _ 2 (by norm_num)).norm)).sub
    (memLp_finsetSum _ fun i _ =>
      (((process_memLp _ 2 (by norm_num)).norm).sub ((process_memLp _ 2 (by norm_num)).norm)).norm)).const_mul _

theorem shifted_identity {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (Y : SampleSpace) :
    2*value τ Y+shift τ = |process (τ (Fin.last n)) Y|-|process (τ 0) Y|-
      centeredSum τ Y+correction τ Y := by
  unfold value shift centeredSum centered correction crossingCorrection IBMCenteredAbsoluteVariation.increment
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  ring

theorem shifted_square_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (h0 : τ 0 = 0) :
    (∫ Y, (2*value τ Y+shift τ)^2 ∂gaussianProduct) ≤ 18*(τ (Fin.last n):ℝ) := by
  have ha := (process_memLp (τ (Fin.last n)) 2 (by norm_num)).integrable_sq
  have hb := (centeredSum_memLp τ).integrable_sq
  have hc := (correction_memLp τ).integrable_sq
  have hx := (((value_memLp τ).const_mul 2).add (memLp_const (shift τ))).integrable_sq
  have hp : ∀ᵐ Y ∂gaussianProduct, (2*value τ Y+shift τ)^2 ≤
      3*((process (τ (Fin.last n)) Y)^2+(centeredSum τ Y)^2+(correction τ Y)^2) := by
    filter_upwards [process_zero_ae] with Y hY
    rw [shifted_identity,h0,hY,abs_zero,sub_zero]
    nlinarith [sq_abs (process (τ (Fin.last n)) Y),
      sq_nonneg (|process (τ (Fin.last n)) Y|+centeredSum τ Y),
      sq_nonneg (|process (τ (Fin.last n)) Y|-correction τ Y),
      sq_nonneg (centeredSum τ Y+correction τ Y)]
  have hi := integral_mono_ae hx (((ha.add hb).add hc).const_mul 3) hp
  rw [integral_const_mul] at hi
  simp only [Pi.add_apply] at hi
  have hab : Integrable (fun Y => (process (τ (Fin.last n)) Y)^2+(centeredSum τ Y)^2) gaussianProduct := ha.add hb
  rw [integral_add hab hc,integral_add ha hb] at hi
  have he : (∫ Y, (process (τ (Fin.last n)) Y)^2 ∂gaussianProduct) = (τ (Fin.last n):ℝ) := by
    simpa only [pow_two,min_self] using process_product_integral (τ (Fin.last n)) (τ (Fin.last n))
  rw [he] at hi
  have hb' := centeredSum_square_bound τ hτ
  rw [h0] at hb'
  simp only [NNReal.coe_zero,sub_zero] at hb'
  have hc' := correction_square_bound τ hτ h0
  linarith

theorem value_variance_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (h0 : τ 0 = 0) :
    Var[value τ; gaussianProduct] ≤ (9/2:ℝ)*(τ (Fin.last n):ℝ) := by
  have hv := variance_le_expectation_sq
    ((((value_memLp τ).const_mul 2).add (memLp_const (shift τ))).aestronglyMeasurable)
  have he : Var[fun Y => 2*value τ Y+shift τ; gaussianProduct] = 4*Var[value τ; gaussianProduct] := by
    rw [variance_add_const ((value_memLp τ).const_mul 2).aestronglyMeasurable,
      variance_const_mul]
    norm_num
  change Var[fun Y => 2*value τ Y+shift τ; gaussianProduct] ≤
    ∫ Y, (2*value τ Y+shift τ)^2 ∂gaussianProduct at hv
  rw [he] at hv
  linarith [shifted_square_bound τ hτ h0]

end OperatorDerivativeRewrite.Foundation.IBMClockVarianceBound
