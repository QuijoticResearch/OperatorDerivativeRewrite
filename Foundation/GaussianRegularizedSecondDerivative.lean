import Foundation.GaussianHermiteDomains

/-! Actual Gaussian L2 regularization of the second derivative. The constant
output channel is retained; the construction uses the existing Hermite basis. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianRegularizedSecondDerivative
open GaussianCore
set_option backward.isDefEq.respectTransparency false

theorem hermite_ext {f g : GaussianL2} (h : ∀ n, hermiteCoefficient f n = hermiteCoefficient g n) :
    f = g := by
  apply hermiteBasis.repr.injective
  apply lp.ext
  funext n
  simpa only [hermiteBasis_coefficient, hermiteCoefficient] using h n

theorem shifted_square_summable (f : GaussianL2) (k : ℕ) :
    Summable (fun n => hermiteCoefficient f (n + k) ^ 2) :=
  (hermiteCoefficient_hasSum_sq f).summable.comp_injective (by
    intro a b h
    change a + k = b + k at h
    omega)

theorem weighted_coefficients_summable (f : GaussianL2) (k : ℕ) (w : ℕ → ℝ)
    (C : ℝ) (hw : ∀ n, w n ^ 2 ≤ C ^ 2) :
    Summable (fun n => (w n * hermiteCoefficient f (n + k)) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _
    ((shifted_square_summable f k).mul_left (C ^ 2))
  intro n
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (hw n) (sq_nonneg _)

def weightedShiftValue (k : ℕ) (w : ℕ → ℝ) (C : ℝ) (hw : ∀ n, w n ^ 2 ≤ C ^ 2)
    (f : GaussianL2) : GaussianL2 :=
  Classical.choose (exists_hermite_coefficients _ (weighted_coefficients_summable f k w C hw))

theorem weightedShiftValue_coefficient (k : ℕ) (w : ℕ → ℝ) (C : ℝ)
    (hw : ∀ n, w n ^ 2 ≤ C ^ 2) (f : GaussianL2) (n : ℕ) :
    hermiteCoefficient (weightedShiftValue k w C hw f) n = w n * hermiteCoefficient f (n + k) :=
  Classical.choose_spec (exists_hermite_coefficients _ (weighted_coefficients_summable f k w C hw)) n

theorem weightedShiftValue_norm_sq (k : ℕ) (w : ℕ → ℝ) (C : ℝ)
    (hw : ∀ n, w n ^ 2 ≤ C ^ 2) (f : GaussianL2) :
    ‖weightedShiftValue k w C hw f‖ ^ 2 ≤ C ^ 2 * ‖f‖ ^ 2 := by
  rw [← (hermiteCoefficient_hasSum_sq (weightedShiftValue k w C hw f)).tsum_eq]
  simp_rw [weightedShiftValue_coefficient]
  calc
    _ ≤ ∑' n, C ^ 2 * hermiteCoefficient f (n + k) ^ 2 :=
      Summable.tsum_le_tsum (fun n => by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (hw n) (sq_nonneg _))
        (weighted_coefficients_summable f k w C hw) ((shifted_square_summable f k).mul_left _)
    _ = C ^ 2 * ∑' n, hermiteCoefficient f (n + k) ^ 2 := tsum_mul_left
    _ ≤ C ^ 2 * ∑' n, hermiteCoefficient f n ^ 2 :=
      mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj
        (hermiteCoefficient_hasSum_sq f).summable (fun n => sq_nonneg _)
        (by intro a b h; change a + k = b + k at h; omega :
          Function.Injective (fun n : ℕ => n + k))) (sq_nonneg _)
    _ = _ := by rw [(hermiteCoefficient_hasSum_sq f).tsum_eq]

def weightedShiftLinear (k : ℕ) (w : ℕ → ℝ) (C : ℝ) (hw : ∀ n, w n ^ 2 ≤ C ^ 2) :
    GaussianL2 →ₗ[ℝ] GaussianL2 where
  toFun := weightedShiftValue k w C hw
  map_add' f g := by
    apply hermite_ext
    intro n
    have ha (a b : GaussianL2) : hermiteCoefficient (a + b) n =
        hermiteCoefficient a n + hermiteCoefficient b n := inner_add_right _ _ _
    rw [weightedShiftValue_coefficient, ha, weightedShiftValue_coefficient, weightedShiftValue_coefficient]
    simp only [hermiteCoefficient, inner_add_right]
    ring
  map_smul' c f := by
    apply hermite_ext
    intro n
    have hs (a : GaussianL2) : hermiteCoefficient (c • a) n = c * hermiteCoefficient a n :=
      real_inner_smul_right _ _ _
    simp only [RingHom.id_apply]
    rw [weightedShiftValue_coefficient, hs, weightedShiftValue_coefficient]
    simp only [hermiteCoefficient, real_inner_smul_right]
    ring

def weightedShift (k : ℕ) (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ n, w n ^ 2 ≤ C ^ 2) :
    GaussianL2 →L[ℝ] GaussianL2 :=
  (weightedShiftLinear k w C hw).mkContinuous C (fun f => by
    have hh := weightedShiftValue_norm_sq k w C hw f
    have hc := mul_nonneg hC (norm_nonneg f)
    change ‖weightedShiftValue k w C hw f‖ ≤ C * ‖f‖
    nlinarith [norm_nonneg (weightedShiftValue k w C hw f)])

theorem weightedShift_coefficient (k : ℕ) (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ n, w n ^ 2 ≤ C ^ 2) (f : GaussianL2) (n : ℕ) :
    hermiteCoefficient (weightedShift k w C hC hw f) n = w n * hermiteCoefficient f (n + k) :=
  weightedShiftValue_coefficient k w C hw f n

def weight (n : ℕ) : ℝ := if n = 0 then 1 else (n : ℝ)⁻¹

theorem weight_pos (n : ℕ) : 0 < weight n := by
  by_cases hn : n = 0
  · simp [weight, hn]
  · simp only [weight, if_neg hn]
    positivity

theorem weight_sq_le_one (n : ℕ) : weight n ^ 2 ≤ 1 := by
  by_cases hn : n = 0
  · simp [weight, hn]
  · have hh : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hi : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hh
    have hp := (weight_pos n).le
    simp only [weight, if_neg hn] at hp ⊢
    nlinarith

def gain (n : ℕ) : ℝ := weight n * Real.sqrt (n + 1 : ℝ) * Real.sqrt (n + 2 : ℝ)

theorem gain_sq_le_six (n : ℕ) : gain n ^ 2 ≤ 6 := by
  rw [gain, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  by_cases hn : n = 0
  · norm_num [weight, hn]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
    simp only [weight, if_neg hn]
    have he : (n : ℝ)⁻¹ ^ 2 * (n + 1) * (n + 2) =
        ((n + 1) * (n + 2)) / (n : ℝ) ^ 2 := by
      field_simp
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
    have hm := mul_nonneg (sub_nonneg.mpr hn1) (show 0 ≤ 5 * (n : ℝ) + 2 by positivity)
    nlinarith

def smoothing : GaussianL2 →L[ℝ] GaussianL2 :=
  weightedShift 0 weight 1 zero_le_one (fun n => by simpa using weight_sq_le_one n)

def regularizedSecond : GaussianL2 →L[ℝ] GaussianL2 :=
  weightedShift 2 gain (Real.sqrt 6) (Real.sqrt_nonneg _) (fun n => by
    simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)] using gain_sq_le_six n)

theorem smoothing_coefficient (f : GaussianL2) (n : ℕ) :
    hermiteCoefficient (smoothing f) n = weight n * hermiteCoefficient f n := by
  simpa only [smoothing, Nat.add_zero] using weightedShift_coefficient 0 weight 1 zero_le_one
    (fun n => by simpa using weight_sq_le_one n) f n

theorem regularizedSecond_coefficient (f : GaussianL2) (n : ℕ) :
    hermiteCoefficient (regularizedSecond f) n = gain n * hermiteCoefficient f (n + 2) :=
  weightedShift_coefficient 2 gain (Real.sqrt 6) (Real.sqrt_nonneg _) _ f n

theorem smoothing_injective : Function.Injective smoothing := by
  intro f g hfg
  apply hermite_ext
  intro n
  have hh := congrArg (fun f => hermiteCoefficient f n) hfg
  simp only [smoothing_coefficient] at hh
  exact mul_left_cancel₀ (ne_of_gt (weight_pos n)) hh

/-- Agreement with the ACTUAL two successive closed derivatives, not merely
a matching definition of assigned spectral coefficients. -/
theorem regularizedSecond_actual_graph (f g h : GaussianL2)
    (hf : (f, g) ∈ closedDerivative.graph) (hg : (g, h) ∈ closedDerivative.graph) :
    regularizedSecond f = smoothing h := by
  apply hermite_ext
  intro n
  rw [regularizedSecond_coefficient, smoothing_coefficient,
    (closedDerivative_graph_iff g h).mp hg n, (closedDerivative_graph_iff f g).mp hf (n + 1)]
  simp only [gain, Nat.cast_add, Nat.cast_one, add_assoc]
  norm_num
  ring

theorem weightedShift_norm_le (k : ℕ) (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ n, w n ^ 2 ≤ C ^ 2) : ‖weightedShift k w C hC hw‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  have hh := weightedShiftValue_norm_sq k w C hw f
  have hc := mul_nonneg hC (norm_nonneg f)
  change ‖weightedShiftValue k w C hw f‖ ≤ C * ‖f‖
  nlinarith [norm_nonneg (weightedShiftValue k w C hw f)]

theorem smoothing_norm_le : ‖smoothing‖ ≤ 1 := weightedShift_norm_le _ _ _ _ _

theorem regularizedSecond_norm_le : ‖regularizedSecond‖ ≤ Real.sqrt 6 :=
  weightedShift_norm_le _ _ _ _ _

theorem normalized_coefficient (n m : ℕ) :
    hermiteCoefficient (normalizedHermite n) m = if m = n then 1 else 0 :=
  (orthonormal_iff_ite.mp normalizedHermite_orthonormal) m n

theorem regularizedSecond_hermite (n : ℕ) :
    regularizedSecond (normalizedHermite (n + 2)) = gain n • normalizedHermite n := by
  apply hermite_ext
  intro m
  rw [regularizedSecond_coefficient]
  simp only [hermiteCoefficient, real_inner_smul_right]
  change gain m * hermiteCoefficient (normalizedHermite (n + 2)) (m + 2) =
    gain n * hermiteCoefficient (normalizedHermite n) m
  rw [normalized_coefficient, normalized_coefficient]
  by_cases hm : m = n
  · subst m; simp
  · simp [hm]

theorem regularizedSecond_retains_constant_channel :
    regularizedSecond (normalizedHermite 2) = Real.sqrt 2 • normalizedHermite 0 := by
  simpa [gain, weight] using regularizedSecond_hermite 0

theorem regularizedSecond_cubic :
    regularizedSecond (normalizedHermite 3) = Real.sqrt 6 • normalizedHermite 1 := by
  have hg : gain 1 = Real.sqrt 6 := by
    norm_num [gain, weight]
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simpa only [hg] using regularizedSecond_hermite 1

theorem regularizedSecond_norm : ‖regularizedSecond‖ = Real.sqrt 6 := by
  apply le_antisymm regularizedSecond_norm_le
  have hn (n : ℕ) : ‖normalizedHermite n‖ = 1 := normalizedHermite_orthonormal.norm_eq_one n
  have hh := regularizedSecond.le_opNorm (normalizedHermite 3)
  rw [regularizedSecond_cubic, norm_smul, hn, hn, mul_one, mul_one,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hh
  exact hh

theorem smoothing_hermite (n : ℕ) : smoothing (normalizedHermite n) = weight n • normalizedHermite n := by
  apply hermite_ext
  intro m
  rw [smoothing_coefficient]
  change weight m * hermiteCoefficient (normalizedHermite n) m =
    inner ℝ (normalizedHermite m) (weight n • normalizedHermite n)
  rw [real_inner_smul_right]
  change weight m * hermiteCoefficient (normalizedHermite n) m =
    weight n * hermiteCoefficient (normalizedHermite n) m
  rw [normalized_coefficient]
  by_cases hm : m = n <;> simp [hm]

/-- The regularization loses no Gaussian mode, and its image is dense. -/
theorem smoothing_denseRange : DenseRange smoothing := by
  have hs : Submodule.span ℝ (Set.range normalizedHermite) ≤ smoothing.toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    refine ⟨(weight n)⁻¹ • normalizedHermite n, ?_⟩
    change smoothing ((weight n)⁻¹ • normalizedHermite n) = normalizedHermite n
    rw [map_smul, smoothing_hermite, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (weight_pos n)), one_smul]
  exact normalizedHermite_dense_span.mono hs

end OperatorDerivativeRewrite.Foundation.GaussianRegularizedSecondDerivative
