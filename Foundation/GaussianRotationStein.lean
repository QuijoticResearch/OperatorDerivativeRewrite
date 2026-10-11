/-
Copyright (c) 2026 OperatorDerivativeRewrite contributors.
Gaussian rotation uses Mathlib's centered-Gaussian product rotation theorem.
The Stein step below reuses the attributed local Foundation.GaussianSteinBounded proof.
-/
import Foundation.GaussianSteinBounded
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.Prod

/-! Static Gaussian rotation and bounded C¹ Stein pairing for interpolation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianRotationStein

abbrev γ : Measure ℝ := GaussianCore.γ

/-- Every real unit-circle pair defines an orientation-preserving Gaussian rotation. -/
theorem gaussian_rotation_map (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (γ.prod γ).map (fun p : ℝ × ℝ =>
      (a * p.1 + b * p.2, -b * p.1 + a * p.2)) = γ.prod γ := by
  have ha₁ : -1 ≤ a := by nlinarith [sq_nonneg b, sq_nonneg (a + 1)]
  have ha₂ : a ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  let θ : ℝ := if 0 ≤ b then Real.arccos a else -Real.arccos a
  have hroot : Real.sqrt (1 - a ^ 2) = |b| := by
    rw [show 1 - a ^ 2 = b ^ 2 by linarith [hab], Real.sqrt_sq_eq_abs]
  have hc : Real.cos θ = a := by
    dsimp [θ]
    split_ifs
    · exact Real.cos_arccos ha₁ ha₂
    · simpa [Real.cos_neg] using Real.cos_arccos ha₁ ha₂
  have hs : Real.sin θ = b := by
    dsimp [θ]
    split_ifs with hb
    · rw [Real.sin_arccos, hroot, abs_of_nonneg hb]
    · have hb' : b < 0 := lt_of_not_ge hb
      rw [Real.sin_neg, Real.sin_arccos, hroot, abs_of_neg hb']
      ring
  have hmean : γ[id] = 0 := by
    simp [γ]
  have hR : (ContinuousLinearMap.rotation θ : ℝ × ℝ →L[ℝ] ℝ × ℝ) =
      (fun p : ℝ × ℝ => (a * p.1 + b * p.2, -b * p.1 + a * p.2)) := by
    funext p
    simp [ContinuousLinearMap.rotation_apply, hc, hs, smul_eq_mul]
  have hrot := IsGaussian.map_rotation_eq_self (μ := γ) hmean θ
  rw [hR] at hrot
  exact hrot


/-- The absolute coordinate has finite first moment under the product Gaussian law. -/
theorem product_abs_coordinates_integrable :
    Integrable (fun p : ℝ × ℝ => |p.1|) (γ.prod γ) ∧
      Integrable (fun p : ℝ × ℝ => |p.2|) (γ.prod γ) := by
  have hi : Integrable (fun x : ℝ => |x|) γ :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).abs
  exact ⟨hi.comp_fst γ, hi.comp_snd γ⟩

/-- Both original and rotated pairings have genuine finite product integrals. -/
theorem rotated_stein_integrable
    (a b : ℝ) (k ψ : ℝ → ℝ) (hk : Measurable k) (hψ : ContDiff ℝ 1 ψ)
    {K A C : ℝ} (hk_bd : ∀ z, |k z| ≤ K)
    (hψ_bd : ∀ x, |ψ x| ≤ A) (hψ'_bd : ∀ x, |deriv ψ x| ≤ C) :
    Integrable (fun p : ℝ × ℝ =>
      ψ p.1 * k (a * p.1 + b * p.2) * (-b * p.1 + a * p.2)) (γ.prod γ) ∧
    Integrable (fun p : ℝ × ℝ =>
      deriv ψ p.1 * k (a * p.1 + b * p.2)) (γ.prod γ) ∧
    Integrable (fun p : ℝ × ℝ =>
      k p.1 * (p.2 * ψ (a * p.1 - b * p.2))) (γ.prod γ) ∧
    Integrable (fun p : ℝ × ℝ =>
      k p.1 * deriv ψ (a * p.1 - b * p.2)) (γ.prod γ) := by
  obtain ⟨h1, h2⟩ := product_abs_coordinates_integrable
  have hK : 0 ≤ K := (abs_nonneg _).trans (hk_bd 0)
  have hA : 0 ≤ A := (abs_nonneg _).trans (hψ_bd 0)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hψ'_bd 0)
  have hmeas₁ : Measurable (fun p : ℝ × ℝ => k (a * p.1 + b * p.2)) :=
    hk.comp (by fun_prop)
  have hmeas₂ : Measurable (fun p : ℝ × ℝ => ψ (a * p.1 - b * p.2)) :=
    hψ.continuous.measurable.comp (by fun_prop)
  have hmeas₃ : Measurable (fun p : ℝ × ℝ => deriv ψ (a * p.1 - b * p.2)) :=
    (hψ.continuous_deriv le_rfl).measurable.comp (by fun_prop)
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      (A * K * |b|) * |p.1| + (A * K * |a|) * |p.2|) (γ.prod γ) :=
    (h1.const_mul _).add (h2.const_mul _)
  constructor
  · refine Integrable.mono' hmajor ?_ ?_
    · have hvel : Measurable (fun p : ℝ × ℝ => -b * p.1 + a * p.2) := by fun_prop
      exact (((hψ.continuous.measurable.comp measurable_fst).mul hmeas₁).mul
        hvel).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro p
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hv : |-b * p.1 + a * p.2| ≤ |b| * |p.1| + |a| * |p.2| := by
        calc
          |-b * p.1 + a * p.2| ≤ |-b * p.1| + |a * p.2| := abs_add_le _ _
          _ = |b| * |p.1| + |a| * |p.2| := by simp [abs_mul]
      calc
        |ψ p.1| * |k (a * p.1 + b * p.2)| * |-b * p.1 + a * p.2|
            ≤ A * K * (|b| * |p.1| + |a| * |p.2|) := by
              have hprod : |ψ p.1| * |k (a * p.1 + b * p.2)| ≤ A * K :=
                mul_le_mul (hψ_bd _) (hk_bd _) (abs_nonneg _) hA
              exact (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans
                (mul_le_mul_of_nonneg_left hv (mul_nonneg hA hK))
          _ = (A * K * |b|) * |p.1| + (A * K * |a|) * |p.2| := by ring
  constructor
  · refine Integrable.mono' (integrable_const (C * K)) ?_ ?_
    · exact ((hψ.continuous_deriv le_rfl).measurable.comp measurable_fst |>.mul
        hmeas₁).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro p
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hψ'_bd _) (hk_bd _) (abs_nonneg _) hC
  constructor
  · refine Integrable.mono' (h2.const_mul (K * A)) ?_ ?_
    · exact ((hk.comp measurable_fst).mul
        (measurable_snd.mul hmeas₂)).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro p
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc
        |k p.1| * (|p.2| * |ψ (a * p.1 - b * p.2)|)
            ≤ K * (|p.2| * A) := by
              apply mul_le_mul (hk_bd _) ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hK
              exact mul_le_mul_of_nonneg_left (hψ_bd _) (abs_nonneg _)
          _ = K * A * |p.2| := by ring
  · refine Integrable.mono' (integrable_const (K * C)) ?_ ?_
    · exact ((hk.comp measurable_fst).mul hmeas₃).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro p
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hk_bd _) (hψ'_bd _) (abs_nonneg _) hK

/-- Rotating a Gaussian pair and applying bounded C¹ Stein in the second coordinate.
The bounded measurable `k` is never differentiated. -/
theorem rotated_stein_identity
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (k ψ : ℝ → ℝ) (hk : Measurable k) (hψ : ContDiff ℝ 1 ψ)
    {K A C : ℝ} (hk_bd : ∀ z, |k z| ≤ K)
    (hψ_bd : ∀ x, |ψ x| ≤ A) (hψ'_bd : ∀ x, |deriv ψ x| ≤ C) :
    (∫ p : ℝ × ℝ,
      ψ p.1 * k (a * p.1 + b * p.2) * (-b * p.1 + a * p.2) ∂(γ.prod γ)) =
      -b * ∫ p : ℝ × ℝ,
        deriv ψ p.1 * k (a * p.1 + b * p.2) ∂(γ.prod γ) := by
  obtain ⟨hL, hR, hFL, hFR⟩ :=
    rotated_stein_integrable a b k ψ hk hψ hk_bd hψ_bd hψ'_bd
  let R : ℝ × ℝ → ℝ × ℝ := fun p =>
    (a * p.1 + b * p.2, -b * p.1 + a * p.2)
  let F : ℝ × ℝ → ℝ := fun p => k p.1 * (p.2 * ψ (a * p.1 - b * p.2))
  let G : ℝ × ℝ → ℝ := fun p => k p.1 * deriv ψ (a * p.1 - b * p.2)
  have hmap : (γ.prod γ).map R = γ.prod γ := gaussian_rotation_map a b hab
  have hinv (p : ℝ × ℝ) :
      a * (a * p.1 + b * p.2) - b * (-b * p.1 + a * p.2) = p.1 := by
    calc
      a * (a * p.1 + b * p.2) - b * (-b * p.1 + a * p.2) =
          (a ^ 2 + b ^ 2) * p.1 := by ring
      _ = p.1 := by rw [hab]; ring
  have hFmeas : Measurable F := by
    dsimp [F]
    exact (hk.comp measurable_fst).mul
      (measurable_snd.mul (hψ.continuous.measurable.comp (by fun_prop)))
  have hGmeas : Measurable G := by
    dsimp [G]
    exact (hk.comp measurable_fst).mul
      ((hψ.continuous_deriv le_rfl).measurable.comp (by fun_prop))
  have hFrot : (∫ p, F p ∂(γ.prod γ)) = ∫ p, F (R p) ∂(γ.prod γ) := by
    have hm : AEStronglyMeasurable F ((γ.prod γ).map R) := by
      rw [hmap]
      exact hFmeas.aestronglyMeasurable
    have hi := integral_map (μ := γ.prod γ) (φ := R) (by fun_prop) hm
    rwa [hmap] at hi
  have hGrot : (∫ p, G p ∂(γ.prod γ)) = ∫ p, G (R p) ∂(γ.prod γ) := by
    have hm : AEStronglyMeasurable G ((γ.prod γ).map R) := by
      rw [hmap]
      exact hGmeas.aestronglyMeasurable
    have hi := integral_map (μ := γ.prod γ) (φ := R) (by fun_prop) hm
    rwa [hmap] at hi
  have hleft : (∫ p : ℝ × ℝ,
      ψ p.1 * k (a * p.1 + b * p.2) * (-b * p.1 + a * p.2) ∂(γ.prod γ)) =
      ∫ p, F p ∂(γ.prod γ) := by
    calc
      _ = ∫ p, F (R p) ∂(γ.prod γ) := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro p
        change ψ p.1 * k (a * p.1 + b * p.2) * (-b * p.1 + a * p.2) =
          k (a * p.1 + b * p.2) *
            ((-b * p.1 + a * p.2) *
              ψ (a * (a * p.1 + b * p.2) - b * (-b * p.1 + a * p.2)))
        rw [hinv]
        ring
      _ = ∫ p, F p ∂(γ.prod γ) := hFrot.symm
  have hright : (∫ p : ℝ × ℝ,
      deriv ψ p.1 * k (a * p.1 + b * p.2) ∂(γ.prod γ)) =
      ∫ p, G p ∂(γ.prod γ) := by
    calc
      _ = ∫ p, G (R p) ∂(γ.prod γ) := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro p
        change deriv ψ p.1 * k (a * p.1 + b * p.2) =
          k (a * p.1 + b * p.2) *
            deriv ψ (a * (a * p.1 + b * p.2) - b * (-b * p.1 + a * p.2))
        rw [hinv]
        ring
      _ = ∫ p, G p ∂(γ.prod γ) := hGrot.symm
  have hstein (z : ℝ) :
      (∫ v, v * ψ (a * z - b * v) ∂γ) =
        -b * ∫ v, deriv ψ (a * z - b * v) ∂γ := by
    let h : ℝ → ℝ := fun v => ψ (a * z - b * v)
    have hC1 : ContDiff ℝ 1 h := by
      exact hψ.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
    have hd (v : ℝ) : deriv h v = -b * deriv ψ (a * z - b * v) := by
      have hinner : HasDerivAt (fun w : ℝ => a * z - b * w) (-b) v := by
        have hi := ((hasDerivAt_id v).const_mul b).neg.const_add (a * z)
        convert hi using 1
        · funext w; dsimp; ring
        · ring
      have hh := ((hψ.differentiable (by simp)).differentiableAt.hasDerivAt).comp v hinner
      change deriv (ψ ∘ (fun w : ℝ => a * z - b * w)) v = _
      simpa [mul_comm] using hh.deriv
    have hb : ∀ v, |h v| ≤ A := fun v => hψ_bd _
    have hdb : ∀ v, |deriv h v| ≤ |b| * C := by
      intro v
      rw [hd v, abs_mul]
      simpa only [abs_neg] using
        (mul_le_mul_of_nonneg_left (hψ'_bd _) (abs_nonneg b))
    have hs := GaussianSteinBounded.stein_identity hC1 hb hdb
    have heq : (fun v => deriv h v) = (fun v => -b * deriv ψ (a * z - b * v)) :=
      funext hd
    rw [heq, integral_const_mul] at hs
    exact hs.symm
  have hpair : (∫ p, F p ∂(γ.prod γ)) = -b * ∫ p, G p ∂(γ.prod γ) := by
    have hpoint (z : ℝ) :
        (∫ v, k z * (v * ψ (a * z - b * v)) ∂γ) =
          -b * ∫ v, k z * deriv ψ (a * z - b * v) ∂γ := by
      rw [integral_const_mul, integral_const_mul, hstein z]
      ring
    dsimp [F, G]
    rw [integral_prod _ hFL, integral_prod _ hFR]
    simp_rw [hpoint]
    rw [integral_const_mul]
  rw [hleft, hright]
  exact hpair
end OperatorDerivativeRewrite.Foundation.GaussianRotationStein
