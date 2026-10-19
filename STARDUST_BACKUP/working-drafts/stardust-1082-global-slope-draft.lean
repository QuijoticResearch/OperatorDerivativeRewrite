import Foundation.IBMSchwartzPhysicalSlope
noncomputable section
open MeasureTheory
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian IBMCorrectionStein IBMShiftedJetMoments
open IBMSchwartzSourceDerivative IBMSchwartzPhysicalPrimitive IBMPhysicalDerivativeKernel
open IBMSchwartzPhysicalFirstKernel IBMPhysicalNoiseRealization IBMPhysicalNoiseCalculus
open IBMGaussianSteinMoments IBMPhysicalNoiseClock GaussianTimeHilbert
namespace DraftGlobalSlope
theorem jet_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u : CoefficientSpace) :
    |M g a u (j+1) 0| * ‖u‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g j) := by
  have hc (f : GaussianL2) :
      ‖firstChaosEmbedding.toContinuousLinearMap.adjoint f‖ ≤ ‖f‖ := by
    calc
      _ ≤ ‖firstChaosEmbedding.toContinuousLinearMap.adjoint‖*‖f‖ :=
        firstChaosEmbedding.toContinuousLinearMap.adjoint.le_opNorm f
      _ = ‖firstChaosEmbedding.toContinuousLinearMap‖*‖f‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right
        firstChaosEmbedding.norm_toContinuousLinearMap_le (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  have h := (hc (observable g a j u)).trans (observable_bound g a j u)
  rw [observable_adjoint, norm_smul, Real.norm_eq_abs] at h
  exact h

theorem translated_norm (ρ : ℝ → ℝ) (hc : Continuous ρ) (hs : HasCompactSupport ρ) (x : ℝ) :
    ‖translatedClass ρ hc hs x‖ = (eLpNorm ρ 2 volume).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (translatedClass_coeFn ρ hc hs x)]
  change (eLpNorm (ρ ∘ fun w : ℝ => x-w) 2 volume).toReal = _
  rw [eLpNorm_comp_measurePreserving hc.aestronglyMeasurable
    (volume.measurePreserving_sub_left x)]

theorem slope_global_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖slope g a n r‖ ≤ C := by
  let A1 : ℝ := SchwartzMap.seminorm ℝ 0 0 (jet g 1)
  let A2 : ℝ := SchwartzMap.seminorm ℝ 0 0 (jet g 2)
  let B : ℝ := (eLpNorm (IBMMollifier.kernel n) 2 volume).toReal
  refine ⟨A2+A1*B, by positivity, fun r => ?_⟩
  have hn : ‖physicalJet n r 0‖ = ‖tripleCoefficient n r 0‖ := by
    rw [← physicalToCoefficient.norm_map (physicalJet n r 0),
      physicalJet, triple_coefficient_physical]
  have h1 : ‖physicalJet n r 1‖ = B := by
    change ‖convolutionKernel (deriv (IBMMollifier.kernel n)) r‖ = B
    rw [derivative_eq_translated ((IBMMollifier.kernel_smooth n).of_le (by norm_num))
      (IBMMollifier.kernel_compactSupport n)]
    exact translated_norm _ _ _ _
  have hc : |inner ℝ (tripleCoefficient n r 0) (tripleCoefficient n r 1)| ≤ 1 :=
    IBMSchwartzPhysicalSlope.covariance_bound n r
  have hj : |M g a (tripleCoefficient n r 0) 3 0| * ‖physicalJet n r 0‖ ≤ A2 := by
    rw [hn]
    exact jet_bound g a 2 _
  have hm : |M g a (tripleCoefficient n r 0) 1 0| ≤ A1 :=
    IBMSchwartzPhysicalSlope.mean_bound g a 1 _
  rw [slope_eq]
  calc
    _ ≤ ‖(inner ℝ (tripleCoefficient n r 0) (tripleCoefficient n r 1)*
        M g a (tripleCoefficient n r 0) 3 0) • physicalJet n r 0‖+
        ‖M g a (tripleCoefficient n r 0) 1 0 • physicalJet n r 1‖ := norm_add_le _ _
    _ = |inner ℝ (tripleCoefficient n r 0) (tripleCoefficient n r 1)| *
        (|M g a (tripleCoefficient n r 0) 3 0| * ‖physicalJet n r 0‖)+
        |M g a (tripleCoefficient n r 0) 1 0| * B := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, h1]
      ring
    _ ≤ 1*A2+A1*B := add_le_add (mul_le_mul hc hj (by positivity) (by norm_num))
      (mul_le_mul_of_nonneg_right hm ENNReal.toReal_nonneg)
    _ = A2+A1*B := by ring
theorem curvature_global_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖curvatureKernel g a n r‖ ≤ C := by
  obtain ⟨K,hK⟩ := (IBMMollifier.kernel_smooth n).continuous.norm.bddAbove_range_of_hasCompactSupport
    (IBMMollifier.kernel_compactSupport n).norm
  have hK0 : 0 ≤ K := (norm_nonneg (IBMMollifier.kernel n 0)).trans (hK ⟨0,rfl⟩)
  let A (j : ℕ) : ℝ := SchwartzMap.seminorm ℝ 0 0 (jet g j)
  let B0 : ℝ := (eLpNorm (IBMMollifier.kernel n) 2 volume).toReal
  let B1 : ℝ := (eLpNorm (deriv (IBMMollifier.kernel n)) 2 volume).toReal
  refine ⟨K*A 2+A 4+2*A 3*B0+A 1*B1, by positivity, fun r => ?_⟩
  let u := tripleCoefficient n r 0
  let v := tripleCoefficient n r 1
  let w := tripleCoefficient n r 2
  let d := inner ℝ u v
  let q := ‖v‖^2+inner ℝ u w
  have hn : ‖physicalJet n r 0‖ = ‖u‖ := by
    rw [← physicalToCoefficient.norm_map (physicalJet n r 0),
      physicalJet, triple_coefficient_physical]
  have hv : ‖physicalJet n r 1‖ = B0 := by
    change ‖convolutionKernel (deriv (IBMMollifier.kernel n)) r‖ = B0
    rw [derivative_eq_translated ((IBMMollifier.kernel_smooth n).of_le (by norm_num))
      (IBMMollifier.kernel_compactSupport n)]
    exact translated_norm _ _ _ _
  have hw : ‖physicalJet n r 2‖ = B1 := by
    change ‖convolutionKernel (deriv (deriv (IBMMollifier.kernel n))) r‖ = B1
    rw [derivative_eq_translated
      (((IBMMollifier.kernel_smooth n).of_le (by norm_num) :
        ContDiff ℝ 2 (IBMMollifier.kernel n)).deriv' (n := 1))
      (IBMMollifier.kernel_compactSupport n).deriv]
    exact translated_norm _ _ _ _
  have hd : |d| ≤ 1 := IBMSchwartzPhysicalSlope.covariance_bound n r
  have hd2 : |d|^2 ≤ 1 := by nlinarith [abs_nonneg d]
  have hq : |q| ≤ K := by
    change |‖tripleCoefficient n r 1‖^2+
      inner ℝ (tripleCoefficient n r 0) (tripleCoefficient n r 2)| ≤ K
    rw [IBMOriginalBoundaryResidual.actual_bracket]
    exact hK ⟨r,rfl⟩
  have hj3 : |M g a u 3 0| * ‖physicalJet n r 0‖ ≤ A 2 := by
    rw [hn]; exact jet_bound g a 2 u
  have hj5 : |M g a u 5 0| * ‖physicalJet n r 0‖ ≤ A 4 := by
    rw [hn]; exact jet_bound g a 4 u
  have hm3 : |M g a u 3 0| ≤ A 3 := IBMSchwartzPhysicalSlope.mean_bound g a 3 u
  have hm1 : |M g a u 1 0| ≤ A 1 := IBMSchwartzPhysicalSlope.mean_bound g a 1 u
  have ht0 : ‖(q*M g a u 3 0+d^2*M g a u 5 0) • physicalJet n r 0‖ ≤ K*A 2+A 4 := by
    rw [add_smul]
    calc
      _ ≤ ‖(q*M g a u 3 0) • physicalJet n r 0‖+
        ‖(d^2*M g a u 5 0) • physicalJet n r 0‖ := norm_add_le _ _
      _ = |q| * (|M g a u 3 0| * ‖physicalJet n r 0‖)+
        |d|^2*(|M g a u 5 0| * ‖physicalJet n r 0‖) := by
        simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow]; ring
      _ ≤ K*A 2+1*A 4 := add_le_add (mul_le_mul hq hj3 (by positivity) hK0)
        (mul_le_mul hd2 hj5 (by positivity) (by norm_num))
      _ = _ := by ring
  have ht1 : ‖(2*d*M g a u 3 0) • physicalJet n r 1‖ ≤ 2*A 3*B0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, hv]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh : 2*|d| * |M g a u 3 0| ≤ 2*A 3 := by
      calc
        _ ≤ (2*1)*A 3 := mul_le_mul
          (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2)) hm3
          (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right hh ENNReal.toReal_nonneg
  have ht2 : ‖M g a u 1 0 • physicalJet n r 2‖ ≤ A 1*B1 := by
    rw [norm_smul, Real.norm_eq_abs, hw]
    exact mul_le_mul_of_nonneg_right hm1 ENNReal.toReal_nonneg
  change ‖(q*M g a u 3 0+d^2*M g a u 5 0) • physicalJet n r 0+
    (2*d*M g a u 3 0) • physicalJet n r 1+M g a u 1 0 • physicalJet n r 2‖ ≤ _
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add ht0 ht1)) ht2)

end DraftGlobalSlope
