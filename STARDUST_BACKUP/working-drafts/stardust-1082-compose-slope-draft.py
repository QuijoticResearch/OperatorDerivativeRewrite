from pathlib import Path
r=Path('C:/OperatorDerivativeRewrite')
a=(r/'.lake/stardust-1082-first-jet-bound-draft.lean').read_text().split('example ',1)[1]
b=(r/'.lake/stardust-1082-translated-norm-draft.lean').read_text().split('example ',1)[1]
s='''import Foundation.IBMSchwartzPhysicalSlope
noncomputable section
open MeasureTheory
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian IBMCorrectionStein IBMShiftedJetMoments
open IBMSchwartzSourceDerivative IBMSchwartzPhysicalPrimitive IBMPhysicalDerivativeKernel
open IBMSchwartzPhysicalFirstKernel IBMPhysicalNoiseRealization IBMPhysicalNoiseCalculus
open IBMGaussianSteinMoments IBMPhysicalNoiseClock GaussianTimeHilbert
namespace DraftGlobalSlope
theorem jet_bound '''+a+'\ntheorem translated_norm '+b+'''
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
end DraftGlobalSlope
'''
(r/'.lake/stardust-1082-global-slope-draft.lean').write_text(s,encoding='utf-8')
