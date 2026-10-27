import Foundation.CauchyDriftUniformObstruction

/-! Actual Cauchy cubic diffusion-chain obstruction. The cosine witness has
cubic remainder -3/2 at zero. Adding any multiple of the sine derivation
preserves this remainder. This refutes a diffusion hypothesis, not a separate
model-specific logarithmic Sobolev inequality. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyDiffusionChainObstruction
open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteStableGamma.Core
open CauchySineDrift CauchyDriftUniformObstruction

def cubicDefect (L : Fourier → Fourier) (f : Fourier) : Fourier :=
  L (f*f*f) - (3 : ℂ) • (f*L (f*f)) + (3 : ℂ) • (f*f*L f)

theorem drift_cubic_cancellation (f : Fourier) : cubicDefect transport f = 0 := by
  simp only [cubicDefect, transport_product, Algebra.smul_def, map_ofNat]
  ring

theorem cubicDefect_drift (r : ℝ) (f : Fourier) :
    cubicDefect (fun p => generator (stableSymbol 1) p + r • transport p) f =
      cubicDefect (generator (stableSymbol 1)) f := by
  simp only [cubicDefect, transport_product, Algebra.smul_def, map_ofNat]
  ring

theorem cosine_generator_at_zero :
    synthesis 0 (generator (stableSymbol 1) cosineMultiplier) = -1 := by
  norm_num [cosineMultiplier, smul_add, AddMonoidAlgebra.smul_single,
    map_add, generator_single, synthesis_single, character, phase, stableSymbol, unitWave]

theorem cosine_square_generator_at_zero :
    synthesis 0 (generator (stableSymbol 1) (cosineMultiplier*cosineMultiplier)) = -1 := by
  norm_num [cosineMultiplier, smul_add, AddMonoidAlgebra.smul_single,
    add_mul, mul_add, AddMonoidAlgebra.single_mul_single,
    map_add, generator_single, synthesis_single, character, phase, stableSymbol, unitWave]

theorem cosine_cube_generator_at_zero :
    synthesis 0 (generator (stableSymbol 1)
      (cosineMultiplier*cosineMultiplier*cosineMultiplier)) = (-3/2 : ℂ) := by
  norm_num [cosineMultiplier, smul_add, AddMonoidAlgebra.smul_single,
    add_mul, mul_add, AddMonoidAlgebra.single_mul_single,
    map_add, generator_single, synthesis_single, character, phase, stableSymbol, unitWave]

theorem cauchy_cubic_defect :
    synthesis 0 (cubicDefect (generator (stableSymbol 1)) cosineMultiplier) = (-3/2 : ℂ) := by
  simp [cubicDefect, synthesis_mul, cosineMultiplier_synthesis,
    cosine_generator_at_zero, cosine_square_generator_at_zero, cosine_cube_generator_at_zero]

theorem cosine_gamma_at_zero :
    synthesis 0 (gammaIter (stableSymbol 1) 1 cosineMultiplier cosineMultiplier) = (1/2 : ℂ) := by
  norm_num [cosineMultiplier, smul_add, AddMonoidAlgebra.smul_single,
    gammaIter_add_left, gammaIter_add_right, gammaIter_single,
    map_add, map_ofNat, map_div₀, synthesis_single, character, phase, kernel, stableSymbol, unitWave]

theorem cauchy_diffusion_chain_failure :
    synthesis 0 (generator (stableSymbol 1) (cosineMultiplier*cosineMultiplier*cosineMultiplier)) ≠
      3*(synthesis 0 cosineMultiplier)^2 * synthesis 0 (generator (stableSymbol 1) cosineMultiplier) +
      6*synthesis 0 cosineMultiplier * synthesis 0
        (gammaIter (stableSymbol 1) 1 cosineMultiplier cosineMultiplier) := by
  rw [cosine_cube_generator_at_zero, cosine_generator_at_zero, cosine_gamma_at_zero,
    cosineMultiplier_synthesis]
  norm_num

theorem drifted_cubic_defect (r : ℝ) :
    synthesis 0 (cubicDefect (fun p => generator (stableSymbol 1) p + r • transport p)
      cosineMultiplier) = (-3/2 : ℂ) := by
  rw [cubicDefect_drift, cauchy_cubic_defect]

theorem drifted_cubic_nonzero (r : ℝ) :
    cubicDefect (fun p => generator (stableSymbol 1) p + r • transport p)
      cosineMultiplier ≠ 0 := by
  intro hz
  have he := drifted_cubic_defect r
  rw [hz, map_zero] at he
  norm_num at he

end OperatorDerivativeRewrite.Foundation.CauchyDiffusionChainObstruction
