import Foundation.PhysicalHeatCovarianceNonmonotonicity
import Foundation.FourierGammaCovariance

/-!
# Sharp zero curvature on the quadratic torus Fourier core

The ordinary one-coordinate quadratic heat symbol has nonnegative second
Gamma iteration by the existing covariance-power theorem. A real sine mode
has first Gamma value `4` and second Gamma value `0` at the torus origin,
so no strictly positive pointwise `Γ₂ ≥ ρ Γ` bound holds on this core.
This separates the finite-time covariance nonmonotonicity of the preceding
module from the generator's actual flat curvature; it does not assert any
completed generator-domain or physical-process curvature theorem.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
open FiniteFourierReality
open FiniteStableGamma.Core FiniteStableGamma.ComplexEnergy
open FourierGammaCovariance PhysicalHeatCovarianceNonmonotonicity

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatFlatCurvature

private def sineWave : Wave := ka
private def sineWeights : Fin 2 → ℂ := ![Complex.I, -Complex.I]
private def sineWaves : Fin 2 → Wave := ![sineWave, -sineWave]
def sineMode : Fourier :=
  ∑ i : Fin 2, AddMonoidAlgebra.single (sineWaves i) (sineWeights i)

theorem sineMode_gamma_one :
    (synthesis 0 (gammaIter (fun k => (quadRate k : ℝ)) 1 sineMode sineMode)).re = 4 := by
  rw [sineMode, gamma_energy]
  norm_num [energy, Fin.sum_univ_two, sineWaves, sineWeights, sineWave,
    quadRate, ka, kernel, character, phase, Pi.single_apply]

theorem sineMode_gamma_two :
    (synthesis 0 (gammaIter (fun k => (quadRate k : ℝ)) 2 sineMode sineMode)).re = 0 := by
  rw [sineMode, gamma_energy]
  norm_num [energy, Fin.sum_univ_two, sineWaves, sineWeights, sineWave,
    quadRate, ka, kernel, character, phase, Pi.single_apply]

theorem sineMode_hermitian : Hermitian sineMode := by
  apply (hermitian_iff_reflection sineMode).mpr
  simp [sineMode, sineWaves, sineWeights, sineWave, Fin.sum_univ_two,
    reflection_single]
  abel

theorem quad_gamma_two_nonnegative (f : Fourier) (x : Space) :
    (synthesis x (gammaIter (fun k => (quadRate k : ℝ)) 2 f f)).im = 0 ∧
      0 ≤ (synthesis x (gammaIter (fun k => (quadRate k : ℝ)) 2 f f)).re := by
  exact gamma_nonnegative _ quadRate_covariance 2 f x

theorem no_positive_quad_curvature :
    ¬ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ f : Fourier, Hermitian f → ∀ x : Space,
        ρ * (synthesis x (gammaIter (fun k => (quadRate k : ℝ)) 1 f f)).re ≤
          (synthesis x (gammaIter (fun k => (quadRate k : ℝ)) 2 f f)).re := by
  rintro ⟨ρ, hρ, h⟩
  have hsite := h sineMode sineMode_hermitian 0
  rw [sineMode_gamma_one, sineMode_gamma_two] at hsite
  linarith

end OperatorDerivativeRewrite.Foundation.PhysicalHeatFlatCurvature
