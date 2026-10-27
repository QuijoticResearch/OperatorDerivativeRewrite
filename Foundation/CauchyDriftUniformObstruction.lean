import Foundation.CauchySineDrift
import Foundation.FiniteFourierTorusAverage

/-! Actual circle-integral obstruction to the uniform-measure drift energy
Poincare claim. The finite drifted Gamma identity remains valid. -/
namespace OperatorDerivativeRewrite.Foundation.CauchyDriftUniformObstruction
open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
open FiniteStableGamma.Core CauchySineDrift

theorem zero_wave : (![0,0,0] : Wave) = 0 := by
  ext i
  fin_cases i <;> rfl

noncomputable def witness : Fourier :=
  AddMonoidAlgebra.single 0 2 + AddMonoidAlgebra.single unitWave (1/2) +
    AddMonoidAlgebra.single (-unitWave) (1/2)

noncomputable def driftGenerator (f : Fourier) : Fourier :=
  generator (stableSymbol 1) f + transport f

theorem witness_synthesis (x : Space) : synthesis x witness = 2 + (Real.cos (x 0) : ℂ) := by
  have hw : witness = AddMonoidAlgebra.single 0 2 + cosineMultiplier := by
    simp only [witness, cosineMultiplier, smul_add, AddMonoidAlgebra.smul_single,
      smul_eq_mul, mul_one]
    abel
  rw [hw, map_add, synthesis_single, character_zero, mul_one, cosineMultiplier_synthesis]

theorem witness_mean : constantTrace witness = 2 := by
  norm_num [constantTrace_apply, witness, unitWave]

theorem drift_mean : constantTrace (driftGenerator witness) = (1/2 : ℂ) := by
  norm_num [driftGenerator, witness, map_add, generator_single, transport_add,
    transport_single, stableSymbol, constantTrace_apply, unitWave, zero_wave]

theorem witness_square_mean : constantTrace (witness*witness) = (9/2 : ℂ) := by
  norm_num [witness, add_mul, mul_add, AddMonoidAlgebra.single_mul_single,
    constantTrace_apply, unitWave, zero_wave]

theorem witness_energy : -constantTrace (witness*driftGenerator witness) = (-1/2 : ℂ) := by
  norm_num [driftGenerator, witness, map_add, generator_single, transport_add,
    transport_single, stableSymbol, add_mul, mul_add, mul_sub,
    AddMonoidAlgebra.single_mul_single, constantTrace_apply, unitWave, zero_wave]

theorem witness_circle_mean (x : Space) :
    circleAverage 0 (fun y => synthesis y witness) x = 2 := by
  rw [circleAverage_synthesis]
  norm_num [witness, map_add, cut_single, synthesis_single, unitWave, character_zero]

theorem drift_circle_mean (x : Space) :
    circleAverage 0 (fun y => synthesis y (driftGenerator witness)) x = (1/2 : ℂ) := by
  rw [circleAverage_synthesis]
  norm_num [driftGenerator, witness, map_add, map_sub, generator_single,
    transport_add, transport_single, stableSymbol, cut_single, synthesis_single,
    unitWave, zero_wave, character_zero]

theorem witness_circle_square (x : Space) :
    circleAverage 0 (fun y => synthesis y witness * synthesis y witness) x = (9/2 : ℂ) := by
  simp only [← synthesis_mul]
  rw [circleAverage_synthesis]
  norm_num [witness, add_mul, mul_add, AddMonoidAlgebra.single_mul_single,
    map_add, cut_single, synthesis_single, unitWave, zero_wave, character_zero]

theorem witness_circle_energy (x : Space) :
    -circleAverage 0 (fun y => synthesis y witness * synthesis y (driftGenerator witness)) x =
      (-1/2 : ℂ) := by
  simp only [← synthesis_mul]
  rw [circleAverage_synthesis]
  norm_num [driftGenerator, witness, map_add, map_sub, generator_single,
    transport_add, transport_single, stableSymbol, add_mul, mul_add, mul_sub,
    AddMonoidAlgebra.single_mul_single, cut_single, synthesis_single,
    unitWave, zero_wave, character_zero]

theorem uniform_not_invariant (x : Space) :
    ¬ (∀ f : Fourier, circleAverage 0 (fun y => synthesis y (driftGenerator f)) x = 0) := by
  intro h
  have he := h witness
  rw [drift_circle_mean] at he
  norm_num at he

theorem witness_poincare_failure (x : Space) :
    ¬ ((circleAverage 0 (fun y => synthesis y witness * synthesis y witness) x).re -
      (circleAverage 0 (fun y => synthesis y witness) x).re ^ 2 ≤
      2 * (-circleAverage 0
        (fun y => synthesis y witness * synthesis y (driftGenerator witness)) x).re) := by
  rw [witness_circle_square, witness_circle_mean, witness_circle_energy]
  norm_num

theorem witness_real (x : Space) : (synthesis x witness).im = 0 := by
  rw [witness_synthesis]
  simp

theorem witness_no_nonnegative_constant (x : Space) (C : ℝ) (hC : 0 ≤ C) :
    ¬ ((circleAverage 0 (fun y => synthesis y witness * synthesis y witness) x).re -
      (circleAverage 0 (fun y => synthesis y witness) x).re ^ 2 ≤
      C * (-circleAverage 0
        (fun y => synthesis y witness * synthesis y (driftGenerator witness)) x).re) := by
  rw [witness_circle_square, witness_circle_mean, witness_circle_energy]
  norm_num
  linarith

theorem no_uniform_poincare (x : Space) (C : ℝ) (hC : 0 ≤ C) :
    ¬ (∀ f : Fourier, (∀ y : Space, (synthesis y f).im = 0) →
      (circleAverage 0 (fun y => synthesis y f * synthesis y f) x).re -
        (circleAverage 0 (fun y => synthesis y f) x).re ^ 2 ≤
        C * (-circleAverage 0
          (fun y => synthesis y f * synthesis y (driftGenerator f)) x).re) := by
  intro h
  exact witness_no_nonnegative_constant x C hC (h witness witness_real)

end OperatorDerivativeRewrite.Foundation.CauchyDriftUniformObstruction
