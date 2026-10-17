import Foundation.SectorTransferSymmetry

/-! Transverse Fourier-symbol tests for the YM-NS dictionary. The common imaginary
Fourier factor is omitted; it cannot affect whether a coefficient vanishes. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.DictionaryTriadLocalization
open SectorTransferSymmetry
set_option backward.isDefEq.respectTransparency false

/-- The valid support implication: at least one input must exceed half the cutoff. -/
theorem high_output_has_large_input {E : Type*} [SeminormedAddCommGroup E]
    (k l : E) (K : ℝ) (hout : K < ‖k+l‖) :
    K/2 < ‖k‖ ∨ K/2 < ‖l‖ := by
  by_contra h
  push Not at h
  have ht := norm_add_le k l
  linarith

theorem low_low_exclusion {E : Type*} [SeminormedAddCommGroup E]
    (k l : E) (K : ℝ) (hk : ‖k‖ ≤ K/2) (hl : ‖l‖ ≤ K/2) :
    ¬ K < ‖k+l‖ := by
  intro hout
  rcases high_output_has_large_input k l K hout with h | h <;> linarith

def leray (m : Wave) (v : Vector) : Vector :=
  fun i => v i - dotWave m v / waveSquare m * (m i : ℝ)

theorem leray_of_transverse (m : Wave) (v : Vector) (hv : dotWave m v = 0) :
    leray m v = v := by
  ext i
  simp [leray, hv]

def coefficient (k l : Wave) (a b : Vector) : Vector :=
  fun i => dotWave l a * b i + dotWave k b * a i

def e2 : Vector := ![0,1,0]
def e3 : Vector := ![0,0,1]
def low : Wave := ![1,0,0]
def high (N : ℤ) : Wave := ![0,N,0]
def output (N : ℤ) : Wave := ![1,N,0]

theorem low_high_sum (N : ℤ) : low + high N = output N := by
  ext i
  fin_cases i <;> simp [low, high, output]

theorem low_high_transverse (N : ℤ) :
    dotWave low e2 = 0 ∧ dotWave (high N) e3 = 0 ∧
      dotWave (output N) e3 = 0 := by
  simp [dotWave, low, high, output, e2, e3, Fin.sum_univ_succ]

theorem low_high_coefficient (N : ℤ) :
    leray (output N) (coefficient low (high N) e2 e3) = (N : ℝ) • e3 := by
  ext i
  fin_cases i <;>
    simp [leray, coefficient, dotWave, low, high, output, e2, e3, Fin.sum_univ_succ]

theorem low_high_nonzero (N : ℤ) (hN : N ≠ 0) :
    leray (output N) (coefficient low (high N) e2 e3) ≠ 0 := by
  rw [low_high_coefficient]
  intro h
  have hh := congrFun h 2
  simp [e3] at hh
  exact hN (by exact_mod_cast hh)

theorem low_high_sizes (N : ℤ) : waveSquare low = 1 ∧
    waveSquare (high N) = (N : ℝ)^2 ∧ waveSquare (output N) = 1+(N : ℝ)^2 := by
  norm_num [waveSquare, low, high, output, Fin.sum_univ_succ]

theorem low_high_arbitrary_cutoff (N : ℤ) (hN : 4 ≤ N) :
    waveSquare low < ((N : ℝ)/2)^2 ∧
      (N : ℝ)^2 < waveSquare (output N) ∧
      leray (output N) (coefficient low (high N) e2 e3) ≠ 0 := by
  obtain ⟨hl, _, hm⟩ := low_high_sizes N
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨?_, ?_, low_high_nonzero N (by omega)⟩
  · rw [hl]
    nlinarith [sq_nonneg ((N : ℝ)-2)]
  · rw [hm]
    linarith

/-- At cutoff4, the frequency-one input affects an output above the cutoff. -/
theorem low_high_cutoff :
    waveSquare low < (4/2 : ℝ)^2 ∧ waveSquare (high 4) ≤ (4 : ℝ)^2 ∧
      (4 : ℝ)^2 < waveSquare (output 4) ∧
      leray (output 4) (coefficient low (high 4) e2 e3) ≠ 0 := by
  refine ⟨?_, ?_, ?_, low_high_nonzero 4 (by norm_num)⟩ <;>
    norm_num [waveSquare, low, high, output, Fin.sum_univ_succ]

def cancelLeft (N : ℤ) : Wave := ![N,0,0]
def cancelRight (N : ℤ) : Wave := ![1-N,1,0]
def fixedOutput : Wave := ![1,1,0]

theorem cancellation_sum (N : ℤ) : cancelLeft N + cancelRight N = fixedOutput := by
  ext i
  fin_cases i <;> simp [cancelLeft, cancelRight, fixedOutput]

theorem cancellation_transverse (N : ℤ) :
    dotWave (cancelLeft N) e2 = 0 ∧ dotWave (cancelRight N) e3 = 0 ∧
      dotWave fixedOutput e3 = 0 := by
  simp [dotWave, cancelLeft, cancelRight, fixedOutput, e2, e3, Fin.sum_univ_succ]

theorem cancellation_coefficient (N : ℤ) :
    leray fixedOutput (coefficient (cancelLeft N) (cancelRight N) e2 e3) = e3 := by
  ext i
  fin_cases i <;>
    simp [leray, coefficient, dotWave, cancelLeft, cancelRight, fixedOutput,
      e2, e3, Fin.sum_univ_succ]

theorem cancellation_sizes (N : ℤ) :
    waveSquare (cancelLeft N) = (N : ℝ)^2 ∧
      waveSquare (cancelRight N) = (1-(N : ℝ))^2+1 ∧ waveSquare fixedOutput = 2 := by
  norm_num [waveSquare, cancelLeft, cancelRight, fixedOutput, Fin.sum_univ_succ]

/-- No uniform input/output frequency ratio follows from triadic conservation,
even for transverse inputs and a nonzero projected advection coefficient. -/
theorem unbounded_input_ratio (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℤ, R^2 * waveSquare fixedOutput < waveSquare (cancelLeft N) ∧
      R^2 * waveSquare fixedOutput < waveSquare (cancelRight N) ∧
      leray fixedOutput (coefficient (cancelLeft N) (cancelRight N) e2 e3) ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_int_gt (2*R+2)
  obtain ⟨hl, hr, hm⟩ := cancellation_sizes N
  refine ⟨N, ?_, ?_, ?_⟩
  · rw [hl, hm]
    nlinarith [sq_nonneg ((N : ℝ)-2*R-2), sq_nonneg R]
  · rw [hr, hm]
    nlinarith [sq_nonneg ((N : ℝ)-2*R-2), sq_nonneg R]
  · rw [cancellation_coefficient]
    intro h
    have hh := congrFun h 2
    norm_num [e3] at hh

end OperatorDerivativeRewrite.Foundation.DictionaryTriadLocalization
