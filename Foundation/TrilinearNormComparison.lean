import Foundation.SpectralEnergyInterpolation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent tests of the scalar norm reduction in the incoming energy-flux corollary. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.TrilinearNormComparison
open SpectralEnergyInterpolation
set_option backward.isDefEq.respectTransparency false

def intermediate (A B : ℝ) : ℝ := A^((3:ℝ)/2)*B^((3:ℝ)/2)
def target (A B : ℝ) : ℝ := A^2*B

theorem three_halves_eq {x : ℝ} (hx : 0<x) : x^((3:ℝ)/2)=x*Real.sqrt x := by
  rw [show (3:ℝ)/2=1+1/2 by norm_num, Real.rpow_add hx,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem reduction_iff {A B C : ℝ} (hA : 0<A) (hB : 0<B) (hC : 0≤C) :
    intermediate A B≤C*target A B ↔ B≤C^2*A := by
  have hroot : (Real.sqrt A*Real.sqrt B)^2=A*B := by
    rw [mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
  have hi : intermediate A B=A*B*(Real.sqrt A*Real.sqrt B) := by
    rw [intermediate, three_halves_eq hA, three_halves_eq hB]
    ring
  have ht : C*target A B=A*B*(C*A) := by unfold target; ring
  rw [hi, ht]
  constructor
  · intro hh
    have hc := le_of_mul_le_mul_of_pos_left hh (mul_pos hA hB)
    have hs := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg hC hA.le)).mpr hc
    rw [hroot] at hs
    have hm : A*B≤A*(C^2*A) := by nlinarith [hs]
    exact le_of_mul_le_mul_of_pos_left hm hA
  · intro hh
    have hm := mul_le_mul_of_nonneg_left hh hA.le
    have hs : (Real.sqrt A*Real.sqrt B)^2≤(C*A)^2 := by rw [hroot]; nlinarith [hm]
    have hc := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg hC hA.le)).mp hs
    exact mul_le_mul_of_nonneg_left hc (mul_pos hA hB).le

theorem factor_one_iff {A B : ℝ} (hA : 0<A) (hB : 0<B) :
    intermediate A B≤target A B ↔ B≤A := by
  simpa using (reduction_iff hA hB (by norm_num : (0:ℝ)≤1))

theorem under_order_iff_equal {A B : ℝ} (hA : 0<A) (hB : 0<B) (hAB : A≤B) :
    intermediate A B≤target A B ↔ A=B := by
  rw [factor_one_iff hA hB]
  exact ⟨fun hh => le_antisymm hAB hh, fun hh => hh.symm.le⟩

theorem strict_failure {A B : ℝ} (hA : 0<A) (hAB : A<B) : target A B < intermediate A B := by
  have hB := hA.trans hAB
  exact lt_of_not_ge (fun hh => (not_le_of_gt hAB) ((factor_one_iff hA hB).mp hh))

theorem intermediate_one_four : intermediate 1 4=8 := by
  rw [intermediate, three_halves_eq (by norm_num : (0:ℝ)<1),
    three_halves_eq (by norm_num : (0:ℝ)<4)]
  norm_num

def criticalNorm {ι : Type*} (s : Finset ι) (w a : ι → ℝ) : ℝ := Real.sqrt (moment s w a 1)
def dissipativeNorm {ι : Type*} (s : Finset ι) (w a : ι → ℝ) : ℝ := Real.sqrt (moment s w a 3)
def exampleFrequency (_i : Fin 1) : ℝ := 4
def exampleAmplitude (_i : Fin 1) : ℝ := 1/2

theorem example_moments :
    moment Finset.univ exampleFrequency exampleAmplitude 0=1/4 ∧
      moment Finset.univ exampleFrequency exampleAmplitude 1=1 ∧
      moment Finset.univ exampleFrequency exampleAmplitude 2=4 ∧
      moment Finset.univ exampleFrequency exampleAmplitude 3=16 := by
  norm_num [moment, exampleFrequency, exampleAmplitude, Fin.sum_univ_succ]

theorem example_norms : criticalNorm Finset.univ exampleFrequency exampleAmplitude=1 ∧
    dissipativeNorm Finset.univ exampleFrequency exampleAmplitude=4 := by
  unfold criticalNorm dissipativeNorm
  rw [example_moments.2.1, example_moments.2.2.2]
  norm_num

theorem exact_spectral_counterexample :
    criticalNorm Finset.univ exampleFrequency exampleAmplitude≤
      dissipativeNorm Finset.univ exampleFrequency exampleAmplitude ∧
    intermediate (criticalNorm Finset.univ exampleFrequency exampleAmplitude)
      (dissipativeNorm Finset.univ exampleFrequency exampleAmplitude)=8 ∧
    target (criticalNorm Finset.univ exampleFrequency exampleAmplitude)
      (dissipativeNorm Finset.univ exampleFrequency exampleAmplitude)=4 := by
  rw [example_norms.1, example_norms.2, intermediate_one_four]
  norm_num [target]

theorem two_test_norms_differ :
    criticalNorm Finset.univ exampleFrequency
      (fun i => Real.sqrt (exampleFrequency i)*exampleAmplitude i)=2 ∧
    criticalNorm Finset.univ exampleFrequency
      (fun i => exampleFrequency i*exampleAmplitude i)=4 := by
  unfold criticalNorm
  rw [moment_sqrt_multiplier Finset.univ exampleFrequency exampleAmplitude 1
    (by intro i hi; norm_num [exampleFrequency]), derivative_test_energy,
    example_moments.2.2.1, example_moments.2.2.2]
  norm_num

def familyFrequency (L : ℝ) (_i : Fin 1) : ℝ := L^2
def familyAmplitude (L : ℝ) (_i : Fin 1) : ℝ := 1/L

theorem family_moments {L : ℝ} (hL : 0<L) :
    moment Finset.univ (familyFrequency L) (familyAmplitude L) 0=1/L^2 ∧
      moment Finset.univ (familyFrequency L) (familyAmplitude L) 1=1 ∧
      moment Finset.univ (familyFrequency L) (familyAmplitude L) 3=L^4 := by
  constructor
  · norm_num [moment, familyFrequency, familyAmplitude, Fin.sum_univ_succ]
  · constructor
    · norm_num [moment, familyFrequency, familyAmplitude, Fin.sum_univ_succ]
      field_simp [hL.ne']
    · norm_num [moment, familyFrequency, familyAmplitude, Fin.sum_univ_succ]
      field_simp [hL.ne']

theorem family_norms {L : ℝ} (hL : 0<L) :
    criticalNorm Finset.univ (familyFrequency L) (familyAmplitude L)=1 ∧
      dissipativeNorm Finset.univ (familyFrequency L) (familyAmplitude L)=L^2 := by
  unfold criticalNorm dissipativeNorm
  rw [(family_moments hL).2.1, (family_moments hL).2.2]
  constructor
  · norm_num
  · rw [show L^4=(L^2)^2 by ring, Real.sqrt_sq (sq_nonneg L)]

theorem no_uniform_factor (C : ℝ) (hC : 0≤C) :
    ∃ L : ℝ, 1≤L ∧ (∀ i : Fin 1, 1≤familyFrequency L i) ∧
      moment Finset.univ (familyFrequency L) (familyAmplitude L) 0≤1 ∧
      criticalNorm Finset.univ (familyFrequency L) (familyAmplitude L)≤
        dissipativeNorm Finset.univ (familyFrequency L) (familyAmplitude L) ∧
      C*target (criticalNorm Finset.univ (familyFrequency L) (familyAmplitude L))
        (dissipativeNorm Finset.univ (familyFrequency L) (familyAmplitude L))<
      intermediate (criticalNorm Finset.univ (familyFrequency L) (familyAmplitude L))
        (dissipativeNorm Finset.univ (familyFrequency L) (familyAmplitude L)) := by
  let L := C+1
  have hL1 : 1≤L := by dsimp [L]; linarith
  have hL : 0<L := by linarith
  have hLs : 1≤L^2 := by nlinarith
  refine ⟨L, hL1, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hLs
  · rw [(family_moments hL).1]
    exact (div_le_one (sq_pos_of_pos hL)).mpr hLs
  · rw [(family_norms hL).1, (family_norms hL).2]
    exact hLs
  · rw [(family_norms hL).1, (family_norms hL).2]
    apply lt_of_not_ge
    intro hh
    have hb := (reduction_iff (by norm_num : (0:ℝ)<1) (sq_pos_of_pos hL) hC).mp hh
    dsimp [L] at hb
    nlinarith

theorem no_universal_constant :
    ¬∃ C : ℝ, 0≤C ∧ ∀ L : ℝ, 1≤L →
      intermediate (criticalNorm Finset.univ (familyFrequency L) (familyAmplitude L))
        (dissipativeNorm Finset.univ (familyFrequency L) (familyAmplitude L))≤
      C*target (criticalNorm Finset.univ (familyFrequency L) (familyAmplitude L))
        (dissipativeNorm Finset.univ (familyFrequency L) (familyAmplitude L)) := by
  rintro ⟨C, hC, hh⟩
  obtain ⟨L, hL, hw, hK, hAB, hbad⟩ := no_uniform_factor C hC
  exact (not_le_of_gt hbad) (hh L hL)

theorem reduction_iff_ratio {A B C : ℝ} (hA : 0<A) (hB : 0<B) (hC : 0≤C) :
    intermediate A B≤C*target A B ↔ B/A≤C^2 := by
  rw [reduction_iff hA hB hC, div_le_iff₀ hA]

theorem spectral_factor_iff_frequency {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hE : 0<moment s w a 1) (hD : 0<moment s w a 3) (C : ℝ) (hC : 0≤C) :
    intermediate (criticalNorm s w a) (dissipativeNorm s w a)≤
      C*target (criticalNorm s w a) (dissipativeNorm s w a) ↔
      Real.sqrt (moment s w a 3/moment s w a 1)≤C^2 := by
  unfold criticalNorm dissipativeNorm
  rw [reduction_iff_ratio (Real.sqrt_pos.mpr hE) (Real.sqrt_pos.mpr hD) hC]
  rw [Real.sqrt_div hD.le]

theorem frequency_capped_reduction {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hE : 0<moment s w a 1) (hD : 0<moment s w a 3) (L : ℝ) (hL : 0≤L)
    (hfreq : Real.sqrt (moment s w a 3/moment s w a 1)≤L) :
    intermediate (criticalNorm s w a) (dissipativeNorm s w a)≤
      Real.sqrt L*target (criticalNorm s w a) (dissipativeNorm s w a) := by
  apply (spectral_factor_iff_frequency s w a hE hD (Real.sqrt L) (Real.sqrt_nonneg L)).mpr
  rw [Real.sq_sqrt hL]
  exact hfreq

end OperatorDerivativeRewrite.Foundation.TrilinearNormComparison
