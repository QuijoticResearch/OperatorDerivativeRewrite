import Foundation.CorridorFiniteTimeExit
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Positive finite spectral moments, kinetic admissibility and derivative-test bookkeeping. -/
noncomputable section
open Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.SpectralEnergyInterpolation
set_option backward.isDefEq.respectTransparency false

def moment {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i∈s, (w i)^n*(a i)^2

theorem moment_nonneg {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (n : ℕ)
    (hw : ∀ i∈s, 0≤w i) : 0≤moment s w a n :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (pow_nonneg (hw i hi) n) (sq_nonneg _))

theorem kinetic_nonneg {ι : Type*} (s : Finset ι) (w a : ι → ℝ) : 0≤moment s w a 0 := by
  unfold moment
  simp only [pow_zero, one_mul]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem cauchy_moments_zero {ι : Type*} (s : Finset ι) (w a : ι → ℝ) :
    (moment s w a 1)^2≤moment s w a 0*moment s w a 2 := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq s a (fun i => w i*a i)
  have he : (∑ i∈s, a i*(w i*a i))=moment s w a 1 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [pow_one]
    ring
  have hk : (∑ i∈s, (a i)^2)=moment s w a 0 := by simp [moment]
  have hq : (∑ i∈s, (w i*a i)^2)=moment s w a 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rwa [he, hk, hq] at hh

theorem moment_sqrt_multiplier {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (n : ℕ)
    (hw : ∀ i∈s, 0≤w i) :
    moment s w (fun i => Real.sqrt (w i)*a i) n=moment s w a (n+1) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow, Real.sq_sqrt (hw i hi), pow_succ]
  ring

theorem cauchy_moments_one {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i∈s, 0≤w i) :
    (moment s w a 2)^2≤moment s w a 1*moment s w a 3 := by
  have hh := cauchy_moments_zero s w (fun i => Real.sqrt (w i)*a i)
  rw [moment_sqrt_multiplier s w a 1 hw, moment_sqrt_multiplier s w a 0 hw,
    moment_sqrt_multiplier s w a 2 hw] at hh
  exact hh

theorem cubic_interpolation {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i∈s, 0≤w i) :
    (moment s w a 1)^3≤(moment s w a 0)^2*moment s w a 3 := by
  have hE := moment_nonneg s w a 1 hw
  have hQ := moment_nonneg s w a 2 hw
  have hD := moment_nonneg s w a 3 hw
  have hK := kinetic_nonneg s w a
  have hc0 := cauchy_moments_zero s w a
  have hc1 := cauchy_moments_one s w a hw
  by_cases hz : moment s w a 1=0
  · rw [hz]
    simpa using mul_nonneg (sq_nonneg (moment s w a 0)) hD
  · have hp : 0<moment s w a 1 := lt_of_le_of_ne hE (Ne.symm hz)
    have hs : ((moment s w a 1)^2)^2≤(moment s w a 0*moment s w a 2)^2 :=
      (sq_le_sq₀ (sq_nonneg _) (mul_nonneg hK hQ)).mpr hc0
    have hm := mul_le_mul_of_nonneg_left hc1 (sq_nonneg (moment s w a 0))
    have hscaled : moment s w a 1*(moment s w a 1)^3≤
        moment s w a 1*((moment s w a 0)^2*moment s w a 3) := by
      nlinarith [hs, hm]
    exact le_of_mul_le_mul_of_pos_left hscaled hp

theorem energy_le_kinetic_mul_frequency {K E D : ℝ} (hK : 0≤K) (hE : 0<E) (hD : 0≤D)
    (hi : E^3≤K^2*D) : E≤K*Real.sqrt (D/E) := by
  have hs : (Real.sqrt (D/E))^2=D/E := Real.sq_sqrt (div_nonneg hD hE.le)
  have hd : D=(Real.sqrt (D/E))^2*E := by rw [hs]; field_simp
  have hscaled : E*E^2≤E*(K*Real.sqrt (D/E))^2 := by
    rw [hd] at hi
    nlinarith [hi]
  have hsq := le_of_mul_le_mul_of_pos_left hscaled hE
  exact (sq_le_sq₀ hE.le (mul_nonneg hK (Real.sqrt_nonneg _))).mp hsq

theorem finite_frequency_lower {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i∈s, 0≤w i) (hE : 0<moment s w a 1) :
    moment s w a 1≤moment s w a 0*Real.sqrt (moment s w a 3/moment s w a 1) :=
  energy_le_kinetic_mul_frequency (kinetic_nonneg s w a) hE
    (moment_nonneg s w a 3 hw) (cubic_interpolation s w a hw)

theorem energy_bound_from_caps {K E D B L : ℝ} (hK : 0≤K) (hE : 0<E) (hD : 0≤D)
    (hi : E^3≤K^2*D) (hKB : K≤B) (hL : 0≤L) (hfreq : Real.sqrt (D/E)≤L) : E≤B*L := by
  calc
    E≤K*Real.sqrt (D/E) := energy_le_kinetic_mul_frequency hK hE hD hi
    _≤K*L := mul_le_mul_of_nonneg_left hfreq hK
    _≤B*L := mul_le_mul_of_nonneg_right hKB hL

theorem moment_multiplier {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (n : ℕ) :
    moment s w (fun i => w i*a i) n=moment s w a (n+2) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add, mul_pow]
  ring

theorem derivative_test_energy {ι : Type*} (s : Finset ι) (w a : ι → ℝ) :
    moment s w (fun i => w i*a i) 1=moment s w a 3 := moment_multiplier s w a 1

/-- Conditional norm substitution; this does not prove a trilinear estimate. -/
theorem derivative_test_bound {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i∈s, 0≤w i) (C T : ℝ)
    (hb : |T|≤C*Real.sqrt (moment s w a 1)*Real.sqrt (moment s w a 3)*
      Real.sqrt (moment s w (fun i => w i*a i) 1)) :
    |T|≤C*Real.sqrt (moment s w a 1)*moment s w a 3 := by
  rw [derivative_test_energy] at hb
  have hs := Real.mul_self_sqrt (moment_nonneg s w a 3 hw)
  calc
    _≤C*Real.sqrt (moment s w a 1)*Real.sqrt (moment s w a 3)*Real.sqrt (moment s w a 3) := hb
    _=(C*Real.sqrt (moment s w a 1))*(Real.sqrt (moment s w a 3)*Real.sqrt (moment s w a 3)) := by ring
    _=_ := by rw [hs]

theorem profile_kinetic_lower {K t : ℝ} (hK : 0≤K) (ht : t<1)
    (hi : (CorridorFiniteTimeExit.energy t)^3≤K^2*CorridorFiniteTimeExit.dissipation t) :
    2*CorridorFiniteTimeExit.energy t≤K := by
  have hh := energy_le_kinetic_mul_frequency hK (CorridorFiniteTimeExit.energy_pos ht)
    (CorridorFiniteTimeExit.dissipation_pos ht).le hi
  change CorridorFiniteTimeExit.energy t≤K*CorridorFiniteTimeExit.frequency t at hh
  rw [CorridorFiniteTimeExit.frequency_eq ht] at hh
  linarith

theorem profile_no_bounded_kinetic_interpolation (K : ℝ → ℝ) (B : ℝ)
    (hK : ∀ t∈Ico (0:ℝ) 1, 0≤K t ∧ K t≤B)
    (hi : ∀ t∈Ico (0:ℝ) 1,
      (CorridorFiniteTimeExit.energy t)^3≤(K t)^2*CorridorFiniteTimeExit.dissipation t) : False := by
  have hev := CorridorFiniteTimeExit.energy_blowup.eventually_ge_atTop (B+1)
  have ht0 : ∀ᶠ t : ℝ in 𝓝[<] 1, 0<t :=
    (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have ht1 : ∀ᶠ t : ℝ in 𝓝[<] 1, t<1 := self_mem_nhdsWithin
  obtain ⟨t, he, ht0, ht1⟩ := (hev.and (ht0.and ht1)).exists
  have hk := hK t ⟨ht0.le, ht1⟩
  have hb := profile_kinetic_lower hk.1 ht1 (hi t ⟨ht0.le, ht1⟩)
  have hB := hk.1.trans hk.2
  linarith

theorem profile_interpolation_saturated (t : ℝ) :
    (CorridorFiniteTimeExit.energy t)^3=
      (2*CorridorFiniteTimeExit.energy t)^2*CorridorFiniteTimeExit.dissipation t := by
  unfold CorridorFiniteTimeExit.dissipation
  ring

theorem no_finite_spectral_profile_with_bounded_kinetic {ι : Type*} (s : Finset ι)
    (w a : ℝ → ι → ℝ) (B : ℝ)
    (hw : ∀ t∈Ico (0:ℝ) 1, ∀ i∈s, 0≤w t i)
    (hK : ∀ t∈Ico (0:ℝ) 1, moment s (w t) (a t) 0≤B)
    (hE : ∀ t∈Ico (0:ℝ) 1, moment s (w t) (a t) 1=CorridorFiniteTimeExit.energy t)
    (hD : ∀ t∈Ico (0:ℝ) 1, moment s (w t) (a t) 3=CorridorFiniteTimeExit.dissipation t) : False := by
  apply profile_no_bounded_kinetic_interpolation (fun t => moment s (w t) (a t) 0) B
  · intro t ht
    exact ⟨kinetic_nonneg s (w t) (a t), hK t ht⟩
  · intro t ht
    have hh := cubic_interpolation s (w t) (a t) (hw t ht)
    rwa [hE t ht, hD t ht] at hh

theorem constant_frequency_moment {ι : Type*} (s : Finset ι) (a : ι → ℝ) (c : ℝ) (n : ℕ) :
    moment s (fun _ => c) a n=c^n*moment s (fun _ => c) a 0 := by
  unfold moment
  simp only [pow_zero, one_mul]
  rw [Finset.mul_sum]

theorem constant_frequency_interpolation_equality {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (c : ℝ) : (moment s (fun _ => c) a 1)^3=
      (moment s (fun _ => c) a 0)^2*moment s (fun _ => c) a 3 := by
  rw [constant_frequency_moment s a c 1, constant_frequency_moment s a c 3]
  ring

def profileFrequency (_j : Fin 32) : ℝ := 1/2
def profileAmplitude (ε t : ℝ) (j : Fin 32) : ℝ :=
  Real.sqrt (2*CorridorFiniteTimeExit.sectorEnergy ε j t)

theorem profile_sector_weight {ε t : ℝ} (hε : 0<ε) (hε1 : ε≤1) (ht0 : 0≤t) (ht1 : t<1)
    (j : Fin 32) : profileFrequency j*(profileAmplitude ε t j)^2=
      CorridorFiniteTimeExit.sectorEnergy ε j t := by
  have hp := CorridorFiniteTimeExit.sectorEnergy_positive hε hε1 ht0 ht1 j
  unfold profileFrequency profileAmplitude
  rw [Real.sq_sqrt (by positivity)]
  ring

theorem profile_moment {ε t : ℝ} (hε : 0<ε) (hε1 : ε≤1) (ht0 : 0≤t) (ht1 : t<1)
    (n : ℕ) : moment Finset.univ profileFrequency (profileAmplitude ε t) n=
      2*(1/2:ℝ)^n*CorridorFiniteTimeExit.energy t := by
  calc
    _ = ∑ j : Fin 32, 2*(1/2:ℝ)^n*CorridorFiniteTimeExit.sectorEnergy ε j t := by
      apply Finset.sum_congr rfl
      intro j hj
      have hp := CorridorFiniteTimeExit.sectorEnergy_positive hε hε1 ht0 ht1 j
      unfold profileFrequency profileAmplitude
      rw [Real.sq_sqrt (by positivity)]
      ring
    _ = 2*(1/2:ℝ)^n*(∑ j : Fin 32, CorridorFiniteTimeExit.sectorEnergy ε j t) := by
      rw [Finset.mul_sum]
    _ = _ := by rw [CorridorFiniteTimeExit.sectorEnergy_sum]

theorem profile_spectral_realization {ε t : ℝ} (hε : 0<ε) (hε1 : ε≤1) (ht0 : 0≤t) (ht1 : t<1) :
    moment Finset.univ profileFrequency (profileAmplitude ε t) 0=2*CorridorFiniteTimeExit.energy t ∧
      moment Finset.univ profileFrequency (profileAmplitude ε t) 1=CorridorFiniteTimeExit.energy t ∧
      moment Finset.univ profileFrequency (profileAmplitude ε t) 3=CorridorFiniteTimeExit.dissipation t := by
  constructor
  · rw [profile_moment hε hε1 ht0 ht1 0]
    norm_num
  · constructor
    · rw [profile_moment hε hε1 ht0 ht1 1]
      ring
    · rw [profile_moment hε hε1 ht0 ht1 3]
      unfold CorridorFiniteTimeExit.dissipation
      ring

end OperatorDerivativeRewrite.Foundation.SpectralEnergyInterpolation
