import Foundation.RestrictedEulerRatioCounterexample
import Foundation.CorridorMaximumRegularity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A scalar diagnostic for the quoted corridor inequalities, not a Navier–Stokes flow. -/
noncomputable section
open Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CorridorFiniteTimeExit
set_option backward.isDefEq.respectTransparency false

abbrev pole := RestrictedEulerRatioCounterexample.scale
def energy (t : ℝ) : ℝ := (pole t)^2
def dissipation (t : ℝ) : ℝ := energy t/4
def trilinear (t : ℝ) : ℝ := -(pole t)^3-dissipation t
def frequency (t : ℝ) : ℝ := Real.sqrt (dissipation t/energy t)
def concentration (ε t : ℝ) : ℝ := 1-ε/2-ε*t/4
def higherDissipation (t : ℝ) : ℝ := energy t/16
def higherTrilinear (t : ℝ) : ℝ := trilinear t/4

theorem pole_pos {t : ℝ} (ht : t<1) : 0<pole t := by
  unfold pole RestrictedEulerRatioCounterexample.scale
  exact inv_pos.mpr (by linarith)

theorem pole_ge_one {t : ℝ} (ht0 : 0≤t) (ht1 : t<1) : 1≤pole t := by
  unfold pole RestrictedEulerRatioCounterexample.scale
  apply (one_le_inv₀ (by linarith : (0:ℝ)<1-t)).mpr
  linarith

theorem energy_pos {t : ℝ} (ht : t<1) : 0<energy t := by
  unfold energy
  exact sq_pos_of_pos (pole_pos ht)

theorem dissipation_pos {t : ℝ} (ht : t<1) : 0<dissipation t :=
  div_pos (energy_pos ht) (by norm_num)

theorem energy_hasDerivAt {t : ℝ} (ht : t<1) : HasDerivAt energy (2*(pole t)^3) t := by
  have hn : t≠1 := ne_of_lt ht
  convert (RestrictedEulerRatioCounterexample.scale_derivative t hn).pow 2 using 1
  · ext s; rfl
  · norm_num
    ring

theorem energy_ode {t : ℝ} (ht : t<1) :
    HasDerivAt energy (-2*trilinear t-2*dissipation t) t := by
  convert energy_hasDerivAt ht using 1
  unfold trilinear
  ring

theorem energy_derivative_positive {t : ℝ} (ht : t<1) : 0<deriv energy t := by
  rw [(energy_hasDerivAt ht).deriv]
  positivity [pole_pos ht]

theorem dissipation_ode {t : ℝ} (ht : t<1) :
    HasDerivAt dissipation (-2*higherTrilinear t-2*higherDissipation t) t := by
  convert (energy_ode ht).div_const 4 using 1
  · ext s; rfl
  · unfold higherTrilinear higherDissipation dissipation
    ring

theorem higherDissipation_pos {t : ℝ} (ht : t<1) : 0<higherDissipation t :=
  div_pos (energy_pos ht) (by norm_num)

theorem interpolation_identity (t : ℝ) : (dissipation t)^2=energy t*higherDissipation t := by
  unfold dissipation higherDissipation
  ring

theorem sqrt_energy {t : ℝ} (ht : t<1) : Real.sqrt (energy t)=pole t :=
  Real.sqrt_sq (pole_pos ht).le

theorem sqrt_dissipation {t : ℝ} (ht : t<1) : Real.sqrt (dissipation t)=pole t/2 := by
  have he : dissipation t=(pole t/2)^2 := by unfold dissipation energy; ring
  rw [he, Real.sqrt_sq (by positivity [pole_pos ht])]

theorem frequency_eq {t : ℝ} (ht : t<1) : frequency t=1/2 := by
  have he : dissipation t/energy t=(1/2:ℝ)^2 := by
    unfold dissipation
    field_simp [(energy_pos ht).ne']
    ring
  rw [frequency, he, Real.sqrt_sq (by norm_num)]

theorem low_frequency {t : ℝ} (ht : t<1) : 0<frequency t ∧ frequency t<1 := by
  rw [frequency_eq ht]
  norm_num

theorem trilinear_required_sign {t : ℝ} (ht : t<1) : trilinear t< -dissipation t := by
  unfold trilinear
  have hp : 0<(pole t)^3 := pow_pos (pole_pos ht) 3
  linarith

theorem trilinear_negative {t : ℝ} (ht : t<1) : trilinear t<0 :=
  (trilinear_required_sign ht).trans (neg_neg_of_pos (dissipation_pos ht))

theorem trilinear_upper {t : ℝ} (ht0 : 0≤t) (ht1 : t<1) :
    |trilinear t|≤4*energy t*Real.sqrt (dissipation t) := by
  have hp := pole_ge_one ht0 ht1
  have hprod := mul_nonneg (sq_nonneg (pole t)) (sub_nonneg.mpr hp)
  rw [abs_of_neg (trilinear_negative ht1), trilinear, sqrt_dissipation ht1]
  unfold dissipation energy
  nlinarith [sq_nonneg (pole t)]

theorem frequency_upper {t : ℝ} (ht0 : 0≤t) (ht1 : t<1) :
    frequency t<4*Real.sqrt (energy t) := by
  rw [frequency_eq ht1, sqrt_energy ht1]
  linarith [pole_ge_one ht0 ht1]

theorem admissible_high_interval {t : ℝ} (ht0 : 0≤t) (ht1 : t<1) :
    ∃ w : ℝ, 1≤w ∧ w<4*Real.sqrt (energy t) := by
  refine ⟨1, le_rfl, ?_⟩
  rw [sqrt_energy ht1]
  linarith [pole_ge_one ht0 ht1]

theorem concentration_hasDerivAt (ε t : ℝ) : HasDerivAt (concentration ε) (-ε/4) t := by
  convert ((hasDerivAt_id t).const_mul (ε/4)).const_sub (1-ε/2) using 1
  · ext s
    change 1-ε/2-ε*s/4=(1-ε/2)-(ε/4)*s
    ring
  · ring

theorem concentration_margin {ε t : ℝ} (hε : 0<ε) (ht : t<1) :
    1-3*ε/4<concentration ε t := by
  have hm := mul_lt_mul_of_pos_left ht hε
  unfold concentration
  nlinarith

theorem remains_concentrated {ε t : ℝ} (hε : 0<ε) (ht : t<1) :
    1-ε<concentration ε t := by
  have hm := concentration_margin hε ht
  linarith

theorem concentration_range {ε t : ℝ} (hε : 0<ε) (hε1 : ε≤1) (ht0 : 0≤t) (ht1 : t<1) :
    0<concentration ε t ∧ concentration ε t<1 := by
  have hm := remains_concentrated hε ht1
  have hp := mul_nonneg hε.le ht0
  unfold concentration at *
  constructor <;> nlinarith

theorem concentration_decay {ε t : ℝ} (hε : 0<ε) (ht0 : 0≤t) (ht1 : t<1) :
    deriv (concentration ε) t≤ -(frequency t)^2*(1-concentration ε t) ∧
      -(frequency t)^2*(1-concentration ε t)<0 := by
  rw [(concentration_hasDerivAt ε t).deriv, frequency_eq ht1]
  have hm := mul_lt_mul_of_pos_left ht1 hε
  have hp := mul_nonneg hε.le ht0
  unfold concentration
  constructor <;> nlinarith

theorem no_exit_before_terminal {ε : ℝ} (hε : 0<ε) :
    ¬∃ t∈Ico (0:ℝ) 1, concentration ε t<1-ε := by
  rintro ⟨t, ht, he⟩
  exact (not_lt_of_gt (remains_concentrated hε ht.2)) he

theorem gap_tendsto_zero : Tendsto (fun t : ℝ => 1-t) (𝓝[<] 1) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun t : ℝ => 1-t) := by fun_prop
    simpa only [sub_self] using (hc.tendsto 1).mono_left
      (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)
  · have ht : ∀ᶠ t : ℝ in 𝓝[<] 1, t<1 := self_mem_nhdsWithin
    filter_upwards [ht] with t ht
    exact sub_pos.mpr ht

theorem pole_tendsto_infinity : Tendsto pole (𝓝[<] 1) atTop := by
  change Tendsto (fun t : ℝ => (1-t)⁻¹) (𝓝[<] 1) atTop
  exact tendsto_inv_nhdsGT_zero.comp gap_tendsto_zero

theorem energy_blowup : Tendsto energy (𝓝[<] 1) atTop := by
  change Tendsto (fun t : ℝ => (pole t)^2) (𝓝[<] 1) atTop
  exact (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp pole_tendsto_infinity

theorem concentration_terminal_limit (ε : ℝ) :
    Tendsto (concentration ε) (𝓝[<] 1) (𝓝 (1-3*ε/4)) := by
  have hc : Continuous (concentration ε) := by unfold concentration; fun_prop
  have he : concentration ε 1=1-3*ε/4 := by unfold concentration; ring
  have ht := (hc.tendsto 1).mono_left
    (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)
  rw [he] at ht
  exact ht

/-- All scalar bounds quoted in the low-frequency argument hold without finite-time exit. -/
theorem scalar_diagnostic (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    Tendsto energy (𝓝[<] 1) atTop ∧
      (∀ t∈Ico (0:ℝ) 1,
        0<energy t ∧ 0<dissipation t ∧
        HasDerivAt energy (-2*trilinear t-2*dissipation t) t ∧
        0<deriv energy t ∧ trilinear t< -dissipation t ∧
        |trilinear t|≤4*energy t*Real.sqrt (dissipation t) ∧
        frequency t<4*Real.sqrt (energy t) ∧ 0<frequency t ∧ frequency t<1 ∧
        0<concentration ε t ∧ concentration ε t<1 ∧ 1-ε<concentration ε t ∧
        deriv (concentration ε) t≤ -(frequency t)^2*(1-concentration ε t) ∧
        -(frequency t)^2*(1-concentration ε t)<0) ∧
      ¬∃ t∈Ico (0:ℝ) 1, concentration ε t<1-ε := by
  refine ⟨energy_blowup, ?_, no_exit_before_terminal hε⟩
  intro t ht
  exact ⟨energy_pos ht.2, dissipation_pos ht.2, energy_ode ht.2,
    energy_derivative_positive ht.2, trilinear_required_sign ht.2,
    trilinear_upper ht.1 ht.2, frequency_upper ht.1 ht.2,
    (low_frequency ht.2).1, (low_frequency ht.2).2,
    (concentration_range hε hε1 ht.1 ht.2).1, (concentration_range hε hε1 ht.1 ht.2).2,
    remains_concentrated hε ht.2, (concentration_decay hε ht.1 ht.2).1,
    (concentration_decay hε ht.1 ht.2).2⟩

def sectorEnergy (ε : ℝ) (j : Fin 32) (t : ℝ) : ℝ :=
  if j=0 then concentration ε t*energy t else (1-concentration ε t)*energy t/31

theorem sectorEnergy_positive {ε t : ℝ} (hε : 0<ε) (hε1 : ε≤1) (ht0 : 0≤t) (ht1 : t<1)
    (j : Fin 32) : 0<sectorEnergy ε j t := by
  have hr := concentration_range hε hε1 ht0 ht1
  unfold sectorEnergy
  split_ifs
  · exact mul_pos hr.1 (energy_pos ht1)
  · exact div_pos (mul_pos (sub_pos.mpr hr.2) (energy_pos ht1)) (by norm_num)

theorem sectorEnergy_sum (ε t : ℝ) : (∑ j : Fin 32, sectorEnergy ε j t)=energy t := by
  rw [Fin.sum_univ_succ]
  simp only [sectorEnergy, Fin.succ_ne_zero, ite_false, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem concentration_quarter_bound {ε t : ℝ} (hε : 0<ε) (hε1 : ε≤1) (ht1 : t<1) :
    1/4<concentration ε t := by
  have hm := concentration_margin hε ht1
  linarith

theorem maximum_sector_energy {ε t : ℝ} (hε : 0<ε) (hε1 : ε≤1) (ht1 : t<1) :
    CorridorMaximumRegularity.finiteMaximum Finset.univ Finset.univ_nonempty (sectorEnergy ε) t=
      concentration ε t*energy t := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
    intro j hj
    by_cases hz : j=0
    · simp [sectorEnergy, hz]
    · simp only [sectorEnergy, hz, ite_false]
      apply (div_le_iff₀ (by norm_num : (0:ℝ)<31)).mpr
      have hr : 0≤32*concentration ε t-1 := by
        linarith [concentration_quarter_bound hε hε1 ht1]
      nlinarith [mul_nonneg (energy_pos ht1).le hr]
  · change sectorEnergy ε (0 : Fin 32) t≤_
    exact Finset.le_sup' (fun j : Fin 32 => sectorEnergy ε j t) (Finset.mem_univ 0)

theorem concentration_from_sectors {ε t : ℝ} (hε : 0<ε) (hε1 : ε≤1) (ht1 : t<1) :
    CorridorMaximumRegularity.finiteMaximum Finset.univ Finset.univ_nonempty (sectorEnergy ε) t /
      (∑ j : Fin 32, sectorEnergy ε j t)=concentration ε t := by
  rw [maximum_sector_energy hε hε1 ht1, sectorEnergy_sum]
  exact mul_div_cancel_right₀ _ (energy_pos ht1).ne'

end OperatorDerivativeRewrite.Foundation.CorridorFiniteTimeExit
