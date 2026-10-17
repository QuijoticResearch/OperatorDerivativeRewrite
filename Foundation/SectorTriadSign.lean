import Foundation.SectorTransferSymmetry

/-! An exact nonzero signed sector-transfer triad, with total enstrophy transfer zero. -/
noncomputable section
open Finset
namespace OperatorDerivativeRewrite.Foundation.SectorTriadSign
open SectorTransferSymmetry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048

def mode (i : Fin 6) : Wave :=
  ![![1,0,0],![0,1,0],![1,1,0],![-1,0,0],![0,-1,0],![-1,-1,0]] i
def amplitude (i : Fin 6) : Vector :=
  ![![0,2,0],![-1,0,0],![-1,1,0],![0,-2,0],![1,0,0],![1,-1,0]] i
def opposite (i : Fin 6) : Fin 6 := ![3,4,5,0,1,2] i
def modes : Finset Wave := Finset.univ.image mode
def polarization (k : Wave) (j : Fin 3) : ℝ :=
  ∑ i : Fin 6, if k=mode i then amplitude i j else 0

theorem mode_injective : Function.Injective mode := by decide

theorem mode_opposite (i : Fin 6) : mode (opposite i) = -mode i := by
  fin_cases i <;> decide

theorem amplitude_opposite (i : Fin 6) : amplitude (opposite i) = -amplitude i := by
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [amplitude,opposite]

theorem polarization_mode (i : Fin 6) : polarization (mode i) = amplitude i := by
  ext j
  simp [polarization,mode_injective.eq_iff]

theorem sum_modes (f : Wave → ℝ) : (∑ k ∈ modes, f k) = ∑ i : Fin 6, f (mode i) := by
  unfold modes
  rw [Finset.sum_image]
  intro i _ j _ h
  exact mode_injective h

theorem polarization_off (k : Wave) (hk : k∉modes) : polarization k = 0 := by
  have hn : ∀ i, k≠mode i := by
    intro i he
    apply hk
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩
  ext j
  simp [polarization,hn]

theorem transverse (k : Wave) : dotWave k (polarization k)=0 := by
  by_cases hk : k∈modes
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hk
    rw [polarization_mode]
    fin_cases i <;> norm_num [dotWave,mode,amplitude,Fin.sum_univ_succ]
  · simp [polarization_off k hk,dotWave]

theorem polarization_odd (k : Wave) : polarization (-k)= -polarization k := by
  by_cases hk : k∈modes
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hk
    rw [← mode_opposite,polarization_mode,polarization_mode,amplitude_opposite]
  · have hn : -k∉modes := by
      intro h
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
      apply hk
      have he : mode (opposite i)=k := by
        rw [mode_opposite]
        simpa using congrArg Neg.neg hi
      exact Finset.mem_image.mpr ⟨opposite i,Finset.mem_univ _,he⟩
    rw [polarization_off k hk,polarization_off (-k) hn,neg_zero]

def weights (i : Fin 6) : ℝ := ![4,1,4,4,1,4] i
def transfers (i : Fin 6) : ℝ := ![4,-4,0,4,-4,0] i

theorem mode_energy (i : Fin 6) : modeEnergy polarization (mode i)=weights i := by
  unfold modeEnergy
  rw [polarization_mode]
  fin_cases i <;> norm_num [waveSquare,dotVector,mode,amplitude,weights,Fin.sum_univ_succ]

theorem mode_transfer (i : Fin 6) : transfer modes polarization (mode i)=transfers i := by
  simp only [transfer,sum_modes,triadTerm,polarization_mode]
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ,mode,amplitude,transfers,waveSquare,dotWave,dotVector,
      funext_iff,Fin.forall_fin_succ,Pi.add_apply]

theorem energy_exact : energy modes polarization=18 := by
  unfold energy
  rw [sum_modes]
  simp_rw [mode_energy]
  norm_num [weights,Fin.sum_univ_succ]

theorem totalTransfer_zero : totalTransfer modes polarization=0 := by
  unfold totalTransfer
  rw [sum_modes]
  simp_rw [mode_transfer]
  norm_num [transfers,Fin.sum_univ_succ]

def sector (k : Wave) : Fin 32 :=
  if k=mode 0 then 0 else if k=mode 1 then 1 else if k=mode 2 then 2 else
  if k=mode 3 then 3 else if k=mode 4 then 4 else if k=mode 5 then 5 else 6

theorem sector_mode (i : Fin 6) : sector (mode i)=Fin.castLE (by decide : 6≤32) i := by
  fin_cases i <;> decide

def sectorWeight (j : Fin 32) : ℝ :=
  if j=0 ∨ j=2 ∨ j=3 ∨ j=5 then 4 else if j=1 ∨ j=4 then 1 else 0
def sectorFlux (j : Fin 32) : ℝ :=
  if j=0 ∨ j=3 then 4 else if j=1 ∨ j=4 then -4 else 0

theorem sectorEnergy_exact (j : Fin 32) : sectorEnergy modes sector polarization j=sectorWeight j := by
  simp only [sectorEnergy,sum_modes,sector_mode,mode_energy]
  fin_cases j <;> norm_num [Fin.sum_univ_succ,weights,sectorWeight]

theorem sectorTransfer_exact (j : Fin 32) : sectorTransfer modes sector polarization j=sectorFlux j := by
  simp only [sectorTransfer,sum_modes,sector_mode,mode_transfer]
  fin_cases j <;> norm_num [Fin.sum_univ_succ,transfers,sectorFlux]

theorem concentration_exact : concentration modes sector polarization=11/54 := by
  norm_num [concentration,fraction,energy_exact,sectorEnergy_exact,sectorWeight,Fin.sum_univ_succ]

theorem sigma_exact : sigma modes sector polarization=4/27 := by
  norm_num [sigma,fraction,energy_exact,sectorEnergy_exact,sectorWeight,sectorTransfer_exact,
    sectorFlux,totalTransfer_zero,Fin.sum_univ_succ]

theorem rate_exact : rate modes sector polarization= -128/149 := by
  rw [rate,sigma_exact,concentration_exact]
  norm_num

theorem rate_negative : rate modes sector polarization<0 := by rw [rate_exact]; norm_num

theorem reversed_rate : rate modes sector (fun k i => -polarization k i)=128/149 := by
  rw [rate_neg,rate_exact]
  norm_num

theorem concentrated : 1/(32 : ℝ)<concentration modes sector polarization := by
  rw [concentration_exact]
  norm_num

theorem no_universal_nonnegative :
    ¬ ∀ V : Field,
      (∀ k, k∉modes → V k=0) →
      (∀ k, dotWave k (V k)=0) →
      (∀ k, V (-k)= -V k) →
      0<energy modes V →
      1/(32 : ℝ)<concentration modes sector V → 0≤rate modes sector V := by
  intro h
  have hn := h polarization polarization_off transverse polarization_odd
    (by rw [energy_exact]; norm_num) concentrated
  exact not_le_of_gt rate_negative hn

end OperatorDerivativeRewrite.Foundation.SectorTriadSign
