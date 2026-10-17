import Foundation.AngularTriadPartition

/-! Exact phase/energy sign classification for a three-amplitude divergence-free triad. -/
noncomputable section
open Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ParameterizedSectorTriad
open SectorTransferSymmetry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048

def amplitude (a b c : ℝ) (i : Fin 6) : Vector :=
  ![![0,a,0],![-b,0,0],![-c,c,0],![0,-a,0],![b,0,0],![c,-c,0]] i
def polarization (a b c : ℝ) (k : Wave) (j : Fin 3) : ℝ :=
  ∑ i : Fin 6, if k=SectorTriadSign.mode i then amplitude a b c i j else 0
def energyValue (a b c : ℝ) : ℝ := 2*a^2+2*b^2+8*c^2
def fourthValue (a b c : ℝ) : ℝ := a^4+b^4+16*c^4
def imbalance (a b c : ℝ) : ℝ := a*b*c*(a^2-b^2)
def denominator (a b c : ℝ) : ℝ := 2*fourthValue a b c-(energyValue a b c)^2/32
def weights (a b c : ℝ) (i : Fin 6) : ℝ := ![a^2,b^2,4*c^2,a^2,b^2,4*c^2] i
def transfers (a b c : ℝ) (i : Fin 6) : ℝ := ![2*a*b*c,-2*a*b*c,0,2*a*b*c,-2*a*b*c,0] i
def sectorWeight (a b c : ℝ) (j : Fin 32) : ℝ :=
  if j=0 ∨ j=8 then a^2 else if j=7 ∨ j=31 then b^2 else if j=4 ∨ j=20 then 4*c^2 else 0
def sectorFlux (a b c : ℝ) (j : Fin 32) : ℝ :=
  if j=0 ∨ j=8 then 2*a*b*c else if j=7 ∨ j=31 then -2*a*b*c else 0

theorem polarization_mode (a b c : ℝ) (i : Fin 6) :
    polarization a b c (SectorTriadSign.mode i)=amplitude a b c i := by
  ext j
  simp [polarization,SectorTriadSign.mode_injective.eq_iff]

theorem polarization_off (a b c : ℝ) (k : Wave) (hk : k∉SectorTriadSign.modes) :
    polarization a b c k=0 := by
  have hn : ∀ i, k≠SectorTriadSign.mode i := by
    intro i he
    exact hk (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩)
  ext j
  simp [polarization,hn]

theorem amplitude_opposite (a b c : ℝ) (i : Fin 6) :
    amplitude a b c (SectorTriadSign.opposite i)= -amplitude a b c i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [amplitude,SectorTriadSign.opposite]

theorem transverse (a b c : ℝ) (k : Wave) : dotWave k (polarization a b c k)=0 := by
  by_cases hk : k∈SectorTriadSign.modes
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hk
    rw [polarization_mode]
    fin_cases i <;> norm_num [dotWave,SectorTriadSign.mode,amplitude,Fin.sum_univ_succ] <;> ring
  · simp [polarization_off a b c k hk,dotWave]

theorem polarization_odd (a b c : ℝ) (k : Wave) :
    polarization a b c (-k)= -polarization a b c k := by
  by_cases hk : k∈SectorTriadSign.modes
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hk
    rw [← SectorTriadSign.mode_opposite,polarization_mode,polarization_mode,amplitude_opposite]
  · have hn : -k∉SectorTriadSign.modes := by
      intro h
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
      have he : SectorTriadSign.mode (SectorTriadSign.opposite i)=k := by
        rw [SectorTriadSign.mode_opposite]
        simpa using congrArg Neg.neg hi
      exact hk (Finset.mem_image.mpr ⟨SectorTriadSign.opposite i,Finset.mem_univ _,he⟩)
    rw [polarization_off a b c k hk,polarization_off a b c (-k) hn,neg_zero]

theorem mode_energy (a b c : ℝ) (i : Fin 6) :
    modeEnergy (polarization a b c) (SectorTriadSign.mode i)=weights a b c i := by
  unfold modeEnergy
  rw [polarization_mode]
  fin_cases i <;> norm_num [waveSquare,dotVector,SectorTriadSign.mode,amplitude,weights,Fin.sum_univ_succ] <;> ring

theorem mode_transfer (a b c : ℝ) (i : Fin 6) :
    transfer SectorTriadSign.modes (polarization a b c) (SectorTriadSign.mode i)=transfers a b c i := by
  simp only [transfer,SectorTriadSign.sum_modes,triadTerm,polarization_mode]
  fin_cases i <;> norm_num [Fin.sum_univ_succ,SectorTriadSign.mode,amplitude,transfers,
    waveSquare,dotWave,dotVector,funext_iff,Fin.forall_fin_succ,Pi.add_apply] <;> ring

theorem energy_exact (a b c : ℝ) : energy SectorTriadSign.modes (polarization a b c)=energyValue a b c := by
  unfold energy
  rw [SectorTriadSign.sum_modes]
  simp_rw [mode_energy]
  norm_num [weights,energyValue,Fin.sum_univ_succ] <;> ring

theorem totalTransfer_zero (a b c : ℝ) : totalTransfer SectorTriadSign.modes (polarization a b c)=0 := by
  unfold totalTransfer
  rw [SectorTriadSign.sum_modes]
  simp_rw [mode_transfer]
  norm_num [transfers,Fin.sum_univ_succ] <;> ring

theorem sectorEnergy_exact (a b c : ℝ) (j : Fin 32) :
    sectorEnergy SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c) j=sectorWeight a b c j := by
  simp only [sectorEnergy,SectorTriadSign.sum_modes,AngularTriadPartition.sector_mode,mode_energy]
  fin_cases j <;> norm_num [Fin.sum_univ_succ,weights,sectorWeight,AngularTriadPartition.modeLabels]

theorem sectorTransfer_exact (a b c : ℝ) (j : Fin 32) :
    sectorTransfer SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c) j=sectorFlux a b c j := by
  simp only [sectorTransfer,SectorTriadSign.sum_modes,AngularTriadPartition.sector_mode,mode_transfer]
  fin_cases j <;> norm_num [Fin.sum_univ_succ,transfers,sectorFlux,AngularTriadPartition.modeLabels]

theorem concentration_exact (a b c : ℝ) :
    concentration SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c)=
      2*fourthValue a b c/(energyValue a b c)^2 := by
  norm_num [concentration,fraction,energy_exact,sectorEnergy_exact,sectorWeight,Fin.sum_univ_succ]
  simp only [div_pow]
  unfold fourthValue
  ring

theorem sigma_exact (a b c : ℝ) :
    sigma SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c)=
      8*imbalance a b c/(energyValue a b c)^2 := by
  norm_num [sigma,fraction,energy_exact,sectorEnergy_exact,sectorWeight,sectorTransfer_exact,
    sectorFlux,totalTransfer_zero,Fin.sum_univ_succ]
  by_cases he : energyValue a b c=0
  · simp [he]
  · unfold imbalance
    field_simp [he]
    ring

theorem energy_nonneg (a b c : ℝ) : 0≤energyValue a b c := by unfold energyValue; positivity

theorem energy_zero_iff (a b c : ℝ) : energyValue a b c=0 ↔ a=0 ∧ b=0 ∧ c=0 := by
  unfold energyValue
  constructor
  · intro h
    constructor
    · nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg c]
    · constructor <;> nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg c]
  · rintro ⟨rfl,rfl,rfl⟩
    norm_num

theorem concentration_lower (a b c : ℝ) (he : 0 < energyValue a b c) :
    1/6≤concentration SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c) := by
  rw [concentration_exact]
  apply (le_div_iff₀ (sq_pos_of_pos he)).mpr
  unfold fourthValue energyValue
  nlinarith [sq_nonneg (a^2-b^2),sq_nonneg (a^2-4*c^2),sq_nonneg (b^2-4*c^2)]

theorem concentrated (a b c : ℝ) (he : 0 < energyValue a b c) :
    1/(32 : ℝ)<concentration SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c) :=
  lt_of_lt_of_le (by norm_num) (concentration_lower a b c he)

theorem denominator_eq (a b c : ℝ) (he : 0 < energyValue a b c) :
    denominator a b c=(energyValue a b c)^2*
      (concentration SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c)-1/32) := by
  rw [concentration_exact]
  unfold denominator
  field_simp [he.ne'] <;> ring

theorem denominator_pos (a b c : ℝ) (he : 0 < energyValue a b c) : 0 < denominator a b c := by
  rw [denominator_eq a b c he]
  exact mul_pos (sq_pos_of_pos he) (sub_pos.mpr (concentrated a b c he))

theorem rate_exact (a b c : ℝ) (he : 0 < energyValue a b c) :
    rate SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c)=
      -8*imbalance a b c/denominator a b c := by
  have hc := (sub_pos.mpr (concentrated a b c he)).ne'
  rw [rate,sigma_exact,denominator_eq a b c he]
  field_simp [hc,he.ne']
  ring

theorem rate_negative_iff (a b c : ℝ) (he : 0 < energyValue a b c) :
    rate SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c) < 0 ↔ 0 < imbalance a b c := by
  rw [rate_exact a b c he,div_lt_iff₀ (denominator_pos a b c he)]
  constructor <;> intro h <;> nlinarith

theorem rate_positive_iff (a b c : ℝ) (he : 0 < energyValue a b c) :
    0 < rate SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c) ↔ imbalance a b c < 0 := by
  rw [rate_exact a b c he,lt_div_iff₀ (denominator_pos a b c he)]
  constructor <;> intro h <;> nlinarith

theorem rate_zero_iff (a b c : ℝ) (he : 0 < energyValue a b c) :
    rate SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c)=0 ↔ imbalance a b c=0 := by
  rw [rate_exact a b c he,div_eq_zero_iff]
  simp only [(denominator_pos a b c he).ne',or_false]
  constructor <;> intro h <;> nlinarith

theorem swap_energy (a b c : ℝ) : energyValue b a c=energyValue a b c := by unfold energyValue; ring
theorem swap_concentration (a b c : ℝ) :
    concentration SectorTriadSign.modes AngularTriadPartition.sector (polarization b a c)=
      concentration SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c) := by
  rw [concentration_exact,concentration_exact,swap_energy]
  unfold fourthValue
  ring

theorem swap_rate (a b c : ℝ) (he : 0 < energyValue a b c) :
    rate SectorTriadSign.modes AngularTriadPartition.sector (polarization b a c)=
      -rate SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c) := by
  have hs : denominator b a c=denominator a b c := by unfold denominator fourthValue energyValue; ring
  have hi : imbalance b a c= -imbalance a b c := by unfold imbalance; ring
  rw [rate_exact b a c (by rwa [swap_energy]),rate_exact a b c he,hs,hi]
  ring

theorem all_zero_rate : rate SectorTriadSign.modes AngularTriadPartition.sector (polarization 0 0 0)=0 := by
  rw [rate,sigma_exact]
  simp [energyValue,imbalance]

def negativeRegion : Set Vector := {p | 0 < energyValue (p 0) (p 1) (p 2) ∧ 0 < imbalance (p 0) (p 1) (p 2)}

theorem negativeRegion_open : IsOpen negativeRegion := by
  have hE : Continuous (fun p : Vector => energyValue (p 0) (p 1) (p 2)) := by unfold energyValue; fun_prop
  have hI : Continuous (fun p : Vector => imbalance (p 0) (p 1) (p 2)) := by unfold imbalance; fun_prop
  exact (isOpen_lt continuous_const hE).inter (isOpen_lt continuous_const hI)

theorem example_mem : (![2,1,1] : Vector)∈negativeRegion := by norm_num [negativeRegion,energyValue,imbalance]
theorem negativeRegion_neighborhood : negativeRegion∈𝓝 (![2,1,1] : Vector) :=
  negativeRegion_open.mem_nhds example_mem

theorem negativeRegion_rate (p : Vector) (hp : p∈negativeRegion) :
    rate SectorTriadSign.modes AngularTriadPartition.sector (polarization (p 0) (p 1) (p 2)) < 0 :=
  (rate_negative_iff _ _ _ hp.1).mpr hp.2

theorem balanced_interacting :
    energy SectorTriadSign.modes (polarization 2 2 1)=24 ∧
    concentration SectorTriadSign.modes AngularTriadPartition.sector (polarization 2 2 1)=1/6 ∧
    sigma SectorTriadSign.modes AngularTriadPartition.sector (polarization 2 2 1)=0 ∧
    rate SectorTriadSign.modes AngularTriadPartition.sector (polarization 2 2 1)=0 ∧
    transfer SectorTriadSign.modes (polarization 2 2 1) (SectorTriadSign.mode 0)=8 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [energy_exact]
    norm_num [energyValue]
  · rw [concentration_exact]
    norm_num [fourthValue,energyValue]
  · rw [sigma_exact]
    norm_num [imbalance,energyValue]
  · rw [rate_exact 2 2 1 (by norm_num [energyValue])]
    norm_num [imbalance,denominator]
  · rw [mode_transfer]
    norm_num [transfers]

theorem concentration_bound_attained : ∃ a b c : ℝ, 0 < energyValue a b c ∧
    concentration SectorTriadSign.modes AngularTriadPartition.sector (polarization a b c)=1/6 :=
  ⟨2,2,1,by norm_num [energyValue],balanced_interacting.2.1⟩

theorem swapped_example_rates :
    rate SectorTriadSign.modes AngularTriadPartition.sector (polarization 2 1 1)= -128/149 ∧
    rate SectorTriadSign.modes AngularTriadPartition.sector (polarization 1 2 1)=128/149 := by
  constructor
  · rw [rate_exact 2 1 1 (by norm_num [energyValue])]
    norm_num [imbalance,denominator,fourthValue,energyValue]
  · rw [rate_exact 1 2 1 (by norm_num [energyValue])]
    norm_num [imbalance,denominator,fourthValue,energyValue]

end OperatorDerivativeRewrite.Foundation.ParameterizedSectorTriad
