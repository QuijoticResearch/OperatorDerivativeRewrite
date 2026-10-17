import Foundation.SectorTriadSign

/-! An explicit nonempty 32-cell partition of directions realizes the negative triad rate. -/
noncomputable section
open Set
namespace OperatorDerivativeRewrite.Foundation.AngularTriadPartition
open SectorTransferSymmetry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

def bin (x y : ℝ) : Fin 8 :=
  if 4*|y| < |x| then 0 else if 2*|y| < |x| then 1 else
  if 4*|y| < 3*|x| then 2 else if |y| < |x| then 3 else
  if 3*|y| < 4*|x| then 4 else if |y| < 2*|x| then 5 else if |y| < 4*|x| then 6 else 7
def quadrant (x y : ℝ) : Fin 4 :=
  if 0≤y then (if 0≤x then 0 else 1) else (if x<0 then 2 else 3)
def label (v : Vector) : Fin 32 :=
  ⟨8*(quadrant (v 0) (v 1)).val+(bin (v 0) (v 1)).val, by
    have hq := (quadrant (v 0) (v 1)).isLt
    have hb := (bin (v 0) (v 1)).isLt
    omega⟩

theorem bin_scale (a x y : ℝ) (ha : 0<a) : bin (a*x) (a*y)=bin x y := by
  have hcmp (c d : ℝ) : c*|a*y|<d*|a*x| ↔ c*|y|<d*|x| := by
    rw [abs_mul,abs_mul,abs_of_pos ha]
    rw [show c*(a*|y|)=a*(c*|y|) by ring,show d*(a*|x|)=a*(d*|x|) by ring]
    exact mul_lt_mul_iff_of_pos_left ha
  have h1 := hcmp 4 1
  have h2 := hcmp 2 1
  have h3 := hcmp 4 3
  have h4 := hcmp 1 1
  have h5 := hcmp 3 4
  have h6 := hcmp 1 2
  have h7 := hcmp 1 4
  simp only [one_mul] at h1 h2 h3 h4 h5 h6 h7
  simp only [bin,h1,h2,h3,h4,h5,h6,h7]

theorem quadrant_scale (a x y : ℝ) (ha : 0<a) : quadrant (a*x) (a*y)=quadrant x y := by
  have hn : a*x<0 ↔ x<0 := by
    simpa only [mul_zero] using (mul_lt_mul_iff_of_pos_left ha : a*x<a*0 ↔ x<0)
  simp only [quadrant,mul_nonneg_iff_of_pos_left ha,hn]

theorem label_scale (a : ℝ) (ha : 0<a) (v : Vector) : label (a • v)=label v := by
  apply Fin.ext
  simp only [label,Pi.smul_apply,smul_eq_mul,quadrant_scale a _ _ ha,bin_scale a _ _ ha]

def square (v : Vector) : ℝ := ∑ i : Fin 3, (v i)^2
def normalize (v : Vector) : Vector := (Real.sqrt (square v))⁻¹ • v

theorem square_scale (a : ℝ) (v : Vector) : square (a • v)=a^2*square v := by
  simp only [square,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalize_square (v : Vector) (hv : 0<square v) : square (normalize v)=1 := by
  rw [normalize,square_scale,inv_pow,Real.sq_sqrt hv.le]
  exact inv_mul_cancel₀ hv.ne'

theorem label_normalize (v : Vector) (hv : 0<square v) : label (normalize v)=label v :=
  label_scale _ (inv_pos.mpr (Real.sqrt_pos.mpr hv)) v

def slopes (i : Fin 8) : ℝ := ![1/8,3/8,5/8,7/8,7/6,3/2,3,5] i
def sample (i : Fin 32) : Vector :=
  let r := slopes ⟨i.val%8,Nat.mod_lt _ (by decide)⟩
  if i.val/8=0 then ![1,r,0] else if i.val/8=1 then ![-1,r,0] else
  if i.val/8=2 then ![-1,-r,0] else ![1,-r,0]

theorem sample_label (i : Fin 32) : label (sample i)=i := by
  fin_cases i <;> norm_num [label,sample,slopes,quadrant,bin]

theorem sample_square_pos (i : Fin 32) : 0<square (sample i) := by
  fin_cases i <;> norm_num [square,sample,slopes,Fin.sum_univ_succ]

def cell (i : Fin 32) : Set Vector := {v | square v=1 ∧ label v=i}

theorem cell_nonempty (i : Fin 32) : (cell i).Nonempty := by
  refine ⟨normalize (sample i),normalize_square _ (sample_square_pos i),?_⟩
  rw [label_normalize _ (sample_square_pos i),sample_label]

theorem cells_disjoint (i j : Fin 32) (h : i≠j) : Disjoint (cell i) (cell j) := by
  apply Set.disjoint_left.mpr
  intro v hi hj
  exact h (hi.2.symm.trans hj.2)

theorem cells_cover (v : Vector) (hv : square v=1) : ∃ i : Fin 32, v∈cell i :=
  ⟨label v,hv,rfl⟩

def sector (k : Wave) : Fin 32 := label (fun i => (k i : ℝ))
def modeLabels (i : Fin 6) : Fin 32 := ![0,7,4,8,31,20] i

theorem sector_mode (i : Fin 6) : sector (SectorTriadSign.mode i)=modeLabels i := by
  fin_cases i <;> norm_num [sector,label,quadrant,bin,SectorTriadSign.mode,modeLabels]

theorem mode_square_pos (i : Fin 6) : 0<square (fun j => (SectorTriadSign.mode i j : ℝ)) := by
  fin_cases i <;> norm_num [square,SectorTriadSign.mode,Fin.sum_univ_succ]

theorem sector_from_unit_direction (i : Fin 6) :
    normalize (fun j => (SectorTriadSign.mode i j : ℝ))∈cell (modeLabels i) := by
  refine ⟨normalize_square _ (mode_square_pos i),?_⟩
  rw [label_normalize _ (mode_square_pos i)]
  exact sector_mode i

def sectorWeight (j : Fin 32) : ℝ :=
  if j=0 ∨ j=4 ∨ j=8 ∨ j=20 then 4 else if j=7 ∨ j=31 then 1 else 0
def sectorFlux (j : Fin 32) : ℝ :=
  if j=0 ∨ j=8 then 4 else if j=7 ∨ j=31 then -4 else 0

theorem sectorEnergy_exact (j : Fin 32) :
    sectorEnergy SectorTriadSign.modes sector SectorTriadSign.polarization j=sectorWeight j := by
  simp only [sectorEnergy,SectorTriadSign.sum_modes,sector_mode,SectorTriadSign.mode_energy]
  fin_cases j <;> norm_num [Fin.sum_univ_succ,SectorTriadSign.weights,sectorWeight,modeLabels]

theorem sectorTransfer_exact (j : Fin 32) :
    sectorTransfer SectorTriadSign.modes sector SectorTriadSign.polarization j=sectorFlux j := by
  simp only [sectorTransfer,SectorTriadSign.sum_modes,sector_mode,SectorTriadSign.mode_transfer]
  fin_cases j <;> norm_num [Fin.sum_univ_succ,SectorTriadSign.transfers,sectorFlux,modeLabels]

theorem concentration_exact :
    concentration SectorTriadSign.modes sector SectorTriadSign.polarization=11/54 := by
  norm_num [concentration,fraction,SectorTriadSign.energy_exact,sectorEnergy_exact,
    sectorWeight,Fin.sum_univ_succ]

theorem sigma_exact : sigma SectorTriadSign.modes sector SectorTriadSign.polarization=4/27 := by
  norm_num [sigma,fraction,SectorTriadSign.energy_exact,sectorEnergy_exact,sectorWeight,
    sectorTransfer_exact,sectorFlux,SectorTriadSign.totalTransfer_zero,Fin.sum_univ_succ]

theorem rate_exact : rate SectorTriadSign.modes sector SectorTriadSign.polarization= -128/149 := by
  rw [rate,sigma_exact,concentration_exact]
  norm_num

theorem geometric_rate_negative : rate SectorTriadSign.modes sector SectorTriadSign.polarization<0 := by
  rw [rate_exact]
  norm_num

theorem geometric_reversed_rate :
    rate SectorTriadSign.modes sector (fun k i => -SectorTriadSign.polarization k i)=128/149 := by
  rw [rate_neg,rate_exact]
  norm_num

theorem concentrated :
    1/(32 : ℝ)<concentration SectorTriadSign.modes sector SectorTriadSign.polarization := by
  rw [concentration_exact]
  norm_num

theorem no_universal_nonnegative :
    ¬ ∀ V : Field,
      (∀ k, k∉SectorTriadSign.modes → V k=0) →
      (∀ k, dotWave k (V k)=0) →
      (∀ k, V (-k)= -V k) →
      0<energy SectorTriadSign.modes V →
      1/(32 : ℝ)<concentration SectorTriadSign.modes sector V →
        0≤rate SectorTriadSign.modes sector V := by
  intro h
  have hn := h SectorTriadSign.polarization SectorTriadSign.polarization_off
    SectorTriadSign.transverse SectorTriadSign.polarization_odd
    (by rw [SectorTriadSign.energy_exact]; norm_num) concentrated
  exact not_le_of_gt geometric_rate_negative hn

end OperatorDerivativeRewrite.Foundation.AngularTriadPartition
