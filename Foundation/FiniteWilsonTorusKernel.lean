import Foundation.FiniteWilsonTorusGround

/-! Explicit32-state torus quotient candidate and its lifted positive ground.
The microscopic noise and gauge certificates are developed in this module;
none is presumed from the orbit matrix or numerical diagonalization. -/
noncomputable section
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusKernel
abbrev State := Fin 32
abbrev Orbit := Fin 4

def difference (i j : State) : State := ⟨(Nat.xor i.val j.val)%32, Nat.mod_lt _ (by decide)⟩
def orbit (i : State) : Orbit := (![0,2,1,1,1,1,2,3] : Fin 8 → Fin 4) ⟨i.val%8,Nat.mod_lt _ (by decide)⟩
def count : State → ℕ := ![7048,1800,3000,3000,3000,3000,1800,2952,1800,1800,1080,3000,3000,1080,1800,1800,1800,1800,3000,1080,1080,3000,1800,1800,648,1800,1080,1080,1080,1080,1800,648]
def amplitude (i : State) : ℝ := if orbit i=0 then 3 else if orbit i=3 then 1/3 else 1
def kinetic (i j : State) : ℝ := (count (difference i j):ℝ)/65536
def transfer (i j : State) : ℝ := amplitude i*kinetic i j*amplitude j

theorem amplitude_positive (i : State) : 0 < amplitude i := by
  unfold amplitude
  split_ifs <;> norm_num

theorem count_positive (i : State) : 0 < count i := by fin_cases i <;> decide

theorem kinetic_positive (i j : State) : 0 < kinetic i j := by
  exact div_pos (by exact_mod_cast count_positive (difference i j)) (by norm_num)

theorem transfer_positive (i j : State) : 0 < transfer i j :=
  mul_pos (mul_pos (amplitude_positive i) (kinetic_positive i j)) (amplitude_positive j)

theorem transfer_symmetric (i j : State) : transfer i j=transfer j i := by
  have hd : difference i j=difference j i := by simp [difference,Nat.xor_comm]
  simp only [transfer,kinetic,hd]
  ring

private theorem orbit_sum_0 (f : Orbit → ℝ) :
    (∑ j,transfer 0 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 0) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_1 (f : Orbit → ℝ) :
    (∑ j,transfer 1 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 1) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_2 (f : Orbit → ℝ) :
    (∑ j,transfer 2 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 2) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_3 (f : Orbit → ℝ) :
    (∑ j,transfer 3 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 3) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_4 (f : Orbit → ℝ) :
    (∑ j,transfer 4 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 4) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_5 (f : Orbit → ℝ) :
    (∑ j,transfer 5 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 5) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_6 (f : Orbit → ℝ) :
    (∑ j,transfer 6 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 6) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_7 (f : Orbit → ℝ) :
    (∑ j,transfer 7 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 7) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_8 (f : Orbit → ℝ) :
    (∑ j,transfer 8 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 8) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_9 (f : Orbit → ℝ) :
    (∑ j,transfer 9 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 9) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_10 (f : Orbit → ℝ) :
    (∑ j,transfer 10 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 10) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_11 (f : Orbit → ℝ) :
    (∑ j,transfer 11 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 11) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_12 (f : Orbit → ℝ) :
    (∑ j,transfer 12 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 12) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_13 (f : Orbit → ℝ) :
    (∑ j,transfer 13 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 13) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_14 (f : Orbit → ℝ) :
    (∑ j,transfer 14 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 14) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_15 (f : Orbit → ℝ) :
    (∑ j,transfer 15 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 15) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_16 (f : Orbit → ℝ) :
    (∑ j,transfer 16 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 16) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_17 (f : Orbit → ℝ) :
    (∑ j,transfer 17 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 17) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_18 (f : Orbit → ℝ) :
    (∑ j,transfer 18 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 18) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_19 (f : Orbit → ℝ) :
    (∑ j,transfer 19 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 19) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_20 (f : Orbit → ℝ) :
    (∑ j,transfer 20 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 20) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_21 (f : Orbit → ℝ) :
    (∑ j,transfer 21 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 21) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_22 (f : Orbit → ℝ) :
    (∑ j,transfer 22 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 22) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_23 (f : Orbit → ℝ) :
    (∑ j,transfer 23 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 23) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_24 (f : Orbit → ℝ) :
    (∑ j,transfer 24 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 24) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_25 (f : Orbit → ℝ) :
    (∑ j,transfer 25 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 25) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_26 (f : Orbit → ℝ) :
    (∑ j,transfer 26 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 26) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_27 (f : Orbit → ℝ) :
    (∑ j,transfer 27 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 27) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_28 (f : Orbit → ℝ) :
    (∑ j,transfer 28 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 28) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_29 (f : Orbit → ℝ) :
    (∑ j,transfer 29 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 29) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_30 (f : Orbit → ℝ) :
    (∑ j,transfer 30 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 30) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring

private theorem orbit_sum_31 (f : Orbit → ℝ) :
    (∑ j,transfer 31 j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit 31) b*f b := by
  norm_num [transfer,amplitude,kinetic,count,difference,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  ring
/-- Exact aggregation against EVERY function on the four orbits. Row certificates
are split to retain the unchanged default Lean resource limits. -/
theorem orbit_sum (f : Orbit → ℝ) (i : State) :
    (∑ j,transfer i j*f (orbit j))=∑ b,FiniteWilsonTorusGround.block (orbit i) b*f b := by
  fin_cases i
  · exact orbit_sum_0 f
  · exact orbit_sum_1 f
  · exact orbit_sum_2 f
  · exact orbit_sum_3 f
  · exact orbit_sum_4 f
  · exact orbit_sum_5 f
  · exact orbit_sum_6 f
  · exact orbit_sum_7 f
  · exact orbit_sum_8 f
  · exact orbit_sum_9 f
  · exact orbit_sum_10 f
  · exact orbit_sum_11 f
  · exact orbit_sum_12 f
  · exact orbit_sum_13 f
  · exact orbit_sum_14 f
  · exact orbit_sum_15 f
  · exact orbit_sum_16 f
  · exact orbit_sum_17 f
  · exact orbit_sum_18 f
  · exact orbit_sum_19 f
  · exact orbit_sum_20 f
  · exact orbit_sum_21 f
  · exact orbit_sum_22 f
  · exact orbit_sum_23 f
  · exact orbit_sum_24 f
  · exact orbit_sum_25 f
  · exact orbit_sum_26 f
  · exact orbit_sum_27 f
  · exact orbit_sum_28 f
  · exact orbit_sum_29 f
  · exact orbit_sum_30 f
  · exact orbit_sum_31 f

def ground (i : State) : ℝ := FiniteWilsonTorusGround.ground (orbit i)

theorem ground_positive (i : State) : 0 < ground i := FiniteWilsonTorusGround.ground_positive _

theorem ground_eigen (i : State) :
    (∑ j,transfer i j*ground j)=FiniteWilsonTorusGround.value*ground i := by
  change (∑ j,transfer i j*FiniteWilsonTorusGround.ground (orbit j)) = _
  rw [orbit_sum]
  exact FiniteWilsonTorusGround.ground_eigen _

private theorem count_row (i : State) : (∑ j : State,count (difference i j))=65536 := by
  fin_cases i <;> decide

theorem kinetic_rows (i : State) : (∑ j : State,kinetic i j)=1 := by
  have hc : (∑ j : State,(count (difference i j):ℝ))=65536 := by exact_mod_cast count_row i
  unfold kinetic
  rw [← Finset.sum_div,hc]
  norm_num

theorem kinetic_symmetric (i j : State) : kinetic i j=kinetic j i := by
  simp [kinetic,difference,Nat.xor_comm]

end OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusKernel
