import Foundation.PeriodicCoarsePhysicalAveragingObstruction

/-! Sharp coercivity and upper bounds for the actual coarse curl on its physical sector. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarsePhysicalBounds
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarseGramAction PeriodicCoarseSpectrum
open PeriodicCoarsePhysicalSector
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def size (f : Field) : ℝ := dotProduct f f

theorem size_nonneg (f : Field) : 0 ≤ size f := by
  change 0 ≤ ∑ e : CoarseEdge, f e * f e
  exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

theorem size_parseval (f : Field) : size f = 16 * ∑ a : Label, coefficient a f ^ 2 := by
  have h := congrArg (fun v => dotProduct f v) (reconstruction f)
  rw [dotProduct_sum] at h
  simp only [dotProduct_smul, coefficient_dot, smul_eq_mul] at h
  unfold size
  rw [← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem physical_dot_kernel {f g : Field} (hf : f ∈ physicalSpace) (hg : H g = 0) :
    dotProduct f g = 0 := by
  have hk : g ∈ LinearMap.ker H := hg
  rw [gram_kernel_eq_closed] at hk
  exact hf g hk

theorem physical_sector_sum {f : Field} (hf : f ∈ physicalSpace) (T : Finset Direction) :
    dotProduct f (∑ i ∈ T, mode (T,i)) = 0 :=
  physical_dot_kernel hf (H_sector_sum T)

theorem physical_empty_coefficient {f : Field} (hf : f ∈ physicalSpace) (i : Direction) :
    coefficient (∅,i) f = 0 := by
  have hz : H (mode (∅,i)) = 0 := by simp [H_mode]
  have h := physical_dot_kernel hf hz
  rw [coefficient_dot] at h
  linarith

theorem physical_energy_expansion {f : Field} (hf : f ∈ physicalSpace) :
    PeriodicCoarseEnergy.coarseEnergy f =
      16 * ∑ a : Label, (4 * (a.1.card : ℝ)) * coefficient a f ^ 2 := by
  rw [← PeriodicCoarsePhysicalAveragingObstruction.H_energy]
  have hv : f = ∑ a : Label, coefficient a f • mode a := (reconstruction f).symm
  conv_lhs => arg 2; rw [hv]
  rw [map_sum, dotProduct_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, dotProduct_smul, H_mode, dotProduct_sub, dotProduct_smul,
    coefficient_dot]
  have hz : dotProduct f
      (if a.2 ∈ a.1 then (4 : ℝ) • ∑ j ∈ a.1, mode (a.1,j) else 0) = 0 := by
    split_ifs
    · rw [dotProduct_smul, physical_sector_sum hf, smul_zero]
    · exact dotProduct_zero _
  rw [hz]
  simp only [smul_eq_mul]
  ring

theorem physical_coercive {f : Field} (hf : f ∈ physicalSpace) :
    4 * size f ≤ PeriodicCoarseEnergy.coarseEnergy f := by
  rw [size_parseval, physical_energy_expansion hf]
  have hs : (∑ a : Label, 4 * coefficient a f ^ 2) ≤
      ∑ a : Label, (4 * (a.1.card : ℝ)) * coefficient a f ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : a.1 = ∅
    · have hz : coefficient a f = 0 := by
        rw [show a = (∅,a.2) from Prod.ext ha rfl]
        exact physical_empty_coefficient hf _
      rw [hz]
      norm_num
    · have hp : 1 ≤ a.1.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ha)
      have hp' : (1 : ℝ) ≤ (a.1.card : ℝ) := by exact_mod_cast hp
      nlinarith [sq_nonneg (coefficient a f)]
  rw [← Finset.mul_sum] at hs
  linarith

theorem physical_upper {f : Field} (hf : f ∈ physicalSpace) :
    PeriodicCoarseEnergy.coarseEnergy f ≤ 16 * size f := by
  rw [size_parseval, physical_energy_expansion hf]
  have hs : (∑ a : Label, (4 * (a.1.card : ℝ)) * coefficient a f ^ 2) ≤
      ∑ a : Label, 16 * coefficient a f ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    have hc : a.1.card ≤ 4 := by
      calc
        a.1.card ≤ Fintype.card Direction := Finset.card_le_univ _
        _ = 4 := by decide
    have hc' : (a.1.card : ℝ) ≤ 4 := by exact_mod_cast hc
    nlinarith [sq_nonneg (coefficient a f)]
  rw [← Finset.mul_sum] at hs
  linarith

theorem physical_energy_bounds {f : Field} (hf : f ∈ physicalSpace) :
    4 * size f ≤ PeriodicCoarseEnergy.coarseEnergy f ∧
      PeriodicCoarseEnergy.coarseEnergy f ≤ 16 * size f :=
  ⟨physical_coercive hf, physical_upper hf⟩

end OperatorDerivativeRewrite.Foundation.PeriodicCoarsePhysicalBounds
