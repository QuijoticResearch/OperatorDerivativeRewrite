import Foundation.PeriodicCoarsePhysicalBounds

/-! Attained lower and upper energy bounds on the actual coarse physical sector. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarsePhysicalSharp
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarseGramAction PeriodicCoarseEigenbasis
open PeriodicCoarsePhysicalSector PeriodicCoarsePhysicalBounds
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def lowerLabel : Label := ({1},0)
def upperLabel : Label := (Finset.univ,1)
def lowerWitness : Field := eigenMode lowerLabel
def upperWitness : Field := eigenMode upperLabel

theorem endpoint_eigenvalues : eigenvalue lowerLabel = 4 ∧ eigenvalue upperLabel = 16 := by
  decide

theorem endpoint_int_sizes :
    (∑ e : CoarseEdge, intEigenMode lowerLabel e * intEigenMode lowerLabel e) = (16 : ℤ) ∧
    (∑ e : CoarseEdge, intEigenMode upperLabel e * intEigenMode upperLabel e) = (32 : ℤ) := by
  decide

theorem endpoint_sizes : size lowerWitness = 16 ∧ size upperWitness = 32 := by
  have hl := endpoint_int_sizes.1
  have hu := endpoint_int_sizes.2
  unfold size lowerWitness upperWitness dotProduct
  simp_rw [eigenMode_int]
  constructor <;> exact_mod_cast (by assumption)

theorem endpoint_physical : lowerWitness ∈ physicalSpace ∧ upperWitness ∈ physicalSpace := by
  constructor
  · exact positiveMode_physical lowerLabel (by rw [endpoint_eigenvalues.1]; norm_num)
  · exact positiveMode_physical upperLabel (by rw [endpoint_eigenvalues.2]; norm_num)

theorem eigen_energy (a : Label) :
    PeriodicCoarseEnergy.coarseEnergy (eigenMode a) =
      (eigenvalue a : ℝ) * size (eigenMode a) := by
  rw [← PeriodicCoarsePhysicalAveragingObstruction.H_energy, mode_eigen, dotProduct_smul]
  rfl

theorem endpoint_energies : PeriodicCoarseEnergy.coarseEnergy lowerWitness = 64 ∧
    PeriodicCoarseEnergy.coarseEnergy upperWitness = 512 := by
  have hl := eigen_energy lowerLabel
  have hu := eigen_energy upperLabel
  rw [endpoint_eigenvalues.1] at hl
  rw [endpoint_eigenvalues.2] at hu
  change PeriodicCoarseEnergy.coarseEnergy lowerWitness = (4 : ℝ) * size lowerWitness at hl
  change PeriodicCoarseEnergy.coarseEnergy upperWitness = (16 : ℝ) * size upperWitness at hu
  rw [endpoint_sizes.1] at hl
  rw [endpoint_sizes.2] at hu
  constructor <;> linarith

theorem endpoint_rayleigh :
    PeriodicCoarseEnergy.coarseEnergy lowerWitness / size lowerWitness = 4 ∧
    PeriodicCoarseEnergy.coarseEnergy upperWitness / size upperWitness = 16 := by
  rw [endpoint_sizes.1, endpoint_sizes.2, endpoint_energies.1, endpoint_energies.2]
  norm_num

theorem no_larger_lower (c : ℝ) (hc : 4 < c) :
    ¬ ∀ f : Field, f ∈ physicalSpace → c * size f ≤ PeriodicCoarseEnergy.coarseEnergy f := by
  intro h
  have hw := h lowerWitness endpoint_physical.1
  rw [endpoint_sizes.1, endpoint_energies.1] at hw
  linarith

theorem no_smaller_upper (c : ℝ) (hc : c < 16) :
    ¬ ∀ f : Field, f ∈ physicalSpace → PeriodicCoarseEnergy.coarseEnergy f ≤ c * size f := by
  intro h
  have hw := h upperWitness endpoint_physical.2
  rw [endpoint_sizes.2, endpoint_energies.2] at hw
  linarith

theorem rayleigh_bounds {f : Field} (hf : f ∈ physicalSpace) (hn : f ≠ 0) :
    4 ≤ PeriodicCoarseEnergy.coarseEnergy f / size f ∧
      PeriodicCoarseEnergy.coarseEnergy f / size f ≤ 16 := by
  have hp : 0 < size f :=
    lt_of_le_of_ne (size_nonneg f) (Ne.symm (fun h => hn (dotProduct_self_eq_zero.mp h)))
  exact ⟨(le_div_iff₀ hp).mpr (physical_coercive hf),
    (div_le_iff₀ hp).mpr (physical_upper hf)⟩

end OperatorDerivativeRewrite.Foundation.PeriodicCoarsePhysicalSharp
