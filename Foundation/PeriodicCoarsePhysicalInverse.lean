import Foundation.PeriodicCoarsePhysicalSharp

/-! Unique physical coarse Poisson solution and its sharp squared-norm stability estimate. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarsePhysicalInverse
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarseGramAction
open PeriodicCoarsePhysicalSector PeriodicCoarsePhysicalBounds
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def physicalH : physicalSpace →ₗ[ℝ] physicalSpace where
  toFun f := ⟨H f.val, physicalSpace_invariant f.property⟩
  map_add' f g := by apply Subtype.ext; exact map_add H f.val g.val
  map_smul' r f := by apply Subtype.ext; exact map_smul H r f.val

theorem physicalH_injective : Function.Injective physicalH := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro f hf
    have hz : H f.val = 0 := congrArg Subtype.val hf
    have he := physical_zero_kernel f.val f.property hz
    change f ∈ (⊥ : Submodule ℝ physicalSpace)
    rw [Submodule.mem_bot]
    exact Subtype.ext he
  · exact bot_le

def physicalEquiv : physicalSpace ≃ₗ[ℝ] physicalSpace :=
  LinearEquiv.ofInjectiveEndo physicalH physicalH_injective

def solve : physicalSpace →ₗ[ℝ] physicalSpace := physicalEquiv.symm.toLinearMap

theorem solve_equation (g : physicalSpace) : H (solve g).val = g.val := by
  have h := physicalEquiv.apply_symm_apply g
  exact congrArg Subtype.val h

theorem solve_unique (g u : physicalSpace) (hu : H u.val = g.val) : u = solve g := by
  apply physicalH_injective
  apply Subtype.ext
  exact hu.trans (solve_equation g).symm

theorem size_shift (f : Field) :
    size (H f - (4 : ℝ) • f) =
      size (H f) - 8 * dotProduct f (H f) + 16 * size f := by
  unfold size
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm (H f) f]
  ring

theorem physical_operator_lower {f : Field} (hf : f ∈ physicalSpace) :
    16 * size f ≤ size (H f) := by
  have hc := physical_coercive hf
  rw [← PeriodicCoarsePhysicalAveragingObstruction.H_energy] at hc
  have hs := size_nonneg (H f - (4 : ℝ) • f)
  rw [size_shift] at hs
  linarith

theorem solve_stability (g : physicalSpace) :
    size (solve g).val ≤ (1/16 : ℝ) * size g.val := by
  have h := physical_operator_lower (solve g).property
  rw [solve_equation] at h
  linarith

theorem solve_energy (g : physicalSpace) :
    PeriodicCoarseEnergy.coarseEnergy (solve g).val = dotProduct (solve g).val g.val := by
  rw [← PeriodicCoarsePhysicalAveragingObstruction.H_energy, solve_equation]

theorem solve_stability_attained : ∃ g : physicalSpace,
    0 < size g.val ∧ size (solve g).val = (1/16 : ℝ) * size g.val := by
  let u : physicalSpace := ⟨PeriodicCoarsePhysicalSharp.lowerWitness,
    PeriodicCoarsePhysicalSharp.endpoint_physical.1⟩
  let g : physicalSpace := physicalH u
  have hs : solve g = u := (solve_unique g u rfl).symm
  have hg : g.val = (4 : ℝ) • u.val := by
    change H PeriodicCoarsePhysicalSharp.lowerWitness = _
    rw [PeriodicCoarsePhysicalSharp.lowerWitness, PeriodicCoarseEigenbasis.mode_eigen,
      PeriodicCoarsePhysicalSharp.endpoint_eigenvalues.1]
    rfl
  have hu : size u.val = 16 := PeriodicCoarsePhysicalSharp.endpoint_sizes.1
  have hgs : size g.val = 256 := by
    rw [hg]
    change dotProduct ((4 : ℝ) • u.val) ((4 : ℝ) • u.val) = 256
    rw [smul_dotProduct, dotProduct_smul]
    change 4 * (4 * size u.val) = 256
    rw [hu]
    norm_num
  refine ⟨g, by rw [hgs]; norm_num, ?_⟩
  rw [hs, hu, hgs]
  norm_num

end OperatorDerivativeRewrite.Foundation.PeriodicCoarsePhysicalInverse
