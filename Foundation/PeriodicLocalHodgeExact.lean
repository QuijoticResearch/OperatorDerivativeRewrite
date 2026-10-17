import Foundation.PeriodicLocalMultiplicities

/-! Exact local curl-gradient Hodge kernel, tied to the verified spectral multiplicities. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalHodgeExact
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity PeriodicSingleBlockDecomposition
  PeriodicLocalGradientModes PeriodicLocalWalshAction PeriodicLocalSpectralSet
  PeriodicLocalEigenbasis PeriodicLocalMultiplicities
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def characterZ (T : Finset Direction) (x : Vertex) : ℤ :=
  (-1)^(∑ i ∈ T, (x i).val)

def character (T : Finset Direction) (x : Vertex) : ℝ := (characterZ T x : ℝ)

theorem int_character_gradient : ∀ T : Finset Direction, ∀ e : Local,
    gradient (characterZ T) e.val = (-2)*∑ i ∈ T, intWalsh T i e.val := by decide

theorem gradient_character (T : Finset Direction) :
    localGradient (character T) = (-2 : ℝ) • walshSum T := by
  ext e
  have h := int_character_gradient T e
  have hr := congrArg (fun z : ℤ => (z : ℝ)) h
  simpa [localGradient, gradientMap, gradient, character, walshSum, walsh,
    Pi.smul_apply, smul_eq_mul] using hr

theorem walshSum_in_gradient_range (T : Finset Direction) :
    walshSum T ∈ LinearMap.range localGradient := by
  refine ⟨(-1/2 : ℝ) • character T, ?_⟩
  rw [map_smul, gradient_character, smul_smul]
  norm_num

theorem eigenvalue_three_pivot : ∀ a : Label,
    eigenvalue a = 3 ↔ a.val.2 = pivot a := by decide

theorem coreKernel_eq_eigenspace : LinearMap.ker coreIncidence = Module.End.eigenspace H 3 := by
  ext f
  rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff, H_apply]
  exact (PeriodicLocalGradientModes.eigenvalue_three_iff f).symm

theorem gradient_range_eq_coreKernel : LinearMap.range localGradient = LinearMap.ker coreIncidence := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    exact coreIncidence_gradient φ
  · rw [coreKernel_eq_eigenspace]
    have he := eigenspace_eq_span 3
    norm_num at he
    rw [he]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have hp := (eigenvalue_three_pivot a.val).mp a.property
    change mode a.val ∈ LinearMap.range localGradient
    rw [mode, if_pos hp]
    exact walshSum_in_gradient_range a.val.val.1

theorem coreKernel_finrank : Module.finrank ℝ (LinearMap.ker coreIncidence) = 15 := by
  rw [coreKernel_eq_eigenspace]
  exact actual_multiplicities.1

theorem gradient_range_finrank : Module.finrank ℝ (LinearMap.range localGradient) = 15 := by
  rw [gradient_range_eq_coreKernel]
  exact coreKernel_finrank

theorem core_range_finrank : Module.finrank ℝ (LinearMap.range coreIncidence) = 17 := by
  have h := LinearMap.finrank_range_add_finrank_ker coreIncidence
  rw [coreKernel_finrank, Module.finrank_fintype_fun_eq_card, local_card] at h
  omega

theorem actual_matrix_charpoly : localHessian.charpoly =
    (Polynomial.X-Polynomial.C (3 : ℝ))^15 * (Polynomial.X-Polynomial.C (7 : ℝ))^6 *
      (Polynomial.X-Polynomial.C (9 : ℝ))^8 * (Polynomial.X-Polynomial.C (11 : ℝ))^3 := by
  simpa only [H, Matrix.charpoly_toLin'] using charpoly_factorization

end OperatorDerivativeRewrite.Foundation.PeriodicLocalHodgeExact
