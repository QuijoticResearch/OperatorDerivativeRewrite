import Foundation.PeriodicLocalTransverseSharp

/-! The actual local transverse space: dimension, eigenvalue set and upper energy bound. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalTransverseSpace
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity PeriodicSingleBlockDecomposition
  PeriodicLocalGradientModes PeriodicLocalWalshAction PeriodicLocalSpectralSet
  PeriodicLocalEigenbasis PeriodicLocalMultiplicities PeriodicLocalHodgeExact
  PeriodicLocalTransverseGap PeriodicLocalTransverseSharp
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def transverseSpace : Submodule ℝ Field where
  carrier := transverse
  zero_mem' := by intro φ; exact zero_dotProduct _
  add_mem' := by
    intro f g hf hg φ
    rw [add_dotProduct, hf φ, hg φ, add_zero]
  smul_mem' := by
    intro c f hf φ
    rw [smul_dotProduct, hf φ, smul_zero]

theorem eigenbasis_dot_dual (f : Field) (a : Label) :
    dotProduct f (dual a) = (8*(a.val.1.card : ℝ))*eigenBasis.repr f a := by
  have h := congrArg (fun v => dotProduct v (dual a)) (eigenBasis.sum_repr f)
  rw [sum_dotProduct] at h
  simp only [smul_dotProduct, eigenBasis_apply, mode_dual_pair, smul_eq_mul] at h
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  calc
    _ = eigenBasis.repr f a * (8*(a.val.1.card : ℝ)) := h.symm
    _ = _ := mul_comm _ _

theorem pivot_dual_eq_sum (a : Label) (ha : eigenvalue a = 3) : dual a = walshSum a.val.1 := by
  have hp := (eigenvalue_three_pivot a).mp ha
  ext e
  simp [dual, intDual, hp, walshSum, walsh]

theorem transverse_three_coefficient {f : Field} (hf : transverse f) (a : Label)
    (ha : eigenvalue a = 3) : eigenBasis.repr f a = 0 := by
  have h := eigenbasis_dot_dual f a
  rw [pivot_dual_eq_sum a ha, transverse_sum hf] at h
  have hp : 0 < a.val.1.card := Finset.card_pos.mpr ⟨a.val.2, a.property⟩
  have hp' : 0 < (a.val.1.card : ℝ) := by exact_mod_cast hp
  exact (mul_eq_zero.mp h.symm).resolve_left (by positivity)

theorem transverseSpace_eq_span : transverseSpace = Submodule.span ℝ
    (Set.range (fun a : {a : Label // eigenvalue a ≠ 3} => mode a.val)) := by
  apply le_antisymm
  · intro f hf
    rw [← eigenBasis.sum_repr f]
    apply Submodule.sum_mem
    intro a _
    rw [eigenBasis_apply]
    by_cases ha : eigenvalue a = 3
    · rw [transverse_three_coefficient hf a ha, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change transverse (mode a.val)
    apply eigenvector_transverse _ _ (mode_eigen a.val)
    exact_mod_cast a.property

theorem transverseSpace_finrank : Module.finrank ℝ transverseSpace = 17 := by
  rw [transverseSpace_eq_span]
  have hi : LinearIndependent ℝ (fun a : {a : Label // eigenvalue a ≠ 3} => mode a.val) :=
    mode_linearIndependent.comp _ Subtype.val_injective
  have h := finrank_span_eq_card hi
  have hc : Fintype.card {a : Label // eigenvalue a ≠ 3} = 17 := by decide
  exact h.trans hc

theorem transverse_upper_bound {f : Field} (hf : transverse f) : energy f ≤ 11*squaredSize f := by
  rw [transverse_energy_expansion hf, squaredSize_parseval]
  have hs : (∑ a : Label, (3+2*(a.val.1.card : ℝ))*coeff f a ^ 2) ≤
      ∑ a : Label, 11*coeff f a ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    have hc : a.val.1.card ≤ 4 := by
      have h := Finset.card_le_univ a.val.1
      simpa using h
    have hc' : (a.val.1.card : ℝ) ≤ 4 := by exact_mod_cast hc
    nlinarith [sq_nonneg (coeff f a)]
  rw [← Finset.mul_sum] at hs
  nlinarith

theorem transverse_internal_upper {f : Field} (hf : transverse f) :
    coreEnergy f ≤ 8*squaredSize f := by
  have h := transverse_upper_bound hf
  rw [exact_energy_decomposition] at h
  linarith

theorem transverse_no_eigenvalue_three (f : Field) (hf : transverse f) (hn : f ≠ 0) :
    H f ≠ (3 : ℝ) • f := by
  intro he
  have hc : coreIncidence f = 0 :=
    (PeriodicLocalGradientModes.eigenvalue_three_iff f).mp he
  have hr : f ∈ LinearMap.range localGradient := by
    rw [gradient_range_eq_coreKernel]
    exact hc
  obtain ⟨φ, hφ⟩ := hr
  have h := hf φ
  rw [hφ] at h
  have hz : squaredSize f = 0 := by
    simpa only [dotProduct, PeriodicSingleBlockCoercivity.squaredSize, pow_two] using h
  exact hn ((squaredSize_zero_iff f).mp hz)

theorem transverse_eigenvalue_iff (ell : ℝ) :
    (∃ f : Field, transverse f ∧ f ≠ 0 ∧ H f = ell • f) ↔
      ell=7 ∨ ell=9 ∨ ell=11 := by
  constructor
  · rintro ⟨f, hf, hn, he⟩
    have h := PeriodicLocalSpectralSet.eigenvalue_mem ell f hn he
    rcases h with h | h | h | h
    · exact False.elim (transverse_no_eigenvalue_three f hf hn (h ▸ he))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (rfl | rfl | rfl)
    · exact ⟨witness, witness_transverse, witness_nonzero, witness_eigen⟩
    · obtain ⟨f, hn, he⟩ := eigenvalue_nine_exists
      exact ⟨f, eigenvector_transverse f 9 he (by norm_num), hn, he⟩
    · obtain ⟨f, hn, he⟩ := eigenvalue_eleven_exists
      exact ⟨f, eigenvector_transverse f 11 he (by norm_num), hn, he⟩

theorem H_preserves_transverse {f : Field} (hf : transverse f) : transverse (H f) := by
  intro φ
  rw [← H_dot_symmetric f (localGradient φ)]
  have hg : H (localGradient φ) = (3 : ℝ) • localGradient φ := gradient_eigenvalue_three φ
  rw [hg, dotProduct_smul, hf φ, smul_zero]

theorem eigenvector_energy (f : Field) (ell : ℝ) (he : H f = ell • f) :
    energy f = ell*squaredSize f := by
  calc
    _ = dotProduct f (H f) := (hessian_energy f).symm
    _ = _ := by
      rw [he, dotProduct_smul]
      simp only [smul_eq_mul, dotProduct, PeriodicSingleBlockCoercivity.squaredSize, pow_two]

theorem no_smaller_transverse_upper (c : ℝ) (hc : c < 11) :
    ¬ ∀ f : Field, transverse f → energy f ≤ c*squaredSize f := by
  intro h
  obtain ⟨f, hn, he⟩ := eigenvalue_eleven_exists
  have ht := eigenvector_transverse f 11 he (by norm_num)
  have hb := h f ht
  rw [eigenvector_energy f 11 he] at hb
  have h0 : 0 ≤ squaredSize f := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hz : squaredSize f ≠ 0 := fun h => hn ((squaredSize_zero_iff f).mp h)
  have hp : 0 < squaredSize f := lt_of_le_of_ne h0 (Ne.symm hz)
  nlinarith

theorem no_smaller_internal_upper (c : ℝ) (hc : c < 8) :
    ¬ ∀ f : Field, transverse f → coreEnergy f ≤ c*squaredSize f := by
  intro h
  obtain ⟨f, hn, he⟩ := eigenvalue_eleven_exists
  have ht := eigenvector_transverse f 11 he (by norm_num)
  have hb := h f ht
  have hE := eigenvector_energy f 11 he
  rw [exact_energy_decomposition] at hE
  have h0 : 0 ≤ squaredSize f := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hz : squaredSize f ≠ 0 := fun h => hn ((squaredSize_zero_iff f).mp h)
  have hp : 0 < squaredSize f := lt_of_le_of_ne h0 (Ne.symm hz)
  nlinarith

end OperatorDerivativeRewrite.Foundation.PeriodicLocalTransverseSpace
