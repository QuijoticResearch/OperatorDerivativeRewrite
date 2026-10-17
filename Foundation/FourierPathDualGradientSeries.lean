import Foundation.FourierPathDualDamping

/-! Native operator-valued synthesis for conjugate-control heat gradients. -/
noncomputable section
open scoped lp NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualGradientSeries
open L1SeriesSynthesis FourierPathDualControls FourierPathDualDamping
open HigherHeatDyadicLaws HigherHeatFourierBanach HigherHeatFourierPathSemigroup
open FourierPathDirectionalOperator FourierPathDirectionalCharacters

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def symbolMap (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (i : ℕ) : Control m →L[ℝ] ℂ :=
  (frequencyMap levels ξ m i).smulRight (Complex.I * multiplier levels ξ m T i)

theorem symbolMap_apply (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (i : ℕ) (u : Control m) :
    symbolMap levels ξ m T i u =
      eigenvalue (frequency levels ξ (direction m u) i) * multiplier levels ξ m T i := by
  simp only [symbolMap, ContinuousLinearMap.smulRight_apply, frequencyMap_apply,
    Complex.real_smul, eigenvalue]
  ring

def atom (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (i : ℕ) : Control m →L[ℝ] Coeff :=
  ((lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 1 i).restrictScalars ℝ).comp
    (symbolMap levels ξ m T i)

theorem atom_bound (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖atom levels ξ m T i‖ ≤ 1+(T : ℝ)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖(lp.single 1 i (symbolMap levels ξ m T i u) : Coeff)‖ ≤ _
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞)<1), symbolMap_apply]
  exact (damped_frequency_bound levels ξ m u T hT i).trans_eq (mul_comm _ _)

def normalAtom (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (i : ℕ) : Control m →L[ℝ] Coeff :=
  (((1+(T : ℝ)⁻¹)⁻¹ : ℝ) : ℂ) • atom levels ξ m T i

theorem normalAtom_bound (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖normalAtom levels ξ m T i‖ ≤ 1 := by
  have hC : 0 < 1+(T : ℝ)⁻¹ := by positivity
  rw [normalAtom, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hC.le)]
  calc
    _ ≤ (1+(T : ℝ)⁻¹)⁻¹ * (1+(T : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (atom_bound levels ξ m T hT i) (by positivity)
    _ = 1 := inv_mul_cancel₀ hC.ne'

def family (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    Coeff →L[ℂ] (Control m →L[ℝ] Coeff) :=
  ((1+(T : ℝ)⁻¹ : ℝ) : ℂ) •
    synthesis (normalAtom levels ξ m T) (normalAtom_bound levels ξ m T hT)

theorem family_bound (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    ‖family levels ξ m T hT‖ ≤ 1+(T : ℝ)⁻¹ := by
  rw [family, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact mul_le_of_le_one_right (by positivity)
    (synthesis_norm_le (normalAtom levels ξ m T) (normalAtom_bound levels ξ m T hT))

theorem family_tsum (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) (a : Coeff) :
    family levels ξ m T hT a = ∑' i, a i • atom levels ξ m T i := by
  have hC : ((1+(T : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show 1+(T : ℝ)⁻¹ ≠ 0 by positivity)
  change ((1+(T : ℝ)⁻¹ : ℝ) : ℂ) •
    (synthesis (normalAtom levels ξ m T) (normalAtom_bound levels ξ m T hT) a) = _
  rw [synthesis_apply, ← tsum_const_smul'']
  apply tsum_congr
  intro i
  simp only [normalAtom, smul_smul, Complex.ofReal_inv]
  congr 1
  calc
    _ = (((1+(T : ℝ)⁻¹ : ℝ) : ℂ) * ((1+(T : ℝ)⁻¹ : ℝ) : ℂ)⁻¹) * a i := by ring
    _ = a i := by rw [mul_inv_cancel₀ hC, one_mul]

theorem atoms_summable (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) (a : Coeff) :
    Summable (fun i => a i • atom levels ξ m T i) := by
  apply ((coeff_summable a).mul_right (1+(T : ℝ)⁻¹)).of_norm_bounded
  intro i
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (atom_bound levels ξ m T hT i) (norm_nonneg _)

theorem family_coordinate (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (a : Coeff) (u : Control m) (j : ℕ) :
    family levels ξ m T hT a u j = a j * symbolMap levels ξ m T j u := by
  let L : (Control m →L[ℝ] Coeff) →L[ℝ] ℂ :=
    (lp.evalCLM ℝ (fun _ : ℕ => ℂ) 1 j).comp (ContinuousLinearMap.apply ℝ Coeff u)
  have he := L.map_tsum (atoms_summable levels ξ m T hT a)
  change L (family levels ξ m T hT a) = _
  rw [family_tsum, he, tsum_eq_single j]
  · change a j * (lp.single 1 j (symbolMap levels ξ m T j u) : Coeff) j = _
    rw [lp.coeFn_single, Pi.single_eq_same]
  · intro i hi
    change a i * (lp.single 1 i (symbolMap levels ξ m T i u) : Coeff) j = 0
    rw [lp.coeFn_single, Pi.single_eq_of_ne (Ne.symm hi), mul_zero]

theorem family_graph (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (a : Coeff) (u : Control m) :
    (coefficientEvolution levels ξ m T a, family levels ξ m T hT a u) ∈
      coefficientGraph levels ξ (direction m u) := by
  intro i
  rw [family_coordinate, symbolMap_apply]
  change a i * (_ * _) = (a i * _) * _
  ring

theorem family_preserves_kernel (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (a : Coeff) (ha : a ∈ kernel levels ξ) (u : Control m) :
    family levels ξ m T hT a u ∈ kernel levels ξ := by
  have hg : ((kernel levels ξ).mkQ (coefficientEvolution levels ξ m T a),
      (kernel levels ξ).mkQ (family levels ξ m T hT a u)) ∈
      graph levels ξ (direction m u) := ⟨_, family_graph levels ξ m T hT a u, rfl⟩
  have hqa : (kernel levels ξ).mkQ (coefficientEvolution levels ξ m T a) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (evolution_preserves_kernel levels ξ m h.out T a ha)
  rw [hqa] at hg
  exact (Submodule.Quotient.mk_eq_zero _).mp (graph_vertical_zero levels ξ (direction m u) _ hg rfl)

end OperatorDerivativeRewrite.Foundation.FourierPathDualGradientSeries
