import Foundation.FourierPathControlSymbols
import Foundation.FourierPathHeatGradient

/-! Actual absolutely summable operator-valued control gradients. -/
noncomputable section
open scoped lp NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathControlGradientSeries
open L1SeriesSynthesis FourierPathBoundedControls FourierPathControlSymbols
open HigherHeatDyadicLaws HigherHeatFourierBanach HigherHeatFourierPathSemigroup
open FourierPathDirectionalOperator

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def atom (m : ℕ) (T : ℝ≥0) (i : ℕ) : Control →L[ℝ] Coeff :=
  ((lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 1 i).restrictScalars ℝ).comp
    (symbolMap levels ξ m T i)

theorem atom_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖atom levels ξ m T i‖ ≤ 1+(T:ℝ)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖(lp.single 1 i (symbolMap levels ξ m T i u) : Coeff)‖ ≤ _
  rw [lp.norm_single (by norm_num : (0:ℝ≥0∞)<1)]
  exact (symbolMap levels ξ m T i).le_of_opNorm_le (symbolMap_norm levels ξ m hm T hT i) u

theorem term_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖term (atom levels ξ m T) i‖ ≤ 1+(T:ℝ)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  change ‖z • atom levels ξ m T i‖ ≤ _
  rw [norm_smul]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (atom_bound levels ξ m hm T hT i) (norm_nonneg z)

def family (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Coeff →L[ℂ] (Control →L[ℝ] Coeff) :=
  (lp.tsumCLM ℂ ℕ (Control →L[ℝ] Coeff)).comp
    (lp.mapCLM 1 (term (atom levels ξ m T)) (by positivity)
      (term_bound levels ξ m hm T hT))

theorem family_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ‖family levels ξ m hm T hT‖ ≤ 1+(T:ℝ)⁻¹ := by
  calc
    _ ≤ ‖lp.tsumCLM ℂ ℕ (Control →L[ℝ] Coeff)‖ *
        ‖lp.mapCLM 1 (term (atom levels ξ m T)) (by positivity)
          (term_bound levels ξ m hm T hT)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*(1+(T:ℝ)⁻¹) := mul_le_mul lp.norm_tsumCLM_le (lp.norm_mapCLM_le 1 _ _ _)
      (norm_nonneg _) (by positivity)
    _ = _ := one_mul _

theorem atoms_summable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (a : Coeff) :
    Summable (fun i => a i • atom levels ξ m T i) := by
  let b := lp.mapCLM 1 (term (atom levels ξ m T)) (by positivity)
    (term_bound levels ξ m hm T hT) a
  apply Summable.of_norm
  simpa [b, term] using b.property.summable (by norm_num)

theorem family_coordinate (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (a : Coeff) (u : Control) (j : ℕ) :
    family levels ξ m hm T hT a u j = a j * symbolMap levels ξ m T j u := by
  let L : (Control →L[ℝ] Coeff) →L[ℝ] ℂ :=
    (lp.evalCLM ℝ (fun _ : ℕ => ℂ) 1 j).comp (ContinuousLinearMap.apply ℝ Coeff u)
  have he := L.map_tsum (atoms_summable levels ξ m hm T hT a)
  change (family levels ξ m hm T hT a u) j = _
  change L (∑' i, a i • atom levels ξ m T i) = _
  rw [he, tsum_eq_single j]
  · change a j * (lp.single 1 j (symbolMap levels ξ m T j u) : Coeff) j = _
    rw [lp.coeFn_single, Pi.single_eq_same]
  · intro i hi
    change a i * (lp.single 1 i (symbolMap levels ξ m T i u) : Coeff) j = 0
    rw [lp.coeFn_single, Pi.single_eq_of_ne (Ne.symm hi), mul_zero]

theorem family_graph (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (a : Coeff) (u : Control) :
    (coefficientEvolution levels ξ m T a, family levels ξ m hm T hT a u) ∈
      coefficientGraph levels ξ (direction u) := by
  intro i
  rw [family_coordinate, symbolMap_apply]
  change a i * (_ * _) = (a i * _) * _
  ring

theorem family_preserves_kernel (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (a : Coeff) (ha : a ∈ kernel levels ξ) (u : Control) :
    family levels ξ m hm T hT a u ∈ kernel levels ξ := by
  have hg : ((kernel levels ξ).mkQ (coefficientEvolution levels ξ m T a),
      (kernel levels ξ).mkQ (family levels ξ m hm T hT a u)) ∈
      graph levels ξ (direction u) := ⟨_, family_graph levels ξ m hm T hT a u, rfl⟩
  have hqa : (kernel levels ξ).mkQ (coefficientEvolution levels ξ m T a) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (evolution_preserves_kernel levels ξ m hm T a ha)
  rw [hqa] at hg
  exact (Submodule.Quotient.mk_eq_zero _).mp (graph_vertical_zero levels ξ (direction u) _ hg rfl)

end OperatorDerivativeRewrite.Foundation.FourierPathControlGradientSeries
