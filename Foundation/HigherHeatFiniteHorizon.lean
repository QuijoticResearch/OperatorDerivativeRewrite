import Foundation.HigherHeatKernelScaling

/-! A finite-horizon signed path realization obstruction for higher even-order heat. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFiniteHorizon
open HigherHeatSignedLaws HigherHeatKernelMoments HigherHeatPathObstruction HigherHeatKernelScaling

def contraction (n : ℕ) : ℝ≥0 := ((n+1 : ℕ) : ℝ≥0)⁻¹

theorem contraction_pos (n : ℕ) : 0 < contraction n := by unfold contraction; positivity

def duration (m : ℕ) (T : ℝ≥0) (n : ℕ) : ℝ≥0 := T*(contraction n)^(2*m)

theorem duration_pos (m : ℕ) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : 0 < duration m T n :=
  mul_pos hT (pow_pos (contraction_pos n) _)

theorem grid_time_le (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (n i : ℕ) (hi : i ≤ n+1) :
    (i : ℝ≥0)*duration m T n ≤ T := by
  have hn : (1 : ℝ≥0) ≤ ((n+1 : ℕ) : ℝ≥0) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hiR : (i : ℝ≥0) ≤ ((n+1 : ℕ) : ℝ≥0) := by exact_mod_cast hi
  have hp : (i : ℝ≥0) ≤ (((n+1 : ℕ) : ℝ≥0))^(2*m) :=
    hiR.trans (le_self_pow₀ hn (by omega))
  calc
    (i : ℝ≥0)*duration m T n ≤ (((n+1 : ℕ) : ℝ≥0))^(2*m)*duration m T n :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = T := by
      unfold duration contraction
      rw [inv_pow]
      have hne : (((n+1 : ℕ) : ℝ≥0))^(2*m) ≠ 0 := by positivity
      field_simp

def gridIncrement (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (n : ℕ)
    (ω : Set.Iic T → ℝ) (i : Fin n) : ℝ :=
  ω ⟨((i.val+1 : ℕ) : ℝ≥0)*duration m T n,grid_time_le m hm T n (i.val+1) (by omega)⟩ -
    ω ⟨(i.val : ℝ≥0)*duration m T n,grid_time_le m hm T n i.val (by omega)⟩

theorem gridIncrement_measurable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (n : ℕ) :
    Measurable (gridIncrement m hm T n) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply _).sub (measurable_pi_apply _)

theorem no_signed_grid_realization {Ω : Type*} [MeasurableSpace Ω] (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T)
    (μ : SignedMeasure Ω) (observation : (n : ℕ) → Ω → (Fin n → ℝ))
    (hobs : ∀ n, Measurable (observation n))
    (hlaw : ∀ n, μ.map (observation n) =
      incrementLaw m (by omega) (fun _ : Fin n => duration m T n)
        (fun _ => duration_pos m T hT n)) : False := by
  let C : ℝ := ∫ x : ℝ, ‖realKernel m (by omega : 0 < m) T hT x‖
  have hC : 1 < C := norm_integral_gt_one m hm T hT
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (μ.variation Set.univ).toReal hC
  have hb := variation_mass_map_le μ (observation n) (hobs n)
  rw [hlaw n,incrementLaw_variation_mass] at hb
  simp only [duration,norm_integral_scaling m (by omega) T (contraction n) hT (contraction_pos n),
    Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hb
  exact (not_lt_of_ge hb) hn

theorem no_signed_path_law (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T)
    (μ : SignedMeasure (Set.Iic T → ℝ))
    (hlaw : ∀ n, μ.map (gridIncrement m (by omega) T n) =
      incrementLaw m (by omega) (fun _ : Fin n => duration m T n)
        (fun _ => duration_pos m T hT n)) : False :=
  no_signed_grid_realization m hm T hT μ (gridIncrement m (by omega) T)
    (gridIncrement_measurable m (by omega) T) hlaw

end OperatorDerivativeRewrite.Foundation.HigherHeatFiniteHorizon
