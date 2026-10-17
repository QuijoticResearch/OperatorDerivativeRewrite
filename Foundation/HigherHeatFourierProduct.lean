import Foundation.HigherHeatFourierCalculus
import Foundation.HigherHeatFourierBracket

/-! A finite-grid stochastic product rule with the actual signed spectral compensator. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierProduct
open HigherHeatL2 HigherHeatCylinderFourier HigherHeatBackwardFourier HigherHeatFourierInnovations
open HigherHeatFourierCalculus HigherHeatFourierCovariance

def backwardProduct (m : ℕ) (T t : ℝ≥0) (ξ η x : ℝ) : ℂ :=
  backwardCharacter m T t ξ x*backwardCharacter m T t η x

def coefficient (m : ℕ) (T t : ℝ≥0) (ξ η x : ℝ) : ℂ :=
  symbol m (T-t) ξ*symbol m (T-t) η*phase (ξ+η) x

def compensator (m : ℕ) (T s t : ℝ≥0) (ξ η x : ℝ) : ℂ :=
  coefficient m T t ξ η x*covariance m (t-s) ξ η

theorem transition_product (m : ℕ) (hm : 0 < m) (T s t : ℝ≥0) (hst : s < t)
    (ξ η x : ℝ) :
    transition m hm (t-s) (tsub_pos_iff_lt.mpr hst) (backwardProduct m T t ξ η) x=
      coefficient m T t ξ η x*symbol m (t-s) (ξ+η) := by
  have he : backwardProduct m T t ξ η=
      (fun y => (symbol m (T-t) ξ*symbol m (T-t) η)*phase (ξ+η) y) := by
    funext y
    simp only [backwardProduct,backwardCharacter,phase_frequency_add]
    ring
  rw [he,transition_scaled_phase]
  unfold coefficient
  ring

theorem conditional_product_defect (m : ℕ) (hm : 0 < m) (T s t : ℝ≥0)
    (hst : s < t) (ht : t ≤ T) (ξ η x : ℝ) :
    transition m hm (t-s) (tsub_pos_iff_lt.mpr hst) (backwardProduct m T t ξ η) x-
      backwardProduct m T s ξ η x=compensator m T s t ξ η x := by
  have he : (T-t)+(t-s)=T-s := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,NNReal.coe_sub ht,NNReal.coe_sub hst.le,
      NNReal.coe_sub (hst.le.trans ht)]
    ring
  have hξ := symbol_add m (T-t) (t-s) ξ
  have hη := symbol_add m (T-t) (t-s) η
  rw [he] at hξ hη
  rw [transition_product m hm T s t hst]
  simp only [backwardProduct,backwardCharacter,hξ,hη,compensator,coefficient,covariance,
    phase_frequency_add]
  ring

def martingaleStep (m : ℕ) (T s t : ℝ≥0) (ξ η x z : ℝ) : ℂ :=
  backwardCharacter m T s ξ x*gain m T s t η x z+
    backwardCharacter m T s η x*gain m T s t ξ x z+
    coefficient m T t ξ η x*
      (innovation m (t-s) ξ z*innovation m (t-s) η z-covariance m (t-s) ξ η)

theorem martingale_step_factor (m : ℕ) (T s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ T)
    (ξ η x z : ℝ) :
    martingaleStep m T s t ξ η x z=
      coefficient m T t ξ η x*innovation m (t-s) (ξ+η) z := by
  have he : (T-t)+(t-s)=T-s := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,NNReal.coe_sub ht,NNReal.coe_sub hst,NNReal.coe_sub (hst.trans ht)]
    ring
  have hξ := symbol_add m (T-t) (t-s) ξ
  have hη := symbol_add m (T-t) (t-s) η
  rw [he] at hξ hη
  simp only [martingaleStep,backwardCharacter,hξ,hη,gain,coefficient,
    phase_frequency_add,innovation,covariance]
  ring

theorem coefficient_bound (m : ℕ) (T t : ℝ≥0) (ξ η x : ℝ) :
    ‖coefficient m T t ξ η x‖ ≤ 1 := by
  simp only [coefficient,norm_mul,phase_norm,mul_one]
  exact mul_le_one₀ (symbol_norm_le m (T-t) ξ) (norm_nonneg _) (symbol_norm_le m (T-t) η)

theorem actual_past_martingale_step_zero {ι : Type*} [Fintype ι] (m : ℕ) (hm : 0 < m)
    (times : ι → ℝ≥0) (htimes : ∀ i, 0 < times i) (T s t : ℝ≥0)
    (hst : s < t) (ht : t ≤ T) (ξ η : ℝ) :
    (∫ᵛ w, martingaleStep m T s t ξ η (∑ i, w.1 i) w.2
      ∂<•extendedLaw (Measure.pi (fun _ : ι => volume))
        (HigherHeatSignedLaws.incrementDensity m hm times htimes) m hm (t-s)
        (tsub_pos_iff_lt.mpr hst))=0 := by
  have he : (fun w : (ι → ℝ) × ℝ => martingaleStep m T s t ξ η (∑ i, w.1 i) w.2)=
      (fun w : (ι → ℝ) × ℝ => coefficient m T t ξ η (∑ i, w.1 i)*
        innovation m (t-s) (ξ+η) w.2) := by
    funext w
    exact martingale_step_factor m T s t hst.le ht ξ η _ _
  rw [he]
  exact HigherHeatFourierInnovations.actual_past_gain_zero m hm times htimes (t-s)
    (tsub_pos_iff_lt.mpr hst) (ξ+η) (fun w => coefficient m T t ξ η (∑ i, w i))
    (by unfold coefficient HigherHeatCylinderFourier.phase; fun_prop) 1
    (fun w => coefficient_bound m T t ξ η _)

theorem product_step (m : ℕ) (T s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ T)
    (ξ η x z : ℝ) :
    backwardProduct m T t ξ η (x+z)-backwardProduct m T s ξ η x=
      martingaleStep m T s t ξ η x z+compensator m T s t ξ η x := by
  have hξ := backward_gain_factor m T s t hst ht ξ x z
  have hη := backward_gain_factor m T s t hst ht η x z
  have hx : backwardCharacter m T t ξ (x+z)=
      backwardCharacter m T s ξ x+gain m T s t ξ x z := by
    dsimp only [gain]
    linear_combination hξ
  have hy : backwardCharacter m T t η (x+z)=
      backwardCharacter m T s η x+gain m T s t η x z := by
    dsimp only [gain]
    linear_combination hη
  simp only [backwardProduct,hx,hy,martingaleStep,compensator,coefficient,gain,phase_frequency_add]
  ring

theorem finite_product_rule (m : ℕ) (T : ℝ≥0) (grid : ℕ → ℝ≥0) (n : ℕ)
    (hg : Monotone grid) (hT : grid n ≤ T) (ξ η : ℝ) (x : ℕ → ℝ) :
    backwardProduct m T (grid n) ξ η (x n)-backwardProduct m T (grid 0) ξ η (x 0)=
      (∑ j ∈ Finset.range n,
        martingaleStep m T (grid j) (grid (j+1)) ξ η (x j) (x (j+1)-x j))+
      (∑ j ∈ Finset.range n, compensator m T (grid j) (grid (j+1)) ξ η (x j)) := by
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ Finset.range n,
        (backwardProduct m T (grid (j+1)) ξ η (x (j+1))-
          backwardProduct m T (grid j) ξ η (x j)) :=
      (Finset.sum_range_sub (fun j => backwardProduct m T (grid j) ξ η (x j)) n).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [add_sub_cancel] using product_step m T (grid j) (grid (j+1))
        (hg (by omega)) ((hg (by have := Finset.mem_range.mp hj; omega)).trans hT)
        ξ η (x j) (x (j+1)-x j)

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierProduct
