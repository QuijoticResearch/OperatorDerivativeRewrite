import Foundation.IBMNonlinearClockEnergy

/-! Uniform actual native clock-gradient energy for arbitrary deterministic
L2 time weights. Finite-width integrability uses the original bounded covariance;
the uniform row bound uses the existing null-diagonal time-kernel estimate. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockTimeWeightEnergy
open InfiniteGaussian IBMClockOverlapEnergy IBMFoldedTransitionBound IBMNonlinearClockField
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem covariance_row_integrable (n m : ℕ) (s T : ℝ) :
    Integrable (fun t => covariance n m s t) (window T) := by
  obtain ⟨M,_,hM⟩ := covariance_bounded n m
  apply Integrable.of_bound ((covariance_measurable n m).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
  exact ae_of_all _ fun t => by
    change ‖covariance n m s t‖ ≤ M
    rw [Real.norm_of_nonneg (covariance_nonneg _ _ _ _)]
    exact hM _ _

theorem covariance_row_bound (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ s ∂window T, (∫ t, covariance n m s t ∂window T) ≤ 8*peak 1*Real.sqrt T := by
  have hoff := Measure.ae_ae_of_ae_prod (window_off_diagonal T)
  filter_upwards [ae_restrict_mem measurableSet_Ioc,hoff] with s hs hn
  calc
    _ ≤ ∫ t, (2*peak 1)*timeKernel T s t ∂window T := by
      apply integral_mono_ae (covariance_row_integrable n m s T)
        ((timeKernel_row_integrable hT s).integrableOn.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc,hn] with t ht hne
      exact covariance_off_diagonal_le n m hs ht hne
    _ = (2*peak 1)*(∫ t, timeKernel T s t ∂window T) := integral_const_mul _ _
    _ ≤ (2*peak 1)*(4*Real.sqrt T) :=
      mul_le_mul_of_nonneg_left (timeKernel_row_bound hT s)
        (mul_nonneg (by norm_num) (peak_nonneg _))
    _ = _ := by ring

theorem envelope_row_bound (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ s ∂window T, (∫ t, covariance n m s t+4 ∂window T) ≤
      8*peak 1*Real.sqrt T+4*T := by
  filter_upwards [covariance_row_bound n m hT] with s hs
  rw [integral_add (covariance_row_integrable n m s T) (integrable_const 4),integral_const]
  change _+(window T).real univ*4 ≤ _
  rw [IBMNonlinearClockEnergy.window_mass hT]
  linarith

theorem weighted_integrable (n : ℕ) (g : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hg : MemLp g 2 (window T)) : Integrable (fun t => g t • field n t) (window T) := by
  obtain ⟨C,hC,hb⟩ := IBMNonlinearClockColumn.column_bounded n
  apply ((hg.integrable (by norm_num)).norm.mul_const (C*Real.sqrt T)).mono'
    (hg.aestronglyMeasurable.smul (field_stronglyMeasurable n).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  change ‖g t • field n t‖ ≤ ‖g t‖ * (C*Real.sqrt T)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    ((field_norm_bound n hC hb t).trans
      (mul_le_mul_of_nonneg_left (IBMClockAverageCandidate.direction_norm_bound hT ht) hC))
    (norm_nonneg _)

def majorant (n : ℕ) (g : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (g p.1)^2*(covariance n n p.1 p.2+4)

theorem majorant_integrable (n : ℕ) (g : ℝ → ℝ) (T : ℝ)
    (hg : MemLp g 2 (window T)) :
    Integrable (majorant n g) ((window T).prod (window T)) := by
  obtain ⟨M,_,hM⟩ := covariance_bounded n n
  apply (hg.integrable_sq.mul_prod
    (integrable_const (M+4) : Integrable (fun _ : ℝ => M+4) (window T))).mono'
    ((hg.aestronglyMeasurable.comp_fst.pow 2).mul
      ((covariance_measurable n n).add measurable_const).aestronglyMeasurable)
  exact ae_of_all _ fun p => by
    change ‖(g p.1)^2*(covariance n n p.1 p.2+4)‖ ≤ (g p.1)^2*(M+4)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (add_nonneg (covariance_nonneg _ _ _ _) (by norm_num)))]
    exact mul_le_mul_of_nonneg_left (by linarith [hM p.1 p.2]) (sq_nonneg _)

theorem majorant_integral_bound (n : ℕ) (g : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hg : MemLp g 2 (window T)) :
    (∫ p, majorant n g p ∂(window T).prod (window T)) ≤
      (8*peak 1*Real.sqrt T+4*T)*(∫ t, (g t)^2 ∂window T) := by
  rw [integral_prod _ (majorant_integrable n g T hg)]
  change (∫ s, ∫ t, (g s)^2*(covariance n n s t+4) ∂window T ∂window T) ≤ _
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∫ s, (g s)^2*(8*peak 1*Real.sqrt T+4*T) ∂window T := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun s => mul_nonneg (sq_nonneg _)
          (integral_nonneg fun t => add_nonneg (covariance_nonneg _ _ _ _) (by norm_num)))
        (hg.integrable_sq.mul_const _)
      filter_upwards [envelope_row_bound n n hT] with s hs
      exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

/-- Genuine ORIGINAL full-vector Bochner integral, arbitrary rough L2 time
weight, and a constant independent of smoothing width n. -/
theorem weighted_energy (n : ℕ) (g : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hg : MemLp g 2 (window T)) :
    ‖∫ t, g t • field n t ∂window T‖^2 ≤
      (8*peak 1*T*Real.sqrt T+4*T^2)*(∫ t, (g t)^2 ∂window T) := by
  let f : ℝ → IBMClockAverageCandidate.Target := fun t => g t • field n t
  have hf := weighted_integrable n g hT hg
  have hi : Integrable (fun p : ℝ × ℝ => inner ℝ (f p.1) (f p.2))
      ((window T).prod (window T)) :=
    (hf.norm.mul_prod hf.norm).mono'
      (hf.aestronglyMeasurable.comp_fst.inner (𝕜 := ℝ) hf.aestronglyMeasurable.comp_snd)
      (ae_of_all _ fun p => norm_inner_le_norm _ _)
  have he : ‖∫ t, f t ∂window T‖^2 =
      ∫ p : ℝ × ℝ, inner ℝ (f p.1) (f p.2) ∂(window T).prod (window T) := by
    rw [← real_inner_self_eq_norm_sq,real_inner_comm,← integral_inner hf,integral_prod _ hi]
    apply integral_congr_ae
    exact ae_of_all _ fun t => by
      change inner ℝ (∫ s, f s ∂window T) (f t) = _
      rw [real_inner_comm,← integral_inner hf]
  have hm := majorant_integrable n g T hg
  have hp : ∀ᵐ p : ℝ × ℝ ∂(window T).prod (window T),
      inner ℝ (f p.1) (f p.2) ≤ T*((majorant n g p+majorant n g p.swap)/2) := by
    filter_upwards [window_pair_mem T] with p hp
    have hk : 0 ≤ covariance n n p.1 p.2+4 :=
      add_nonneg (covariance_nonneg _ _ _ _) (by norm_num)
    have hb := field_inner_bound n n hp.1.1.le hp.2.1.le
    have hb' : |inner ℝ (field n p.1) (field n p.2)| ≤ T*(covariance n n p.1 p.2+4) := by
      exact hb.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans hp.1.2) hk)
    have habs : |g p.1| * |g p.2| ≤ ((g p.1)^2+(g p.2)^2)/2 := by
      nlinarith [sq_nonneg (|g p.1|-|g p.2|),sq_abs (g p.1),sq_abs (g p.2)]
    have hfirst : inner ℝ (f p.1) (f p.2) ≤
        (|g p.1| * |g p.2|)*(T*(covariance n n p.1 p.2+4)) := by
      calc
        _ ≤ |inner ℝ (f p.1) (f p.2)| := le_abs_self _
        _ = (|g p.1| * |g p.2|) * |inner ℝ (field n p.1) (field n p.2)| := by
          simp only [f,real_inner_smul_left,inner_smul_right,abs_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hb' (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hlast := mul_le_mul_of_nonneg_right habs (mul_nonneg hT hk)
    dsimp only [majorant,Prod.fst_swap,Prod.snd_swap]
    rw [covariance_swap n n p.2 p.1]
    nlinarith
  change ‖∫ t, f t ∂window T‖^2 ≤ _
  calc
    _ = _ := he
    _ ≤ ∫ p : ℝ × ℝ, T*((majorant n g p+majorant n g p.swap)/2)
        ∂(window T).prod (window T) :=
      integral_mono_ae hi (((hm.add hm.swap).div_const 2).const_mul T) hp
    _ = T*(∫ p, majorant n g p ∂(window T).prod (window T)) := by
      rw [integral_const_mul,integral_div]
      rw [integral_add (f := fun p => majorant n g p)
        (g := fun p => majorant n g p.swap) hm hm.swap,integral_prod_swap]
      ring
    _ ≤ T*((8*peak 1*Real.sqrt T+4*T)*(∫ t, (g t)^2 ∂window T)) :=
      mul_le_mul_of_nonneg_left (majorant_integral_bound n g hT hg) hT
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.IBMClockTimeWeightEnergy
