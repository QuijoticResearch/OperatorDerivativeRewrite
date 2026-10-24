import Foundation.IBMClockPastMoments

/-! A fourth-moment one-step bound for ACTUAL spatial-Hilbert Brownian sums.
Past coefficients need not be mutually independent or deterministic. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialFourthStep
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess IBMClockPastMoments

private theorem power_domination (a : ℝ≥0) (S : SampleSpace → TimeHilbert)
    (hS : MemLp S 4 gaussianProduct) (j : ℕ) (hj : j ≤ 4) (c : ℝ)
    (f : SampleSpace → ℝ) (hf : StronglyMeasurable[naturalFiltration a] f)
    (hb : ∀ Y, ‖f Y‖ ≤ c*‖S Y‖^j) : Integrable f gaussianProduct := by
  have hjp : MemLp S (j : ℝ≥0∞) gaussianProduct := hS.mono_exponent (by exact_mod_cast hj)
  exact (hjp.integrable_norm_pow'.const_mul c).mono'
    (hf.mono (naturalFiltration.le a)).aestronglyMeasurable (Eventually.of_forall hb)

private theorem pointwise_bound (x u : TimeHilbert) (d κ : ℝ) (hκ : 0 ≤ κ) (hu : ‖u‖ ≤ κ) :
    ‖x+d • u‖^4 ≤ ‖x‖^4+4*(‖x‖^2*inner ℝ x u)*d+
      (6*κ^2)*(‖x‖^2*d^2)+4*(‖u‖^2*inner ℝ x u)*d^3+κ^4*d^4 := by
  have he : ‖x+d • u‖^4 = (‖x‖^2+2*d*inner ℝ x u+d^2*‖u‖^2)^2 := by
    rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, norm_add_sq_real,
      real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hs : ‖u‖^2 ≤ κ^2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
  have hq : ‖u‖^4 ≤ κ^4 := pow_le_pow_left₀ (norm_nonneg u) hu 4
  have hh : (inner ℝ x u)^2 ≤ ‖x‖^2*‖u‖^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg (inner ℝ x u)) (norm_inner_le_norm x u) 2
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using h
  have hi : (inner ℝ x u)^2 ≤ ‖x‖^2*κ^2 :=
    hh.trans (mul_le_mul_of_nonneg_left hs (sq_nonneg _))
  have h1 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*d^2*‖x‖^2)
  have h2 := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 4*d^2)
  have h4 := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ d^4)
  rw [he]
  nlinarith

theorem fourth_step (a b : ℝ≥0) (hab : a ≤ b) (κ : ℝ) (hκ : 0 ≤ κ)
    (S U : SampleSpace → TimeHilbert)
    (hS : StronglyMeasurable[naturalFiltration a] S)
    (hU : StronglyMeasurable[naturalFiltration a] U)
    (hS4 : MemLp S 4 gaussianProduct) (hUb : ∀ Y, ‖U Y‖ ≤ κ) :
    Integrable (fun Y => ‖S Y+delta a b Y • U Y‖^4) gaussianProduct ∧
      (∫ Y, ‖S Y+delta a b Y • U Y‖^4 ∂gaussianProduct) ≤
        (∫ Y, ‖S Y‖^4 ∂gaussianProduct)+
          6*((b : ℝ)-a)*κ^2*(∫ Y, ‖S Y‖^2 ∂gaussianProduct)+3*((b : ℝ)-a)^2*κ^4 := by
  let A : SampleSpace → ℝ := fun Y => ‖S Y‖^2*inner ℝ (S Y) (U Y)
  let B : SampleSpace → ℝ := fun Y => ‖S Y‖^2
  let C : SampleSpace → ℝ := fun Y => ‖U Y‖^2*inner ℝ (S Y) (U Y)
  have hAm : StronglyMeasurable[naturalFiltration a] A := (hS.norm.pow 2).mul (hS.inner hU)
  have hBm : StronglyMeasurable[naturalFiltration a] B := hS.norm.pow 2
  have hCm : StronglyMeasurable[naturalFiltration a] C := (hU.norm.pow 2).mul (hS.inner hU)
  have hAi : Integrable A gaussianProduct := power_domination a S hS4 3 (by decide) κ A hAm (by
    intro Y
    dsimp only [A]
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ‖S Y‖^2*(‖S Y‖*‖U Y‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (sq_nonneg _)
      _ ≤ ‖S Y‖^2*(‖S Y‖*κ) := by gcongr; exact hUb Y
      _ = κ*‖S Y‖^3 := by ring)
  have hBi : Integrable B gaussianProduct :=
    ((hS4.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_norm_pow')
  have hCi : Integrable C gaussianProduct := power_domination a S hS4 1 (by decide) (κ^3) C hCm (by
    intro Y
    dsimp only [C]
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ‖U Y‖^2*(‖S Y‖*‖U Y‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (sq_nonneg _)
      _ ≤ κ^2*(‖S Y‖*κ) := by gcongr <;> exact hUb Y
      _ = κ^3*‖S Y‖^1 := by ring)
  have hA := past_power a b hab 1 A hAm.measurable hAi
  have hB := past_power a b hab 2 B hBm.measurable hBi
  have hC := past_power a b hab 3 C hCm.measurable hCi
  let R : SampleSpace → ℝ := fun Y => ‖S Y‖^4+4*(A Y*delta a b Y^1)+
    (6*κ^2)*(B Y*delta a b Y^2)+4*(C Y*delta a b Y^3)+κ^4*delta a b Y^4
  have hRi : Integrable R gaussianProduct :=
    ((((hS4.integrable_norm_pow').add (hA.1.const_mul 4)).add
      (hB.1.const_mul (6*κ^2))).add (hC.1.const_mul 4)).add
        ((power_integrable a b 4).const_mul (κ^4))
  have hle (Y : SampleSpace) : ‖S Y+delta a b Y • U Y‖^4 ≤ R Y := by
    simpa only [R, A, B, C, pow_one, mul_assoc] using pointwise_bound (S Y) (U Y) (delta a b Y) κ hκ (hUb Y)
  have hfi : Integrable (fun Y => ‖S Y+delta a b Y • U Y‖^4) gaussianProduct := by
    apply hRi.mono' _ (Eventually.of_forall fun Y => by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖S Y+delta a b Y • U Y‖^4)]
      exact hle Y)
    exact (((hS.mono (naturalFiltration.le a)).aestronglyMeasurable.add
      (((process_stronglyMeasurable b).sub (process_stronglyMeasurable a)).aestronglyMeasurable.smul
        (hU.mono (naturalFiltration.le a)).aestronglyMeasurable)).norm.pow 4)
  refine ⟨hfi, (integral_mono hfi hRi hle).trans_eq ?_⟩
  dsimp only [R]
  have h01 := integral_add (hS4.integrable_norm_pow') (hA.1.const_mul 4)
  have h012 := integral_add ((hS4.integrable_norm_pow').add (hA.1.const_mul 4))
    (hB.1.const_mul (6*κ^2))
  have h0123 := integral_add (((hS4.integrable_norm_pow').add (hA.1.const_mul 4)).add
    (hB.1.const_mul (6*κ^2))) (hC.1.const_mul 4)
  have h01234 := integral_add ((((hS4.integrable_norm_pow').add (hA.1.const_mul 4)).add
    (hB.1.const_mul (6*κ^2))).add (hC.1.const_mul 4))
    ((power_integrable a b 4).const_mul (κ^4))
  simp only [Pi.add_apply] at h01 h012 h0123 h01234
  rw [h01234, h0123, h012, h01]
  have hAz : (∫ Y, A Y*delta a b Y ∂gaussianProduct) = 0 := by
    simpa only [pow_one, delta_first, mul_zero] using hA.2
  simp only [integral_const_mul, hAz, hB.2, hC.2, pow_one, delta_second a b hab,
    delta_third, delta_fourth a b hab, mul_zero, add_zero, B]
  ring

theorem fourth_step_memLp (a b : ℝ≥0) (hab : a ≤ b) (κ : ℝ) (hκ : 0 ≤ κ)
    (S U : SampleSpace → TimeHilbert)
    (hS : StronglyMeasurable[naturalFiltration a] S)
    (hU : StronglyMeasurable[naturalFiltration a] U)
    (hS4 : MemLp S 4 gaussianProduct) (hUb : ∀ Y, ‖U Y‖ ≤ κ) :
    MemLp (fun Y => S Y+delta a b Y • U Y) 4 gaussianProduct := by
  have hi := (fourth_step a b hab κ hκ S U hS hU hS4 hUb).1
  have hm : AEStronglyMeasurable (fun Y => S Y+delta a b Y • U Y) gaussianProduct :=
    ((hS.mono (naturalFiltration.le a)).aestronglyMeasurable.add
    (((process_stronglyMeasurable b).sub (process_stronglyMeasurable a)).aestronglyMeasurable.smul
      (hU.mono (naturalFiltration.le a)).aestronglyMeasurable))
  apply (integrable_norm_rpow_iff hm (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
  simpa using hi

theorem second_step (a b : ℝ≥0) (hab : a ≤ b) (κ : ℝ) (hκ : 0 ≤ κ)
    (S U : SampleSpace → TimeHilbert)
    (hS : StronglyMeasurable[naturalFiltration a] S)
    (hU : StronglyMeasurable[naturalFiltration a] U)
    (hS4 : MemLp S 4 gaussianProduct) (hUb : ∀ Y, ‖U Y‖ ≤ κ) :
    (∫ Y, ‖S Y+delta a b Y • U Y‖^2 ∂gaussianProduct) ≤
      (∫ Y, ‖S Y‖^2 ∂gaussianProduct)+((b : ℝ)-a)*κ^2 := by
  let A : SampleSpace → ℝ := fun Y => inner ℝ (S Y) (U Y)
  have hAm : StronglyMeasurable[naturalFiltration a] A := hS.inner hU
  have hAi : Integrable A gaussianProduct := power_domination a S hS4 1 (by decide) κ A hAm (by
    intro Y
    exact (norm_inner_le_norm (S Y) (U Y)).trans (by
      simpa only [pow_one, mul_comm] using mul_le_mul_of_nonneg_left (hUb Y) (norm_nonneg (S Y))))
  have hA := past_power a b hab 1 A hAm.measurable hAi
  have hAz : (∫ Y, A Y*delta a b Y ∂gaussianProduct) = 0 := by
    simpa only [pow_one, delta_first, mul_zero] using hA.2
  have hSi : Integrable (fun Y => ‖S Y‖^2) gaussianProduct :=
    (hS4.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_norm_pow'
  let R : SampleSpace → ℝ := fun Y => ‖S Y‖^2+2*(A Y*delta a b Y^1)+κ^2*delta a b Y^2
  have hRi : Integrable R gaussianProduct := (hSi.add (hA.1.const_mul 2)).add
    ((power_integrable a b 2).const_mul (κ^2))
  have hle (Y : SampleSpace) : ‖S Y+delta a b Y • U Y‖^2 ≤ R Y := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hs := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hUb Y) 2) (sq_nonneg (delta a b Y))
    dsimp only [R, A]
    nlinarith
  have hfi := ((fourth_step_memLp a b hab κ hκ S U hS hU hS4 hUb).mono_exponent
    (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_norm_pow'
  apply (integral_mono hfi hRi hle).trans_eq
  have h01 := integral_add hSi (hA.1.const_mul 2)
  have h012 := integral_add (hSi.add (hA.1.const_mul 2))
    ((power_integrable a b 2).const_mul (κ^2))
  simp only [Pi.add_apply] at h01 h012
  dsimp only [R]
  rw [h012, h01]
  simp only [integral_const_mul, pow_one, hAz, delta_second a b hab, mul_zero, add_zero]
  ring

end OperatorDerivativeRewrite.Foundation.IBMSpatialFourthStep
