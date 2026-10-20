import Foundation.RiemannSixthTransitionCosinePhase
import Foundation.RiemannEvenWindowZeros
import Foundation.RiemannSixthTransitionReflection
import Foundation.RiemannSixthFarZeroControl
/-! Exact local reality and simplicity for the actual sixth-order flow.
The vertical buffer is explicit; global transition coverage remains separate. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionSimpleZeros

theorem eventually_local_real_simple_zeros (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ t : ℝ in atTop, ∀ u : ℝ, 1000000*(M+8) ≤ u →
      RiemannEvenRealSaddle.phaseSlope 3 t u=0 → ∀ x : ℝ,
      |x| ≤ M*RiemannQuarticTransitionSaddle.realScale u →
      ∀ z : ℂ, ‖z-(x : ℂ)‖ < 1/(2048*(M+8)) →
        RiemannEvenFlow.flow 3 t z=0 →
          z.im=0 ∧ deriv (RiemannEvenFlow.flow 3 t) z ≠ 0 := by
  filter_upwards [RiemannSixthTransitionCosinePhase.eventually_actual_cosine_disks
    M (1/1000000) hM (by norm_num)] with t ht
  intro u hu hs x hx z hz hzero
  have hu0 : 0 < u := by linarith
  have huM : 65536*(M+7) ≤ u := by linarith
  obtain ⟨E,Φ,hglobal,hlocal⟩ := ht u huM hs x hx
  let r : ℝ := 1/(1024*(M+8))
  have hr : 0 < r := by dsimp [r]; positivity
  have hscaled : (M+8)/u ≤ 1/1000000 :=
    (div_le_iff₀ hu0).mpr (by linarith)
  have hbuffer : 1/u ≤ r/2 := by
    dsimp [r]
    rw [div_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hhalf : r/2=1/(2048*(M+8)) := by dsimp [r]; field_simp; ring
  apply RiemannQuarticTransitionSimpleZeros.local_real_simple_zero_of_differentiable
    (RiemannEvenFlow.flow 3 t) (RiemannEvenFlow.flow_differentiable 3 t)
    (RiemannEvenWindowZeros.flow_conj 3 t) x r u (M+8) E Φ hu0 hr (by linarith)
    hscaled hbuffer hglobal hlocal z
  · simpa only [hhalf] using hz
  · exact hzero

theorem eventually_actual_rectangular_real_simple_zeros (M R : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ R) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, R < u ∧ 1000000*(M+8) ≤ u ∧
      RiemannEvenRealSaddle.phaseSlope 3 t u=0 ∧
      ∀ z : ℂ, |z.re| ≤ M*RiemannQuarticTransitionSaddle.realScale u →
        |z.im| ≤ 1/(4096*(M+8)) → RiemannEvenFlow.flow 3 t z=0 →
          z.im=0 ∧ deriv (RiemannEvenFlow.flow 3 t) z ≠ 0 := by
  let L := max R (1000000*(M+8))
  have hL : 0 ≤ L := le_trans hR (le_max_left _ _)
  filter_upwards [eventually_local_real_simple_zeros M hM,
    RiemannEvenRealSaddle.eventually_exists_nondegenerate_saddle 3 (by norm_num) L hL]
    with t hlocal hfamily
  obtain ⟨u,hu,_,hs,_⟩ := hfamily
  have hRu : R < u := lt_of_le_of_lt (le_max_left _ _) hu
  have huM : 1000000*(M+8) ≤ u := (le_max_right _ _).trans hu.le
  refine ⟨u,hRu,huM,hs,?_⟩
  intro z hzre hzim hzero
  have hid : z-(z.re : ℂ)=(z.im : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  have hnorm : ‖z-(z.re : ℂ)‖=|z.im| := by
    rw [hid,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  have hhalf : 1/(4096*(M+8)) < 1/(2048*(M+8)) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  apply hlocal u huM hs z.re hzre z _ hzero
  rw [hnorm]
  exact hzim.trans_lt hhalf

theorem bounded_ratio_real_simple_zeros (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, R < u ∧ 1000000*(M+8) ≤ u ∧
      RiemannEvenRealSaddle.phaseSlope 3 t u=0 ∧
      ∀ z : ℂ, ‖z‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u →
        RiemannEvenFlow.flow 3 t z=0 →
          z.im=0 ∧ deriv (RiemannEvenFlow.flow 3 t) z ≠ 0 := by
  let A := 2*RiemannQuarticTransitionReflection.reflectionCutoff (1024*(M+8))
  let r : ℝ := 1/(2048*(M+8))
  have hA : 0 < A := by
    have h := RiemannQuarticTransitionReflection.reflectionCutoff_pos (1024*(M+8)) (by positivity)
    dsimp [A]
    linarith
  have hr : 0 < r := by dsimp [r]; positivity
  let L := max R (max (1000000*(M+8)) (2*A/r))
  have hL : 0 ≤ L := hR.trans (le_max_left _ _)
  filter_upwards [eventually_local_real_simple_zeros M hM,
    RiemannSixthTransitionReflection.eventually_actual_nonzero_lower M hM,
    RiemannEvenRealSaddle.eventually_exists_nondegenerate_saddle 3 (by norm_num) L hL]
    with t hlocal hlower hfamily
  obtain ⟨u,hu,_,hs,_⟩ := hfamily
  have hRu : R < u := lt_of_le_of_lt (le_max_left _ _) hu
  have huD : 1000000*(M+8) ≤ u := (le_max_left _ _).trans ((le_max_right _ _).trans hu.le)
  have huA : 2*A/r ≤ u := (le_max_right _ _).trans ((le_max_right _ _).trans hu.le)
  have hu0 : 0 < u := by linarith
  have huM : 65536*(M+7) ≤ u := by linarith
  refine ⟨u,hRu,huD,hs,?_⟩
  intro z hz hzero
  have hlo : -A/u < z.im := lt_of_not_ge (fun h => hlower u huM hs z hz h hzero)
  have hconjzero : RiemannEvenFlow.flow 3 t (conj z)=0 := by
    rw [RiemannEvenWindowZeros.flow_conj,hzero]
    simp
  have hhi : -A/u < (conj z).im := lt_of_not_ge (fun h =>
    hlower u huM hs (conj z) (by simpa using hz) h hconjzero)
  simp only [Complex.conj_im] at hhi
  rw [neg_div] at hlo hhi
  have hstrip : |z.im| < A/u := abs_lt.mpr ⟨hlo,by linarith⟩
  have hAr : A/u ≤ r/2 := by
    have hh := (div_le_iff₀ hr).mp huA
    apply (div_le_iff₀ hu0).mpr
    nlinarith
  have hid : z-(z.re : ℂ)=(z.im : ℂ)*Complex.I := by
    apply Complex.ext <;> simp
  have hinside : ‖z-(z.re : ℂ)‖ < r := by
    rw [hid,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    exact hstrip.trans (lt_of_le_of_lt hAr (by linarith))
  exact hlocal u huD hs z.re ((Complex.abs_re_le_norm z).trans hz) z hinside hzero

theorem eventually_all_zeros_real_simple :
    ∀ᶠ t : ℝ in atTop, ∀ z : ℂ, RiemannEvenFlow.flow 3 t z=0 →
      z.im=0 ∧ deriv (RiemannEvenFlow.flow 3 t) z ≠ 0 := by
  obtain ⟨K,hK,hfar⟩ := RiemannSixthFarZeroControl.uniform_actual_far_zeros_real_simple
  filter_upwards [bounded_ratio_real_simple_zeros K 120021 hK.le (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with t hbounded ht
  obtain ⟨u,hu,_,hs,hzeros⟩ := hbounded
  intro z hzero
  rcases le_total ‖z‖ (K*RiemannQuarticTransitionSaddle.realScale u) with hnear | hremote
  · exact hzeros z hnear hzero
  · exact hfar t u ht hu.le hs z hremote hzero

end OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionSimpleZeros
