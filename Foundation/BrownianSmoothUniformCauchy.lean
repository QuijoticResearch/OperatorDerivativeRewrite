import Foundation.BrownianSmoothCompactMaximal

/-! Uniform-in-time control and the Cauchy-in-probability estimate needed
before constructing a limiting continuous local-time path. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianSmoothUniformCauchy
open InfiniteGaussian SmoothAbsoluteApproximation RealSteklovApprox
open BrownianTanakaApproximation BrownianSmoothMassRealization BrownianSmoothCompactMaximal

theorem normalized_error (n : ℕ) (x : ℝ) :
    ‖radius (width n) x - width n - |x|‖ ≤ width n := by
  rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [radius_le_abs_add (width_pos n) x])]
  linarith [abs_le_radius (width_pos n) x]

theorem mass_difference_bound (n m : ℕ) (ω : SampleSpace) (t : ℝ≥0) :
    ‖BrownianSmoothMassPath.path n ω t - BrownianSmoothMassPath.path m ω t‖ ≤
      width n + width m + ‖compensatedPath n ω t - compensatedPath m ω t‖ := by
  let x := IBMConstructedSources.clockPath ω t
  have he : BrownianSmoothMassPath.path n ω t - BrownianSmoothMassPath.path m ω t =
      (radius (width n) x - width n - |x|) - (radius (width m) x - width m - |x|) -
        (compensatedPath n ω t - compensatedPath m ω t) := by
    simp only [compensatedPath, ContinuousMap.coe_mk, x]
    ring
  rw [he]
  calc
    _ ≤ ‖(radius (width n) x - width n - |x|) - (radius (width m) x - width m - |x|)‖ +
        ‖compensatedPath n ω t - compensatedPath m ω t‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add ((norm_sub_le _ _).trans
      (add_le_add (normalized_error n x) (normalized_error m x))) le_rfl

theorem mass_compact_maximal (n m : ℕ) (T ε : ℝ≥0) :
    (ε : ℝ≥0∞) * gaussianProduct {ω | ∃ t : ℝ≥0, t ≤ T ∧
      (ε : ℝ) + width n + width m <
        ‖BrownianSmoothMassPath.path n ω t - BrownianSmoothMassPath.path m ω t‖} ≤
      ENNReal.ofReal ‖approximateField n T - approximateField m T‖ := by
  calc
    _ ≤ (ε : ℝ≥0∞) * gaussianProduct {ω | ∃ t : ℝ≥0, t ≤ T ∧
        (ε : ℝ) < ‖compensatedPath n ω t - compensatedPath m ω t‖} := by
      have hh : {ω | ∃ t : ℝ≥0, t ≤ T ∧ (ε : ℝ) + width n + width m <
          ‖BrownianSmoothMassPath.path n ω t - BrownianSmoothMassPath.path m ω t‖} ⊆
          {ω | ∃ t : ℝ≥0, t ≤ T ∧
            (ε : ℝ) < ‖compensatedPath n ω t - compensatedPath m ω t‖} := by
        rintro ω ⟨t, ht, he⟩
        exact ⟨t, ht, by linarith [mass_difference_bound n m ω t]⟩
      gcongr
    _ ≤ _ := compact_maximal n m T ε

theorem compensated_uniform_cauchy (T ε δ : ℝ≥0) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      gaussianProduct {ω | ∃ t : ℝ≥0, t ≤ T ∧
        (ε : ℝ) < ‖compensatedPath n ω t - compensatedPath m ω t‖} < (δ : ℝ≥0∞) := by
  have hc := (field_tendsto T).cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc ((ε : ℝ) * δ)
    (mul_pos (show (0 : ℝ) < ε from hε) (show (0 : ℝ) < δ from hδ))
  refine ⟨N, fun n hn m hm => ?_⟩
  have hd : ‖approximateField n T - approximateField m T‖ < (ε : ℝ) * δ := by
    simpa only [dist_eq_norm] using hN n hn m hm
  have hu : ENNReal.ofReal ‖approximateField n T - approximateField m T‖ <
      (ε : ℝ≥0∞) * (δ : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_mul (show (0 : ℝ) ≤ ε from ε.property),
      ENNReal.ofReal_coe_nnreal] using (ENNReal.ofReal_lt_ofReal_iff
        (mul_pos (show (0 : ℝ) < ε from hε) (show (0 : ℝ) < δ from hδ))).mpr hd
  exact (ENNReal.mul_lt_mul_iff_right (by exact_mod_cast ne_of_gt hε) ENNReal.coe_ne_top).mp
    ((compact_maximal n m T ε).trans_lt hu)

theorem mass_uniform_cauchy (T ε δ : ℝ≥0) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      gaussianProduct {ω | ∃ t : ℝ≥0, t ≤ T ∧ (ε : ℝ) <
        ‖BrownianSmoothMassPath.path n ω t - BrownianSmoothMassPath.path m ω t‖} <
          (δ : ℝ≥0∞) := by
  obtain ⟨N₁, hN₁⟩ := compensated_uniform_cauchy T (ε / 2) δ (half_pos hε) hδ
  have hw : ∀ᶠ n : ℕ in atTop, width n < (ε : ℝ) / 4 :=
    (width_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < (ε : ℝ) / 4))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hw
  refine ⟨max N₁ N₂, fun n hn m hm => ?_⟩
  have hnm := hN₁ n ((le_max_left _ _).trans hn) m ((le_max_left _ _).trans hm)
  apply lt_of_le_of_lt _ hnm
  apply measure_mono
  rintro ω ⟨t, ht, he⟩
  refine ⟨t, ht, ?_⟩
  have hn' := hN₂ n ((le_max_right _ _).trans hn)
  have hm' := hN₂ m ((le_max_right _ _).trans hm)
  change (ε : ℝ) / 2 < _
  linarith [mass_difference_bound n m ω t]

end OperatorDerivativeRewrite.Foundation.BrownianSmoothUniformCauchy
