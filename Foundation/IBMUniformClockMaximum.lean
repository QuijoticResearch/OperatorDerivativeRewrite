import Foundation.IBMUniformClockGridEnergy
import Foundation.GaussianAbsoluteMoments

/-! Actual Brownian-clock uniform-grid maximum tails. Only existing Gaussian
laws and finite union/Markov estimates are used; no path Holder assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformClockMaximum
open InfiniteGaussian GaussianAbsoluteMoments GaussianTimeProcess IBMUniformClockGridEnergy

theorem gaussian_absolute_moment (v : ℝ≥0) (p : ℕ) :
    (∫ x : ℝ, |x| ^ p ∂gaussianReal 0 v) =
      (Real.sqrt (v : ℝ)) ^ p * standardMoment p := by
  have hs : HasLaw (fun x : ℝ => Real.sqrt (v : ℝ) * x)
      (gaussianReal 0 v) (gaussianReal 0 1) := by
    refine ⟨by fun_prop, ?_⟩
    simp [gaussianReal_map_const_mul, Real.sq_sqrt v.coe_nonneg]
  have he := hs.integral_comp (f := fun x : ℝ => |x| ^ p) (by fun_prop)
  rw [← he]
  simp only [Function.comp_def, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [integral_const_mul]
  rfl

theorem actual_increment_integrable (s t : ℝ≥0) (p : ℕ) :
    Integrable (fun ω => |IBMConstructedSources.clockPath ω t -
      IBMConstructedSources.clockPath ω s| ^ p) gaussianProduct := by
  have hi : Integrable (fun ω => |process t ω - process s ω| ^ p) gaussianProduct := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((process_memLp t (p : ℝ≥0∞) (by simp)).sub
        (process_memLp s (p : ℝ≥0∞) (by simp))).integrable_norm_pow'
  apply hi.congr
  filter_upwards [IBMConstructedSources.clockPath_coordinate_ae s,
    IBMConstructedSources.clockPath_coordinate_ae t] with ω hs ht
  rw [hs, ht]

/-- The genuine twentieth increment moment, including zero-length increments. -/
theorem actual_increment_twentieth (s t : ℝ≥0) :
    (∫ ω, |IBMConstructedSources.clockPath ω t -
      IBMConstructedSources.clockPath ω s| ^ 20 ∂gaussianProduct) =
        |(t : ℝ) - s| ^ 10 * standardMoment 20 := by
  have he : (fun ω => |IBMConstructedSources.clockPath ω t -
      IBMConstructedSources.clockPath ω s| ^ 20) =ᵐ[gaussianProduct]
      (fun ω => |process t ω - process s ω| ^ 20) := by
    filter_upwards [IBMConstructedSources.clockPath_coordinate_ae s,
      IBMConstructedSources.clockPath_coordinate_ae t] with ω hs ht
    rw [hs, ht]
  rw [integral_congr_ae he]
  have hl := (process_increment_hasLaw s t).integral_comp (f := fun x : ℝ => |x| ^ 20)
    (by fun_prop)
  simp only [Function.comp_def, Pi.sub_apply] at hl
  rw [hl, gaussian_absolute_moment]
  have hp : (Real.sqrt ((nndist (t : ℝ) (s : ℝ) : ℝ≥0) : ℝ)) ^ 20 =
      |(t : ℝ) - s| ^ 10 := by
    calc
      _ = ((Real.sqrt ((nndist (t : ℝ) (s : ℝ) : ℝ≥0) : ℝ)) ^ 2) ^ 10 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity), coe_nndist, Real.dist_eq]
  rw [hp]

theorem actual_increment_tail (s t : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    gaussianProduct.real {ω | δ ≤ |IBMConstructedSources.clockPath ω t -
      IBMConstructedSources.clockPath ω s|} ≤
      |(t : ℝ) - s| ^ 10 * standardMoment 20 / δ ^ 20 := by
  calc
    _ ≤ gaussianProduct.real {ω | δ ^ 20 ≤ |IBMConstructedSources.clockPath ω t -
        IBMConstructedSources.clockPath ω s| ^ 20} := by
      apply measureReal_mono (h₂ := by finiteness)
      intro ω hω
      change δ ≤ |IBMConstructedSources.clockPath ω t -
        IBMConstructedSources.clockPath ω s| at hω
      change δ ^ 20 ≤ |IBMConstructedSources.clockPath ω t -
        IBMConstructedSources.clockPath ω s| ^ 20
      gcongr
    _ ≤ _ := by
      apply (le_div_iff₀ (pow_pos hδ 20)).mpr
      rw [mul_comm]
      exact (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ => by positivity)
        (actual_increment_integrable s t 20) (δ ^ 20)).trans_eq (actual_increment_twentieth s t)

def bad (T : ℝ≥0) (n : ℕ) (δ : ℝ) : Set SampleSpace :=
  ⋃ k : Fin n, {ω | δ ≤ |IBMConstructedSources.clockPath ω (grid (T / n) (k.val + 1)) -
    IBMConstructedSources.clockPath ω (grid (T / n) k.val)|}

theorem bad_measurable (T : ℝ≥0) (n : ℕ) (δ : ℝ) : MeasurableSet (bad T n δ) := by
  apply MeasurableSet.iUnion
  intro k
  have ht := (ContinuousMap.measurable_eval (grid (T / n) (k.val + 1))).comp
    IBMConstructedSources.clockPath_measurable
  have hs := (ContinuousMap.measurable_eval (grid (T / n) k.val)).comp
    IBMConstructedSources.clockPath_measurable
  exact measurableSet_le measurable_const (continuous_abs.measurable.comp (ht.sub hs))

theorem bad_probability_le (T : ℝ≥0) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    gaussianProduct.real (bad T n δ) ≤
      (n : ℝ) * ((T : ℝ) / n) ^ 10 * standardMoment 20 / δ ^ 20 := by
  have he (k : Fin n) :
      |((grid (T / n) (k.val + 1) : ℝ≥0) : ℝ) - grid (T / n) k.val| =
        (T : ℝ) / n := by
    have hd : ((grid (T / n) (k.val + 1) : ℝ≥0) : ℝ) - grid (T / n) k.val =
        (T : ℝ) / n := by
      simp only [grid, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
        Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
      ring
    rw [hd, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ∑ k : Fin n, gaussianProduct.real {ω | δ ≤
        |IBMConstructedSources.clockPath ω (grid (T / n) (k.val + 1)) -
          IBMConstructedSources.clockPath ω (grid (T / n) k.val)|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin n, ((T : ℝ) / n) ^ 10 * standardMoment 20 / δ ^ 20 := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [he k] using actual_increment_tail
        (grid (T / n) k.val) (grid (T / n) (k.val + 1)) hδ
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Outside the measurable bad-clock event, all reflected traversal increments
satisfy the deterministic threshold needed by occupation domination. -/
theorem reflected_mesh_of_not_bad (T : ℝ≥0) (n : ℕ) (δ : ℝ) {ω : SampleSpace}
    (hω : ω ∉ bad T n δ) (k : Fin n) :
    abs (|IBMConstructedSources.clockPath ω (grid (T / n) (k.val + 1))| -
      |IBMConstructedSources.clockPath ω (grid (T / n) k.val)|) ≤ δ := by
  have hk : ¬ δ ≤ |IBMConstructedSources.clockPath ω (grid (T / n) (k.val + 1)) -
      IBMConstructedSources.clockPath ω (grid (T / n) k.val)| := by
    intro h
    exact hω (mem_iUnion.mpr ⟨k, h⟩)
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans (lt_of_not_ge hk).le

theorem maximum_rate_identity (x T C : ℝ) (hx : 0 < x) :
    x * (T / x) ^ 10 * C / (x ^ (-(4/9 : ℝ))) ^ 20 =
      T ^ 10 * C * x ^ (-(1/9 : ℝ)) := by
  have hp : (x ^ (-(4/9 : ℝ))) ^ 20 = x ^ (-(80/9 : ℝ)) := by
    rw [← Real.rpow_natCast _ 20, ← Real.rpow_mul hx.le]
    norm_num
  have hd : x ^ 10 * x ^ (-(80/9 : ℝ)) = x ^ (10/9 : ℝ) := by
    rw [← Real.rpow_natCast x 10, ← Real.rpow_add hx]
    norm_num
  have hr : x / x ^ (10/9 : ℝ) = x ^ (-(1/9 : ℝ)) := by
    calc
      _ = x ^ (1 : ℝ) / x ^ (10/9 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) - 10/9) := (Real.rpow_sub hx _ _).symm
      _ = _ := by norm_num
  rw [hp]
  calc
    _ = T ^ 10 * C * (x / (x ^ 10 * x ^ (-(80/9 : ℝ)))) := by
      rw [div_pow]
      field_simp
    _ = _ := by rw [hd, hr]

/-- The exceptional-event probability vanishes for every uniform-grid size,
with rate standardMoment(20) T^10 N^(-1/9). -/
theorem bad_probability_tendsto (T : ℝ≥0) :
    Filter.Tendsto (fun n : ℕ =>
      gaussianProduct.real (bad T (n + 1) ((n + 1 : ℝ) ^ (-(4/9 : ℝ)))))
      Filter.atTop (nhds 0) := by
  have hb (n : ℕ) : gaussianProduct.real (bad T (n + 1)
      ((n + 1 : ℝ) ^ (-(4/9 : ℝ)))) ≤
        (T : ℝ) ^ 10 * standardMoment 20 * (n + 1 : ℝ) ^ (-(1/9 : ℝ)) := by
    have h := bad_probability_le T (n + 1)
      (Real.rpow_pos_of_pos (by positivity : 0 < (n + 1 : ℝ)) (-(4/9 : ℝ)))
    push_cast at h
    simpa only [maximum_rate_identity _ _ _ (by positivity : 0 < (n + 1 : ℝ))] using h
  have hn : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hl := (tendsto_rpow_neg_atTop (by norm_num : 0 < (1/9 : ℝ))).comp hn
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  simpa only [Function.comp_def, mul_zero] using hl.const_mul ((T : ℝ) ^ 10 * standardMoment 20)

end OperatorDerivativeRewrite.Foundation.IBMUniformClockMaximum
