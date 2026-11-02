import Foundation.GaussianDeterministicVolterra
import Foundation.GaussianTimeProcess

/-! Brownian constant-channel calibration for slice divergence assembly.
Raw slice coefficients and time-normalized predictable profiles have different
refinement norms. This is not a black-flow realization or a full slice gradient. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BlackSliceRefinement
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianHilbertProcess
open GaussianDeterministicVolterra
attribute [local instance] timeHilbert_secondCountable

/-- Spatial constant-channel divergence, on the actual Gaussian increment. -/
def sliceDivergence (s t : ℝ≥0) (c : ℝ) : GaussianL2 :=
  (c / ((t : ℝ) - s)) • (wienerL2 t - wienerL2 s)

theorem sliceDivergence_canonical (s t : ℝ≥0) (h : s < t) :
    sliceDivergence s t ((t : ℝ) - s) = wienerL2 t - wienerL2 s := by
  simp [sliceDivergence, div_self (sub_ne_zero.mpr (ne_of_gt (show (s : ℝ) < t from h)))]

/-- Duality against the actual linear Gaussian test cylinder. No full-domain claim. -/
theorem slice_linear_duality (s t : ℝ≥0) (h : s < t) (c b : ℝ) :
    inner ℝ (sliceDivergence s t c) (b • (wienerL2 t - wienerL2 s)) = c * b := by
  rw [sliceDivergence, real_inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, wienerL2_sub_norm_sq s t h.le]
  field_simp [sub_ne_zero.mpr (ne_of_gt (show (s : ℝ) < t from h))]

theorem sliceDivergence_energy (s t : ℝ≥0) (h : s < t) (c : ℝ) :
    ‖sliceDivergence s t c‖ ^ 2 = c^2 / ((t : ℝ) - s) := by
  rw [sliceDivergence, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    wienerL2_sub_norm_sq s t h.le]
  field_simp

/-- The native time profile includes the reciprocal slice length. -/
def sliceProfile (s t : ℝ≥0) (c : ℝ) : TimeHilbert :=
  (c / ((t : ℝ) - s)) • (timeVector t - timeVector s)

theorem sliceProfile_positive (s t : ℝ≥0) (c : ℝ) :
    sliceProfile s t c ∈ positiveProfiles := by
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  all_goals
    apply causal_profile_mem
    filter_upwards [timeVector_coeFn _] with x hx hnon
    rw [hx, Set.indicator_of_notMem hnon]

theorem native_slice_integral (s t : ℝ≥0) (c : ℝ) :
    profileIntegral ⟨sliceProfile s t c, sliceProfile_positive s t c⟩ =
      sliceDivergence s t c := by
  rw [profileIntegral_eq_isonormal]
  simp only [sliceProfile, sliceDivergence, map_smul, map_sub, wienerL2]

def tick (n i : ℕ) : ℝ≥0 := (i : ℝ≥0) / ((n : ℝ≥0) + 1)

theorem tick_zero (n : ℕ) : tick n 0 = 0 := by simp [tick]
theorem tick_last (n : ℕ) : tick n (n+1) = 1 := by simp [tick]

theorem tick_width (n i : ℕ) :
    ((tick n (i+1) : ℝ) - tick n i) = 1 / ((n : ℝ)+1) := by
  simp only [tick, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one,
    Nat.cast_add, Nat.cast_one]
  ring

theorem tick_strict (n i : ℕ) : tick n i < tick n (i+1) := by
  apply NNReal.coe_lt_coe.mp
  have h := tick_width n i
  have hp : 0 < 1 / ((n : ℝ)+1) := by positivity
  linarith

/-- Actual canonical slice divergences telescope to the original Brownian endpoint. -/
theorem canonical_sum (n : ℕ) :
    ∑ i ∈ Finset.range (n+1), sliceDivergence (tick n i) (tick n (i+1))
      ((tick n (i+1) : ℝ) - tick n i) = wienerL2 1 := by
  simp_rw [sliceDivergence_canonical _ _ (tick_strict n _)]
  rw [Finset.sum_range_sub (fun i => wienerL2 (tick n i)) (n+1)]
  simp [tick_zero, tick_last, wienerL2_zero]

def rawEnergy (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), ((tick n (i+1) : ℝ) - tick n i)^2

def normalizedEnergy (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1),
    ((tick n (i+1) : ℝ) - tick n i)^2 / ((tick n (i+1) : ℝ) - tick n i)

theorem rawEnergy_eq (n : ℕ) : rawEnergy n = 1 / ((n : ℝ)+1) := by
  simp only [rawEnergy, tick_width, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

theorem normalizedEnergy_eq (n : ℕ) : normalizedEnergy n = 1 := by
  simp only [normalizedEnergy, tick_width, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem rawEnergy_tendsto_zero : Tendsto rawEnergy atTop (nhds 0) := by
  simp_rw [show rawEnergy = fun n : ℕ => 1 / ((n : ℝ)+1) from funext rawEnergy_eq]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem canonical_sum_energy (n : ℕ) :
    ‖∑ i ∈ Finset.range (n+1), sliceDivergence (tick n i) (tick n (i+1))
      ((tick n (i+1) : ℝ) - tick n i)‖^2 = 1 := by
  rw [canonical_sum]
  rw [wienerL2, (isonormalEmbedding TimeHilbert).norm_map, timeVector_norm_sq]
  norm_num

/-- No partition-independent squared-norm bound in the unweighted slice norm. -/
theorem no_uniform_raw_bound (C : ℝ) : ∃ n : ℕ,
    C * rawEnergy n < ‖wienerL2 1‖^2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have he : ‖wienerL2 1‖^2 = 1 := by
    rw [wienerL2, (isonormalEmbedding TimeHilbert).norm_map, timeVector_norm_sq]
    norm_num
  refine ⟨n, ?_⟩
  rw [rawEnergy_eq, he]
  have hp : 0 < (n : ℝ)+1 := by positivity
  rw [mul_one_div, div_lt_one hp]
  linarith

/-- Reciprocal-time normalization identifies every partition with the SAME
actual native Brownian integrand, not merely equal expectations. -/
theorem canonical_profile_sum (n : ℕ) :
    ∑ i ∈ Finset.range (n+1), sliceProfile (tick n i) (tick n (i+1))
      ((tick n (i+1) : ℝ) - tick n i) = timeVector 1 := by
  have he (i : ℕ) : sliceProfile (tick n i) (tick n (i+1))
      ((tick n (i+1) : ℝ) - tick n i) = timeVector (tick n (i+1)) - timeVector (tick n i) := by
    unfold sliceProfile
    rw [div_self (by rw [tick_width]; positivity), one_smul]
  simp_rw [he]
  rw [Finset.sum_range_sub (fun i => timeVector (tick n i)) (n+1)]
  simp [tick_zero, tick_last, timeVector_zero]

/-- A bounded common divergence cannot preserve raw slice norms while
representing these actual canonical Brownian outputs at all refinements. -/
theorem no_raw_isometric_assembly {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E →L[ℝ] GaussianL2) (u : ℕ → E)
    (hn : ∀ n, ‖u n‖ ^ 2 = rawEnergy n) :
    ¬ ∀ n, J (u n) = wienerL2 1 := by
  intro h
  obtain ⟨n, hbad⟩ := no_uniform_raw_bound (‖J‖^2)
  have hb := J.le_opNorm (u n)
  rw [h n] at hb
  have hs : ‖wienerL2 1‖^2 ≤ ‖J‖^2 * rawEnergy n := by
    rw [← hn n, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  exact (not_lt_of_ge hs) hbad

/-- Even an unbounded closable common operator is impossible if its domain
embeddings preserve the unweighted raw slice norm and the canonical outputs. -/
theorem no_closable_raw_assembly {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E →ₗ.[ℝ] GaussianL2) (u : ℕ → J.domain)
    (hn : ∀ n, ‖(u n : E)‖ ^ 2 = rawEnergy n)
    (hv : ∀ n, J (u n) = wienerL2 1) : ¬ J.IsClosable := by
  intro hc
  have hu : Tendsto (fun n => (u n : E)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp rawEnergy_tendsto_zero
    simpa only [Function.comp_def, ← hn, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht
  obtain ⟨g, hg, hJg⟩ := LinearPMap.isClosable_iff_exists_closed_extension.mp hc
  have hlim : Tendsto (fun n => ((u n : E), wienerL2 1)) atTop
      (nhds (0, wienerL2 1)) := hu.prodMk_nhds tendsto_const_nhds
  have hm : (0, wienerL2 1) ∈ g.graph := hg.mem_of_tendsto hlim (Eventually.of_forall
    (fun n => by
      have hp := LinearPMap.le_graph_of_le hJg (J.mem_graph (u n))
      rwa [hv n] at hp))
  have hz : wienerL2 1 = 0 := by
    simpa using g.mem_graph_snd_inj hm (g.mem_graph 0) rfl
  have he : ‖wienerL2 1‖ ^ 2 = 1 := by
    rw [wienerL2, (isonormalEmbedding TimeHilbert).norm_map, timeVector_norm_sq]
    norm_num
  rw [hz] at he
  norm_num at he

end OperatorDerivativeRewrite.Foundation.BlackSliceRefinement
