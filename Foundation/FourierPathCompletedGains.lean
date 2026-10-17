import Foundation.FourierPathConditionalPairing

/-! Continuous backward observables and exact finite-partition gain representations. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathCompletedGains
open HigherHeatContinuousCylinders HigherHeatFourierBanach HigherHeatFourierTranslations
open HigherHeatFourierPathSemigroup HigherHeatFourierPathC0 FourierPathStopping
open FourierPathTerminalKernels FourierPathKernelFunctionals

variable (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (H : ℝ≥0)
  (q : TestSpace terminalLevels (frequency a))

def state (t : ℝ≥0) (x : ℝ) : ℂ :=
  realize terminalLevels (frequency a) (evolution terminalLevels (frequency a) m hm (H-t) q)
    (line x)

theorem state_continuous : Continuous (fun p : ℝ≥0 × ℝ => state a m hm H q p.1 p.2) := by
  have hf : Continuous (fun p : ℝ≥0 × ℝ => realize terminalLevels (frequency a)
      (evolution terminalLevels (frequency a) m hm (H-p.1) q)) :=
    (realize terminalLevels (frequency a)).continuous.comp
      ((evolution_strong_continuous terminalLevels (frequency a) m hm q).comp
        (continuous_const.sub continuous_fst))
  exact continuous_eval.comp (hf.prodMk (line_continuous.comp continuous_snd))

theorem state_bound (t : ℝ≥0) (x : ℝ) : ‖state a m hm H q t x‖ ≤ ‖q‖ :=
  (test_bound terminalLevels (frequency a) _ (line x)).trans
    (evolution_bound terminalLevels (frequency a) m hm (H-t) q)

theorem state_terminal (x : ℝ) :
    state a m hm H q H x = realize terminalLevels (frequency a) q (line x) := by
  simp only [state, tsub_self, evolution_zero]

theorem state_initial (hH : 0 < H) :
    state a m hm H q 0 0 = expectation terminalLevels (frequency a) m hm H hH q := by
  have hz : line 0 = zeroPath := by
    apply Subtype.ext
    ext s
    simp [line_apply, zeroPath]
  simp only [state, tsub_zero, hz, expectation_at_zero terminalLevels (frequency a) m hm H hH]

theorem curve_continuous (path : Path) :
    Continuous (fun t : ℝ≥0 => state a m hm H q t (path.val (t : ℝ))) := by
  have hp : Continuous (fun t : ℝ≥0 => path.val (t : ℝ)) :=
    path.val.continuous.comp NNReal.continuous_coe
  have hc : Continuous (fun t : ℝ≥0 => (t, path.val (t : ℝ))) := continuous_id.prodMk hp
  have hh := (state_continuous a m hm H q).comp hc
  exact hh

def process (path : Path) : C(ℝ≥0, ℂ) :=
  ⟨fun t => state a m hm H q t (path.val (t : ℝ)), curve_continuous a m hm H q path⟩

theorem process_jointly_continuous :
    Continuous (fun p : ℝ≥0 × Path => process a m hm H q p.2 p.1) := by
  have hp : Continuous (fun p : ℝ≥0 × Path => p.2.val (p.1 : ℝ)) :=
    coordinate_jointly_continuous.comp
      ((NNReal.continuous_coe.comp continuous_fst).prodMk continuous_snd)
  have hc : Continuous (fun p : ℝ≥0 × Path => (p.1, p.2.val (p.1 : ℝ))) :=
    continuous_fst.prodMk hp
  have hh := (state_continuous a m hm H q).comp hc
  exact hh

theorem process_jointly_measurable :
    Measurable (fun p : ℝ≥0 × Path => process a m hm H q p.2 p.1) :=
  (process_jointly_continuous a m hm H q).measurable

theorem process_map_continuous : Continuous (process a m hm H q) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hh := (process_jointly_continuous a m hm H q).comp continuous_swap
  exact hh

theorem process_map_measurable : Measurable (process a m hm H q) :=
  (process_map_continuous a m hm H q).measurable

def curveLaw (μ : Measure Path) : Measure C(ℝ≥0, ℂ) := μ.map (process a m hm H q)

instance curveLaw_probability (μ : Measure Path) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (curveLaw a m hm H q μ) := by
  unfold curveLaw
  infer_instance

def sampledLaw (k : ℕ) (hk : 0 < k) (K : ℝ≥0) (hK : 0 < K) (n : ℕ) :
    Measure C(ℝ≥0, ℂ) :=
  curveLaw a m hm H q (HigherHeatInterpolatedPaths.probabilityPath k hk K hK n)

instance sampledLaw_probability (k : ℕ) (hk : 0 < k) (K : ℝ≥0) (hK : 0 < K) (n : ℕ) :
    IsProbabilityMeasure (sampledLaw a m hm H q k hk K hK n) := by
  letI := HigherHeatInterpolatedPaths.probabilityPath_isProbability k hk K hK n
  unfold sampledLaw
  infer_instance

theorem process_bound (path : Path) (t : ℝ≥0) : ‖process a m hm H q path t‖ ≤ ‖q‖ :=
  state_bound a m hm H q t _

def gain (s t : ℝ≥0) (x y : ℝ) : ℂ := state a m hm H q t y - state a m hm H q s x

theorem gain_bound (s t : ℝ≥0) (x y : ℝ) : ‖gain a m hm H q s t x y‖ ≤ 2 * ‖q‖ :=
  (norm_sub_le _ _).trans (by linarith [state_bound a m hm H q t y, state_bound a m hm H q s x])

def gainSum (grid : ℕ → ℝ≥0) (n : ℕ) (x : ℕ → ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, gain a m hm H q (grid j) (grid (j+1)) (x j) (x (j+1))

theorem gainSum_telescope (grid : ℕ → ℝ≥0) (n : ℕ) (x : ℕ → ℝ) :
    gainSum a m hm H q grid n x =
      state a m hm H q (grid n) (x n) - state a m hm H q (grid 0) (x 0) :=
  Finset.sum_range_sub (fun j => state a m hm H q (grid j) (x j)) n

theorem terminal_representation (hH : 0 < H) (grid : ℕ → ℝ≥0) (n : ℕ)
    (h0 : grid 0 = 0) (hn : grid n = H) (x : ℕ → ℝ) (hx : x 0 = 0) :
    gainSum a m hm H q grid n x = realize terminalLevels (frequency a) q (line (x n)) -
      expectation terminalLevels (frequency a) m hm H hH q := by
  rw [gainSum_telescope, hn, h0, hx, state_terminal, state_initial a m hm H q hH]

theorem path_representation (hH : 0 < H) (grid : ℕ → ℝ≥0) (n : ℕ)
    (h0 : grid 0 = 0) (hn : grid n = H) (path : Path) :
    gainSum a m hm H q grid n (fun j => path.val (grid j)) =
      realize terminalLevels (frequency a) q (line (path.val H)) -
        expectation terminalLevels (frequency a) m hm H hH q := by
  have hx : path.val (grid 0) = 0 := by rw [h0]; exact path.property
  have hh := terminal_representation a m hm H q hH grid n h0 hn
    (fun j => path.val (grid j)) hx
  simpa only [hn] using hh

theorem partition_independent (hH : 0 < H) (grid other : ℕ → ℝ≥0) (n k : ℕ)
    (h0 : grid 0 = 0) (hn : grid n = H) (h0' : other 0 = 0) (hk : other k = H) (path : Path) :
    gainSum a m hm H q grid n (fun j => path.val (grid j)) =
      gainSum a m hm H q other k (fun j => path.val (other j)) := by
  rw [path_representation a m hm H q hH grid n h0 hn path,
    path_representation a m hm H q hH other k h0' hk path]

end OperatorDerivativeRewrite.Foundation.FourierPathCompletedGains
