import Foundation.HigherHeatLpControls

/-! Actual finite measurable step controls in L^(2m) and exact compatibility with signed increment laws. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatLpStepControls
open HigherHeatLpControls HigherHeatStepIntegralLaws HigherHeatStepIntegralRealization

variable {ι : Type*} [Fintype ι]

def raw (s : ι → Set ℝ) (c : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, (s i).indicator (fun _ => c i) x

theorem raw_memLp (m : ℕ) [Fact (0 < m)] (s : ι → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hf : ∀ i, volume (s i) ≠ ∞) (c : ι → ℝ) :
    MemLp (raw s c) (power m) volume := by
  apply memLp_finsetSum
  intro i _
  exact memLp_indicator_const (power m) (hs i) (c i) (Or.inr (hf i))

def control (m : ℕ) [Fact (0 < m)] (s : ι → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hf : ∀ i, volume (s i) ≠ ∞) (c : ι → ℝ) : Control m :=
  (raw_memLp m s hs hf c).toLp (raw s c)

theorem control_ae (m : ℕ) [Fact (0 < m)] (s : ι → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hf : ∀ i, volume (s i) ≠ ∞) (c : ι → ℝ) :
    ⇑(control m s hs hf c) =ᵐ[volume] raw s c := (raw_memLp m s hs hf c).coeFn_toLp

theorem raw_norm_power (s : ι → Set ℝ) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (c : ι → ℝ) (p : ℕ) (hp : 0 < p) (x : ℝ) :
    ‖raw s c x‖ ^ p = ∑ i, (s i).indicator (fun _ => ‖c i‖ ^ p) x := by
  classical
  by_cases hx : ∃ j, x ∈ s j
  · obtain ⟨j, hj⟩ := hx
    have hout (i : ι) (hi : i ≠ j) : x ∉ s i :=
      fun hxi => Set.disjoint_left.mp (hd hi) hxi hj
    have he (v : ι → ℝ) : (∑ i, (s i).indicator (fun _ => v i) x) = v j := by
      rw [Finset.sum_eq_single j]
      · exact Set.indicator_of_mem hj _
      · intro i _ hi
        simp [hout i hi]
      · simp
    unfold raw
    rw [he c, he (fun i => ‖c i‖ ^ p)]
  · have hout (i : ι) : x ∉ s i := fun hxi => hx ⟨i, hxi⟩
    have he (v : ι → ℝ) : (∑ i, (s i).indicator (fun _ => v i) x) = 0 :=
      Finset.sum_eq_zero (fun i _ => by simp [hout i])
    unfold raw
    rw [he c, he (fun i => ‖c i‖ ^ p), norm_zero, zero_pow hp.ne']

theorem clock_step (m : ℕ) [h : Fact (0 < m)] (s : ι → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hf : ∀ i, volume (s i) ≠ ∞)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (c : ι → ℝ) :
    (clock m (control m s hs hf c) : ℝ) = ∑ i, volume.real (s i) * ‖c i‖ ^ (2*m) := by
  have hm := h.out
  have hi (i : ι) : Integrable ((s i).indicator (fun _ : ℝ => ‖c i‖ ^ (2*m))) volume :=
    (integrable_indicator_iff (hs i)).mpr (integrableOn_const (hf i))
  rw [clock_integral]
  trans ∫ x : ℝ, ∑ i, (s i).indicator (fun _ => ‖c i‖ ^ (2*m)) x
  · apply integral_congr_ae
    filter_upwards [control_ae m s hs hf c] with x hx
    rw [hx]
    exact raw_norm_power s hd c (2*m) (by omega) x
  · rw [integral_finsetSum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (hs i), setIntegral_const]
    rfl

def durations (s : ι → Set ℝ) : ι → ℝ≥0 := fun i => (volume (s i)).toNNReal

theorem clock_effectiveTime (m : ℕ) [Fact (0 < m)] (s : ι → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hf : ∀ i, volume (s i) ≠ ∞)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (c : ι → ℝ) :
    clock m (control m s hs hf c) = effectiveTime m (durations s) c := by
  apply NNReal.eq
  rw [clock_step m s hs hf hd c]
  simp only [effectiveTime, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm]
  rfl

theorem marginal_step (m : ℕ) [h : Fact (0 < m)] (s : ι → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hf : ∀ i, volume (s i) ≠ ∞)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (ht : ∀ i, 0 < durations s i)
    (c : ι → ℝ) : marginal m (control m s hs hf c) = integralLaw m h.out (durations s) ht c := by
  rw [integralLaw_eq_heatLaw]
  unfold marginal
  rw [clock_effectiveTime m s hs hf hd c]

end OperatorDerivativeRewrite.Foundation.HigherHeatLpStepControls
