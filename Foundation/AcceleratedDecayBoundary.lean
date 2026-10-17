import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Uniform decay after time acceleration, and a discontinuous initial-time limit. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.AcceleratedDecayBoundary
variable {X E : Type*} [NormedAddCommGroup E]

def rate (n : ℕ) : ℝ := (n : ℝ)+1

theorem rate_positive (n : ℕ) : 0 < rate n := by unfold rate; positivity

theorem rate_tendsto : Tendsto rate atTop atTop :=
  (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add
    (tendsto_const_nhds (x := (1 : ℝ)))

theorem envelope_limit (C decay δ : ℝ) (hdecay : 0 < decay) (hδ : 0 < δ) :
    Tendsto (fun n => C*Real.exp (-decay*(rate n*δ))) atTop (𝓝 0) := by
  have hr : Tendsto (fun n => decay*(rate n*δ)) atTop atTop := by
    convert rate_tendsto.const_mul_atTop (mul_pos hdecay hδ) using 1 <;>
      first | rfl | (funext n; ring)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hr
  simpa only [Function.comp_def, neg_mul, mul_zero] using tendsto_const_nhds.mul he

def accelerated (f : ℝ → X → E) (n : ℕ) (t : ℝ) (x : X) : E := f (rate n*t) x

theorem positive_time_limit (f : ℝ → X → E) (C decay : ℝ) (hdecay : 0 < decay)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖f t x‖ ≤ C*Real.exp (-decay*t))
    (t : ℝ) (ht : 0 < t) (x : X) :
    Tendsto (fun n => accelerated f n t x) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => hb (rate n*t)
    (mul_nonneg (rate_positive n).le ht.le) x)
  exact envelope_limit C decay t hdecay ht

theorem uniform_away_from_zero (f : ℝ → X → E) (C decay : ℝ) (hC : 0 ≤ C) (hdecay : 0 < decay)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖f t x‖ ≤ C*Real.exp (-decay*t)) (δ : ℝ) (hδ : 0 < δ) :
    TendstoUniformlyOn (fun n (p : ℝ × X) => accelerated f n p.1 p.2)
      (fun _ => 0) atTop {p | δ ≤ p.1} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := (envelope_limit C decay δ hdecay hδ).eventually (gt_mem_nhds hε)
  filter_upwards [he] with n hn p hp
  rw [dist_zero_left]
  calc
    _ ≤ C*Real.exp (-decay*(rate n*p.1)) :=
      hb _ (mul_nonneg (rate_positive n).le (hδ.le.trans hp)) _
    _ ≤ C*Real.exp (-decay*(rate n*δ)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hp (rate_positive n).le
      nlinarith
    _ < ε := hn

def boundaryLimit (f : ℝ → X → E) (t : ℝ) (x : X) : E := if t = 0 then f 0 x else 0

theorem nonnegative_time_limit (f : ℝ → X → E) (C decay : ℝ) (hdecay : 0 < decay)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖f t x‖ ≤ C*Real.exp (-decay*t)) (t : ℝ) (ht : 0 ≤ t) (x : X) :
    Tendsto (fun n => accelerated f n t x) atTop (𝓝 (boundaryLimit f t x)) := by
  by_cases hz : t = 0
  · subst t
    simpa [accelerated, boundaryLimit] using
      (tendsto_const_nhds (x := f 0 x) : Tendsto (fun _ : ℕ => f 0 x) atTop (𝓝 (f 0 x)))
  · simpa [boundaryLimit, hz] using
      positive_time_limit f C decay hdecay hb t (lt_of_le_of_ne ht (Ne.symm hz)) x

theorem boundary_not_right_continuous (f : ℝ → X → E) (x : X) (hx : f 0 x ≠ 0) :
    ¬ ContinuousWithinAt (fun t => boundaryLimit f t x) (Ici 0) 0 := by
  intro hc
  have ht := hc.tendsto.mono_left (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self)
  have he : (fun t => boundaryLimit f t x) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : E) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hp : (0 : ℝ) < t := ht
    simp [boundaryLimit, ne_of_gt hp]
  have hz := ht.congr' he
  have hh := tendsto_nhds_unique hz
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : E)) (𝓝[>] 0) (𝓝 0))
  exact hx (by simpa [boundaryLimit] using hh)

end OperatorDerivativeRewrite.Foundation.AcceleratedDecayBoundary
