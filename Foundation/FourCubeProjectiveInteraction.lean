import Foundation.FourCubeFullMixedInteraction

/-! Positive eight-corner partition ratios and pairwise calibration invariance.
Endpoint interpretation is conditional on an independently justified source split. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeProjectiveInteraction
open FourCubeThermalMixedDifference (cornerSum)
open FourCubeFullMixedInteraction

def numerator (K : ℝ → ℝ → ℝ → ℝ) (h : ℝ) : ℝ :=
  K h h h*K h (-h) (-h)*K (-h) h (-h)*K (-h) (-h) h
def denominator (K : ℝ → ℝ → ℝ → ℝ) (h : ℝ) : ℝ :=
  K h (-h) h*K h h (-h)*K (-h) (-h) (-h)*K (-h) h h
def ratio (K : ℝ → ℝ → ℝ → ℝ) (h : ℝ) : ℝ := numerator K h/denominator K h

theorem ratio_positive (K : ℝ → ℝ → ℝ → ℝ) (hK : ∀ x y z,0 < K x y z) (h : ℝ) :
    0 < ratio K h :=
  div_pos (mul_pos (mul_pos (mul_pos (hK _ _ _) (hK _ _ _)) (hK _ _ _)) (hK _ _ _))
    (mul_pos (mul_pos (mul_pos (hK _ _ _) (hK _ _ _)) (hK _ _ _)) (hK _ _ _))

theorem log_ratio (K : ℝ → ℝ → ℝ → ℝ) (hK : ∀ x y z,0 < K x y z) (h : ℝ) :
    Real.log (ratio K h)=cornerSum (fun x y z => Real.log (K x y z)) h := by
  have h1 := hK h h h
  have h2 := hK h (-h) (-h)
  have h3 := hK (-h) h (-h)
  have h4 := hK (-h) (-h) h
  have h5 := hK h (-h) h
  have h6 := hK h h (-h)
  have h7 := hK (-h) (-h) (-h)
  have h8 := hK (-h) h h
  unfold ratio numerator denominator
  rw [Real.log_div (by positivity) (by positivity)]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  unfold cornerSum
  ring

/-- Positive factors missing one source cancel exactly from the multiplicative ratio. -/
theorem ratio_pairwise_invariant (K : ℝ → ℝ → ℝ → ℝ)
    (hK : ∀ x y z,0 < K x y z) (A B C : ℝ → ℝ → ℝ) (h : ℝ) :
    ratio (fun x y z => Real.exp (A x y+B y z+C z x)*K x y z) h=ratio K h := by
  let L := fun x y z => Real.exp (A x y+B y z+C z x)*K x y z
  have hL : ∀ x y z,0 < L x y z := fun x y z => mul_pos (Real.exp_pos _) (hK x y z)
  have hl (x y z : ℝ) : Real.log (L x y z)=Real.log (K x y z)+A x y+B y z+C z x := by
    dsimp [L]
    rw [Real.log_mul (Real.exp_ne_zero _) (hK x y z).ne',Real.log_exp]
    ring
  have he : Real.log (ratio L h)=Real.log (ratio K h) := by
    rw [log_ratio L hL,log_ratio K hK]
    simp_rw [hl]
    exact corner_pairwise_invariant _ A B C h
  have hexp := congrArg Real.exp he
  rw [Real.exp_log (ratio_positive L hL h),Real.exp_log (ratio_positive K hK h)] at hexp
  exact hexp

def kernel (beta x y z : ℝ) : ℝ :=
  FourCubeCompletedHaar.standardPartition beta (FourCubeCompletedHaar.angles x y z)

theorem kernel_positive (beta x y z : ℝ) : 0 < kernel beta x y z :=
  FourCubeCompletedHaar.standard_positive _ _

theorem actual_log_ratio (beta h : ℝ) :
    Real.log (ratio (kernel beta) h)= -cornerSum (freeEnergy beta) h := by
  rw [log_ratio _ (kernel_positive beta)]
  unfold kernel freeEnergy FourCubeCompletedHaar.standardFreeEnergy cornerSum
  ring

/-- Nonzero actual full32 thermal interaction survives all separated scalar factors. -/
theorem actual_log_ratio_limit :
    Tendsto (fun t : ℝ => Real.log (ratio (kernel (1/t^2)) t)/(8*t)) (𝓝[≠] 0) (𝓝 (-c)) := by
  apply actual_thermal_mixed_limit.neg.congr'
  filter_upwards with t
  rw [actual_log_ratio]
  unfold thermalResponse
  ring

theorem actual_calibrated_log_ratio_limit (A B C : ℝ → ℝ → ℝ → ℝ) :
    Tendsto (fun t : ℝ => Real.log (ratio (fun x y z =>
      Real.exp (A t x y+B t y z+C t z x)*kernel (1/t^2) x y z) t)/(8*t))
      (𝓝[≠] 0) (𝓝 (-c)) := by
  apply actual_log_ratio_limit.congr'
  filter_upwards with t
  rw [ratio_pairwise_invariant _ (kernel_positive (1/t^2))]

theorem actual_ratio_eventually_lt_one :
    ∀ᶠ t : ℝ in 𝓝[>] 0,ratio (kernel (1/t^2)) t < 1 := by
  have hf : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun t ht => ne_of_gt ht)
  have h := (actual_log_ratio_limit.mono_left hf).eventually
    (eventually_lt_nhds (neg_lt_zero.mpr c_positive))
  filter_upwards [h,self_mem_nhdsWithin] with t hq ht
  have hlog := (div_lt_iff₀ (mul_pos (show (0 : ℝ)<8 by norm_num) ht)).mp hq
  simp only [zero_mul] at hlog
  apply (Real.log_lt_log_iff (ratio_positive _ (kernel_positive _) _) zero_lt_one).mp
  simpa only [Real.log_one] using hlog

/-- The three actual external source edges, without an assumed transfer grouping. -/
def sourceEdge (j : Fin 3) : FourCubeDirichletBox.BoxEdge :=
  ![FourCubeDirichletBox.highSource,FourCubeDirichletBox.chordSource,
    FourCubeDirichletBox.lowSource] j

/-- If all three raw source edges are spatial for an axis, they share one time slice.
This excludes their direct interpretation as spatial sources at two axis-aligned endpoints. -/
theorem all_spatial_sources_same_time (tau : Fin 4)
    (h : ∀ j : Fin 3,(sourceEdge j).2 ≠ tau) :
    ∀ j : Fin 3,(sourceEdge j).1 tau=(sourceEdge 0).1 tau := by
  fin_cases tau
  · exact False.elim (h 1 rfl)
  · intro j
    fin_cases j <;> rfl
  · exact False.elim (h 0 rfl)
  · intro j
    fin_cases j <;> rfl

end OperatorDerivativeRewrite.Foundation.FourCubeProjectiveInteraction
