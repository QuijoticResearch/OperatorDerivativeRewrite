import Mathlib.Analysis.Complex.JensenFormula

/-! Jensen multiplicity bounds for actual entire functions with subquadratic growth.
This generalizes the existing quartic proof without a real-zero assumption.
The estimates control the weighted divisor mass needed for canonical products. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.EntireSubquadraticZeroCounting
variable (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f univ) (h0 : f 0 ≠ 0)

def zeroCount (R : ℝ) : ℤ :=
  ∑ᶠ z, divisor f (closedBall 0 R) z

include ha h0

theorem zero_order_finite (z : ℂ) :
    meromorphicOrderAt f z ≠ ⊤ := by
  have hn : f 0 ≠ 0 := h0
  have h0 : meromorphicOrderAt f 0 ≠ ⊤ := by
    rw [(ha 0 (mem_univ _)).meromorphicOrderAt_eq,
      (ha 0 (mem_univ _)).analyticOrderAt_eq_zero.mpr hn]
    simp
  exact (ha.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
    isConnected_univ).mp ⟨⟨0,mem_univ _⟩,h0⟩ ⟨z,mem_univ _⟩

theorem zeros_in_closedBall_finite (R : ℝ) :
    (closedBall (0 : ℂ) R ∩ f ⁻¹' {0}).Finite := by
  have han := ha.mono (subset_univ (closedBall (0 : ℂ) R))
  rw [han.meromorphicNFOn.zero_set_eq_divisor_support
    (fun z => zero_order_finite f ha h0 z)]
  exact (divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall ..)

omit h0 in
theorem zeroCount_nonneg (R : ℝ) : 0 ≤ zeroCount f R := by
  apply finsum_nonneg
  exact ((ha).mono (subset_univ _)).divisor_nonneg

theorem zeroCount_subquadratic_bound
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖)) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R →
      (zeroCount f R : ℝ) ≤ K * (R * Real.sqrt R) := by
  obtain ⟨C,hC,hgrowth⟩ := hgrowth
  let D : ℝ := max C 1
  have hD : 1 ≤ D := le_max_right _ _
  have hDp : 0 < D := by linarith
  have hn : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  let A : ℝ := |Real.log D| + |Real.log ‖f 0‖| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(A+4)/Real.log 2,by positivity,?_⟩
  intro R hR
  have hRp : 0 < R := by linarith
  let M := D * Real.exp ((2*R)*Real.sqrt (2*R))
  have hM : 1 ≤ M := by
    have he : 1 ≤ Real.exp ((2*R)*Real.sqrt (2*R)) := Real.one_le_exp (by positivity)
    dsimp [M]
    nlinarith
  have hb (z : ℂ) (hz : z ∈ sphere (0 : ℂ) |2*R|) : ‖f z‖ ≤ M := by
    have he : ‖z‖ = 2*R := by simpa [abs_of_pos (by positivity : 0 < 2*R)]
      using mem_sphere_zero_iff_norm.mp hz
    have h := hgrowth z
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.exp_pos _).le)
  have ha := (ha).mono (subset_univ (closedBall (0 : ℂ) |2*R|))
  have hj := ha.sum_divisor_le (r := R) (R := 2*R) (M := M)
    (by simpa [abs_of_pos hRp])
    (by simpa [abs_of_pos hRp,abs_of_pos (by positivity : 0 < 2*R)] using
      (show R < 2*R by linarith)) hM (norm_pos_iff.mp hn) hb
  have hs : Real.sqrt (2*R) ≤ 2*Real.sqrt R := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hRp.le]
  have hs1 : 1 ≤ Real.sqrt R := (Real.le_sqrt (by norm_num) hRp.le).mpr (by nlinarith)
  have hr1 : 1 ≤ R*Real.sqrt R := by nlinarith
  have hlog : Real.log (M / ‖f 0‖) ≤ (A+4)*(R*Real.sqrt R) := by
    dsimp [M]
    rw [Real.log_div (by positivity) (ne_of_gt hn),Real.log_mul (ne_of_gt hDp)
      (Real.exp_ne_zero _),Real.log_exp]
    have hp := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*R)
    dsimp [A] at *
    nlinarith [le_abs_self (Real.log D),neg_le_abs (Real.log ‖f 0‖),
      mul_nonneg (le_of_lt hA) (sub_nonneg.mpr hr1)]
  have he : (2*R)/R = 2 := by field_simp
  rw [abs_of_pos hRp,he] at hj
  change (zeroCount f R : ℝ) ≤ _ at hj
  calc
    _ ≤ Real.log (M / ‖f 0‖) / Real.log 2 := hj
    _ ≤ ((A+4)*(R*Real.sqrt R))/Real.log 2 := div_le_div_of_nonneg_right hlog hl2.le
    _ = _ := by ring

theorem normalized_zeroCount_tendsto_zero
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖)) :
    Tendsto (fun R : ℝ => (zeroCount f R : ℝ) / R^2) atTop (𝓝 0) := by
  obtain ⟨K,hK,hb⟩ := zeroCount_subquadratic_bound f ha h0 hgrowth
  have hlim : Tendsto (fun R : ℝ => K / Real.sqrt R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [] with R
    exact div_nonneg (by exact_mod_cast zeroCount_nonneg f ha R) (sq_nonneg R)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hRp : 0 < R := by linarith
    have hs : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRp
    calc
      _ ≤ (K*(R*Real.sqrt R))/R^2 := div_le_div_of_nonneg_right (hb R hR) (sq_nonneg R)
      _ = K/Real.sqrt R := by
        apply (div_eq_div_iff (ne_of_gt (sq_pos_of_pos hRp)) (ne_of_gt hs)).mpr
        calc
          K*(R*Real.sqrt R)*Real.sqrt R = K*R*(Real.sqrt R)^2 := by ring
          _ = K*R^2 := by rw [Real.sq_sqrt hRp.le]; ring

omit h0 in
theorem weighted_zero_mass_bound (R : ℝ) (hR : 0 < R) :
    0 ≤ (∑ᶠ z : ℂ, (divisor f (closedBall 0 R) z : ℝ) * ‖z‖^2 / R^4) ∧
    (∑ᶠ z : ℂ, (divisor f (closedBall 0 R) z : ℝ) * ‖z‖^2 / R^4) ≤
      (zeroCount f R : ℝ) / R^2 := by
  let d := divisor f (closedBall (0 : ℂ) R)
  have hd : (Function.support d).Finite := d.finiteSupport (isCompact_closedBall ..)
  have hn (z : ℂ) : 0 ≤ (d z : ℝ) := by
    exact_mod_cast ((ha).mono (subset_univ _)).divisor_nonneg z
  have hfinite (b : ℂ → ℝ) : (Function.support (fun z => (d z : ℝ)*b z)).Finite := by
    apply hd.subset
    intro z hz
    by_contra h
    have he : d z = 0 := by simpa only [Function.mem_support,not_not] using h
    simp only [Function.mem_support,he,Int.cast_zero,zero_mul,ne_eq,not_true_eq_false] at hz
  have hcast : ((∑ᶠ z, d z : ℤ) : ℝ) = ∑ᶠ z, (d z : ℝ) :=
    map_finsum (Int.castRingHom ℝ) hd
  constructor
  · exact finsum_nonneg fun z => div_nonneg (mul_nonneg (hn z) (sq_nonneg _))
      (by positivity)
  · change (∑ᶠ z, (d z : ℝ)*‖z‖^2/R^4) ≤ _
    have hpoint (z : ℂ) : (d z : ℝ)*‖z‖^2/R^4 ≤ (d z : ℝ)/R^2 := by
      by_cases hz : z ∈ closedBall (0 : ℂ) R
      · have hnorm : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
        calc
          _ ≤ (d z : ℝ)*R^2/R^4 := by gcongr; exact hn z
          _ = (d z : ℝ)/R^2 := by field_simp
      · have he : d z = 0 := d.apply_eq_zero_of_notMem hz
        simp [he]
    have hf : (Function.support (fun z => (d z : ℝ)*‖z‖^2/R^4)).Finite := by
      simpa only [div_eq_mul_inv,mul_assoc] using hfinite (fun z => ‖z‖^2*(R^4)⁻¹)
    have hg : (Function.support (fun z => (d z : ℝ)/R^2)).Finite := by
      simpa only [div_eq_mul_inv] using hfinite (fun _ => (R^2)⁻¹)
    calc
      _ ≤ ∑ᶠ z, (d z : ℝ)/R^2 := finsum_le_finsum hf hg hpoint
      _ = (zeroCount f R : ℝ)/R^2 := by
        simp only [div_eq_mul_inv]
        rw [← finsum_mul,← hcast]
        rfl

theorem weighted_zero_mass_tendsto_zero
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖)) :
    Tendsto (fun R : ℝ =>
      ∑ᶠ z : ℂ, (divisor f (closedBall 0 R) z : ℝ) * ‖z‖^2 / R^4)
      atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (normalized_zeroCount_tendsto_zero f ha h0 hgrowth)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact (weighted_zero_mass_bound f ha R (by linarith)).1
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact (weighted_zero_mass_bound f ha R (by linarith)).2

end OperatorDerivativeRewrite.Foundation.EntireSubquadraticZeroCounting
