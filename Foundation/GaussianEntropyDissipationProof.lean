/-
Copyright (c) 2026 OperatorDerivativeRewrite contributors.
-/
import Foundation.GaussianMehlerTimeDerivative
import Foundation.GaussianFisherDecay
import Foundation.GaussianEntropyDissipation
import Foundation.GaussianRotationStein
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Positive bounded C¹ regularity of the actual Mehler evolution and its entropy factor. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter Set Real ProbabilityTheory Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianEntropyDissipationProof

abbrev γ : Measure ℝ := GaussianCore.γ

def logFactor (t : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + Real.log (GaussianMehler.mehler t g x)

/-- The actual Mehler evolution is C¹ in space for bounded C¹ input. -/
theorem mehler_contDiff_one (t : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {M B : ℝ} (hgb : ∀ z, ‖g z‖ ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
    ContDiff ℝ 1 (GaussianMehler.mehler t g) := by
  have hbound : ∀ z, ‖g z‖ ≤ max M B := fun z => (hgb z).trans (le_max_left M B)
  have hdbound : ∀ z, ‖deriv g z‖ ≤ max M B :=
    fun z => (hdgb z).trans (le_max_right M B)
  rw [contDiff_one_iff_deriv]
  constructor
  · intro x
    exact (GaussianFisher.hasDerivAt_mehler_C1 t hg hbound hdbound x).differentiableAt
  · have heq : deriv (GaussianMehler.mehler t g) =
        fun x => Real.exp (-t) * GaussianMehler.mehler t (deriv g) x := by
      funext x
      exact GaussianFisher.deriv_mehler_C1 t hg hbound hdbound x
    rw [heq]
    exact continuous_const.mul
      (GaussianMehler.mehler_continuous (hg.continuous_deriv le_rfl) hdgb t)

/-- Positivity and an upper bound persist under Mehler averaging. -/
theorem mehler_bounds (t : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    {ε M : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
    (hhi : ∀ z, g z ≤ M) (x : ℝ) :
    ε ≤ GaussianMehler.mehler t g x ∧ GaussianMehler.mehler t g x ≤ M := by
  have hM : 0 ≤ M := (hε.le.trans (hlo 0)).trans (hhi 0)
  have hgb : ∀ z, ‖g z‖ ≤ M := by
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hlo z))]
    exact hhi z
  constructor
  · exact GaussianFisher.mehler_lower_bound hg hε hgb hlo t x
  · have hconst : ∀ z : ℝ, ‖(fun _ : ℝ => M) z‖ ≤ M := by
      intro z
      simp [Real.norm_eq_abs, abs_of_nonneg hM]
    have h := GaussianMehler.mehler_mono hg continuous_const hgb hconst hhi t x
    simpa [GaussianMehler.mehler_const] using h

/-- The actual spatial derivative is uniformly bounded for nonnegative times. -/
theorem mehler_deriv_bound (t : ℝ) (ht : 0 ≤ t) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) {M B : ℝ}
    (hgb : ∀ z, ‖g z‖ ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) (x : ℝ) :
    ‖deriv (GaussianMehler.mehler t g) x‖ ≤ B := by
  have hbound : ∀ z, ‖g z‖ ≤ max M B := fun z => (hgb z).trans (le_max_left M B)
  have hdbound : ∀ z, ‖deriv g z‖ ≤ max M B :=
    fun z => (hdgb z).trans (le_max_right M B)
  rw [GaussianFisher.deriv_mehler_C1 t hg hbound hdbound x]
  have hB : 0 ≤ B := (norm_nonneg _).trans (hdgb 0)
  have ha := (GaussianMehlerTimeDerivative.a_bounds t ht).2
  have ha0 := (GaussianMehlerTimeDerivative.a_bounds t ht).1
  have hmean := GaussianMehler.mehler_norm_le hdgb t x
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Real.exp (-t) by exact ha0)]
  exact (mul_le_mul_of_nonneg_left hmean ha0).trans (by nlinarith)

/-- The logarithmic entropy factor is C¹; its derivative is an actual quotient. -/
theorem logFactor_contDiff_one (t : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {ε M B : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
    (hhi : ∀ z, g z ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
    ContDiff ℝ 1 (logFactor t g) := by
  have hgb : ∀ z, ‖g z‖ ≤ M := by
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hlo z))]
    exact hhi z
  have hU := mehler_contDiff_one t hg hgb hdgb
  have hne : ∀ x, GaussianMehler.mehler t g x ≠ 0 :=
    fun x => ne_of_gt (hε.trans_le (mehler_bounds t hg.continuous hε hlo hhi x).1)
  unfold logFactor
  exact contDiff_const.add (hU.log hne)

/-- The log factor differentiates to the logarithmic derivative of the actual evolution. -/
theorem deriv_logFactor (t : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {ε M B : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
    (hhi : ∀ z, g z ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) (x : ℝ) :
    deriv (logFactor t g) x =
      deriv (GaussianMehler.mehler t g) x / GaussianMehler.mehler t g x := by
  have hgb : ∀ z, ‖g z‖ ≤ M := by
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hlo z))]
    exact hhi z
  have hU := mehler_contDiff_one t hg hgb hdgb
  have hne : GaussianMehler.mehler t g x ≠ 0 :=
    ne_of_gt (hε.trans_le (mehler_bounds t hg.continuous hε hlo hhi x).1)
  have hderiv := ((hU.differentiable (by simp)).differentiableAt.hasDerivAt).log hne
  have hconst := (hasDerivAt_const x (1 : ℝ)).add hderiv
  have heq : logFactor t g = (fun _ : ℝ => (1 : ℝ)) +
      fun z => Real.log (GaussianMehler.mehler t g z) := by
    funext z
    rfl
  rw [heq]
  simpa using hconst.deriv

/-- A bound for the entropy logarithmic factor, with no assumption that ε or M straddles one. -/
theorem logFactor_bound (t : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    {ε M : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
    (hhi : ∀ z, g z ≤ M) (x : ℝ) :
    |logFactor t g x| ≤ 1 + |Real.log ε| + |Real.log M| := by
  obtain ⟨hloU, hhiU⟩ := mehler_bounds t hg hε hlo hhi x
  have hposU : 0 < GaussianMehler.mehler t g x := hε.trans_le hloU
  have hloglo : Real.log ε ≤ Real.log (GaussianMehler.mehler t g x) :=
    Real.log_le_log hε hloU
  have hloghi : Real.log (GaussianMehler.mehler t g x) ≤ Real.log M :=
    Real.log_le_log hposU hhiU
  have habs : |Real.log (GaussianMehler.mehler t g x)| ≤
      |Real.log ε| + |Real.log M| := by
    apply abs_le.mpr
    constructor
    · calc
        -(|Real.log ε| + |Real.log M|) ≤ -|Real.log ε| := by
          linarith [abs_nonneg (Real.log M)]
        _ ≤ Real.log ε := (abs_le.mp (le_refl (|Real.log ε|))).1
        _ ≤ Real.log (GaussianMehler.mehler t g x) := hloglo
    · calc
        Real.log (GaussianMehler.mehler t g x) ≤ Real.log M := hloghi
        _ ≤ |Real.log M| := le_abs_self _
        _ ≤ |Real.log ε| + |Real.log M| := by
          linarith [abs_nonneg (Real.log ε)]
  unfold logFactor
  calc
    |1 + Real.log (GaussianMehler.mehler t g x)| ≤
        |(1 : ℝ)| + |Real.log (GaussianMehler.mehler t g x)| := abs_add_le _ _
    _ ≤ 1 + |Real.log ε| + |Real.log M| := by
      norm_num at *
      linarith

/-- A uniform actual derivative bound for the entropy logarithmic factor. -/
theorem deriv_logFactor_bound (t : ℝ) (ht : 0 ≤ t)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {ε M B : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
    (hhi : ∀ z, g z ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) (x : ℝ) :
    ‖deriv (logFactor t g) x‖ ≤ B / ε := by
  have hgb : ∀ z, ‖g z‖ ≤ M := by
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hlo z))]
    exact hhi z
  have hB : 0 ≤ B := (norm_nonneg _).trans (hdgb 0)
  have hUpos : 0 < GaussianMehler.mehler t g x :=
    hε.trans_le (mehler_bounds t hg.continuous hε hlo hhi x).1
  have hUlo := (mehler_bounds t hg.continuous hε hlo hhi x).1
  have hdu := mehler_deriv_bound t ht hg hgb hdgb x
  rw [deriv_logFactor t hg hε hlo hhi hdgb x,
    Real.norm_eq_abs, abs_div, abs_of_pos hUpos]
  rw [Real.norm_eq_abs] at hdu
  calc
    |deriv (GaussianMehler.mehler t g) x| / GaussianMehler.mehler t g x ≤
        B / GaussianMehler.mehler t g x :=
      div_le_div_of_nonneg_right hdu hUpos.le
    _ ≤ B / ε := div_le_div_of_nonneg_left hB hε hUlo
/-- The concrete time-derivative integral from the already verified Mehler theorem. -/
def timeVelocity (t : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, deriv g (GaussianMehlerTimeDerivative.a t * x +
      GaussianMehlerTimeDerivative.b t * y) *
    (-GaussianMehlerTimeDerivative.a t * x +
      (GaussianMehlerTimeDerivative.a t ^ 2 / GaussianMehlerTimeDerivative.b t) * y) ∂γ

/-- A fixed positive-time neighborhood has a common linear Gaussian majorant
for the actual Mehler time velocity, after inner integration. -/
theorem timeVelocity_local_bound (t₀ : ℝ) (ht₀ : 0 < t₀)
    {s : ℝ} (hs : s ∈ {r : ℝ |
      GaussianMehlerTimeDerivative.b t₀ / 2 < GaussianMehlerTimeDerivative.b r} ∩
      Set.Ioi 0) (x : ℝ) {g : ℝ → ℝ}
    {B : ℝ} (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
    ‖timeVelocity s g x‖ ≤ B *
      (|x| + (∫ y : ℝ, |y| ∂γ) / (GaussianMehlerTimeDerivative.b t₀ / 2)) := by
  let c := GaussianMehlerTimeDerivative.b t₀ / 2
  have hc : 0 < c := (GaussianMehlerTimeDerivative.b_local_lower_bound t₀ ht₀).1
  have hB : 0 ≤ B := (norm_nonneg _).trans (hdgb 0)
  have hmoment : Integrable (fun y : ℝ => |y|) γ :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).abs
  have hmajor : Integrable (fun y : ℝ => B * (|x| + |y| / c)) γ := by
    convert ((integrable_const (|x|)).add (hmoment.const_mul (1 / c))).const_mul B using 1
    funext y
    dsimp [c]
    ring
  have hpoint : ∀ y : ℝ,
      ‖deriv g (GaussianMehlerTimeDerivative.a s * x +
        GaussianMehlerTimeDerivative.b s * y) *
        (-GaussianMehlerTimeDerivative.a s * x +
          (GaussianMehlerTimeDerivative.a s ^ 2 / GaussianMehlerTimeDerivative.b s) * y)‖
        ≤ B * (|x| + |y| / c) := by
    intro y
    rw [Real.norm_eq_abs, abs_mul]
    have hv := GaussianMehlerTimeDerivative.velocity_bound t₀ ht₀ hs x y
    have hderiv : |deriv g (GaussianMehlerTimeDerivative.a s * x +
        GaussianMehlerTimeDerivative.b s * y)| ≤ B := by
      simpa only [Real.norm_eq_abs] using hdgb _
    exact (mul_le_mul_of_nonneg_right hderiv (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hv hB)
  have hbound := norm_integral_le_of_norm_le hmajor (Filter.Eventually.of_forall hpoint)
  change ‖timeVelocity s g x‖ ≤ _ at hbound
  calc
    ‖timeVelocity s g x‖ ≤ ∫ y : ℝ, B * (|x| + |y| / c) ∂γ := hbound
    _ = B * (|x| + (∫ y : ℝ, |y| ∂γ) / c) := by
      rw [integral_const_mul]
      rw [integral_add (integrable_const _) (hmoment.div_const c)]
      rw [integral_div]
      simp [c]
/-- The concrete time-derivative integral is measurable in the spatial parameter. -/
theorem timeVelocity_measurable (t : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    Measurable (timeVelocity t g) := by
  have hdg : Measurable (deriv g) := (hg.continuous_deriv le_rfl).measurable
  have hjoint : Measurable (fun p : ℝ × ℝ =>
      deriv g (GaussianMehlerTimeDerivative.a t * p.1 +
        GaussianMehlerTimeDerivative.b t * p.2) *
      (-GaussianMehlerTimeDerivative.a t * p.1 +
        (GaussianMehlerTimeDerivative.a t ^ 2 /
          GaussianMehlerTimeDerivative.b t) * p.2)) := by
    fun_prop
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable
/-- Differentiation of the actual uncentered Gaussian entropy integral at positive time. -/
theorem hasDerivAt_entropy_raw (t : ℝ) (ht : 0 < t)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {ε M B : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
    (hhi : ∀ z, g z ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
    HasDerivAt
      (fun s => ∫ x, GaussianMehler.mehler s g x *
        Real.log (GaussianMehler.mehler s g x) ∂γ)
      (∫ x, logFactor t g x * timeVelocity t g x ∂γ) t := by
  let U : Set ℝ := {s : ℝ |
    GaussianMehlerTimeDerivative.b t / 2 < GaussianMehlerTimeDerivative.b s} ∩ Set.Ioi 0
  let c : ℝ := GaussianMehlerTimeDerivative.b t / 2
  let m : ℝ := ∫ y : ℝ, |y| ∂γ
  let L : ℝ := 1 + |Real.log ε| + |Real.log M|
  let F : ℝ → ℝ → ℝ := fun s x => GaussianMehler.mehler s g x *
    Real.log (GaussianMehler.mehler s g x)
  let F' : ℝ → ℝ → ℝ := fun s x => logFactor s g x * timeVelocity s g x
  let bound : ℝ → ℝ := fun x => L * B * (|x| + m / c)
  have hgb : ∀ z, ‖g z‖ ≤ M := by
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hlo z))]
    exact hhi z
  have hB : 0 ≤ B := (norm_nonneg _).trans (hdgb 0)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨hc, hU, hlocal⟩ := GaussianMehlerTimeDerivative.b_local_lower_bound t ht
  have hFmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) γ := by
    apply Filter.Eventually.of_forall
    intro s
    exact (Real.continuous_mul_log.measurable.comp
      (GaussianMehler.mehler_continuous hg.continuous hgb s).measurable).aestronglyMeasurable
  have hFint : Integrable (F t) γ :=
    (GaussianEntropyDissipation.entropyTrajectory_integrable hg.continuous hgb t).2
  have hF'meas : AEStronglyMeasurable (F' t) γ := by
    exact (((logFactor_contDiff_one t hg hε hlo hhi hdgb).continuous.measurable).mul
      (timeVelocity_measurable t hg)).aestronglyMeasurable
  have hmoment : Integrable (fun x : ℝ => |x|) γ :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).abs
  have hbound_int : Integrable bound γ := by
    convert (hmoment.add (integrable_const (m / c))).const_mul (L * B) using 1
  have hbound : ∀ᵐ x ∂γ, ∀ s ∈ U, ‖F' s x‖ ≤ bound x := by
    filter_upwards with x s hs
    change ‖logFactor s g x * timeVelocity s g x‖ ≤ L * B * (|x| + m / c)
    rw [norm_mul, Real.norm_eq_abs]
    have hlog : |logFactor s g x| ≤ L := logFactor_bound s hg.continuous hε hlo hhi x
    have hv := timeVelocity_local_bound t ht hs x hdgb
    have hmx : 0 ≤ |x| + m / c := by
      have hm : 0 ≤ m := integral_nonneg (fun y => abs_nonneg y)
      dsimp [c]
      positivity
    change ‖timeVelocity s g x‖ ≤ B * (|x| + m / c) at hv
    calc
      |logFactor s g x| * ‖timeVelocity s g x‖ ≤
          L * ‖timeVelocity s g x‖ :=
        mul_le_mul_of_nonneg_right hlog (norm_nonneg _)
      _ ≤ L * (B * (|x| + m / c)) := mul_le_mul_of_nonneg_left hv hL
      _ = L * B * (|x| + m / c) := by ring
  have hdiff : ∀ᵐ x ∂γ, ∀ s ∈ U, HasDerivAt (F · x) (F' s x) s := by
    filter_upwards with x s hs
    obtain ⟨hspos, _⟩ := hlocal s hs
    have huPos : 0 < GaussianMehler.mehler s g x :=
      hε.trans_le (mehler_bounds s hg.continuous hε hlo hhi x).1
    have htime := (GaussianMehlerTimeDerivative.hasDerivAt_mehler_time
      s hspos x hg hgb hdgb).2
    change HasDerivAt (fun r => GaussianMehler.mehler r g x) (timeVelocity s g x) s at htime
    have hchain := (Real.hasDerivAt_mul_log huPos.ne').comp s htime
    change HasDerivAt ((fun z : ℝ => z * Real.log z) ∘
      (fun r => GaussianMehler.mehler r g x))
      (logFactor s g x * timeVelocity s g x) s
    simpa only [logFactor, add_comm] using hchain
  obtain ⟨_, houter⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hU hFmeas hFint hF'meas hbound hbound_int hdiff
  exact houter
/-- The centered entropy has the same positive-time derivative as its uncentered
integral, because the Gaussian mean is invariant on a neighborhood of t. -/
theorem hasDerivAt_entropyTrajectory_raw (t : ℝ) (ht : 0 < t)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {ε M B : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
    (hhi : ∀ z, g z ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
    HasDerivAt (GaussianEntropyDissipation.entropyTrajectory g)
      (∫ x, logFactor t g x * timeVelocity t g x ∂γ) t := by
  have hgb : ∀ z, ‖g z‖ ≤ M := by
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hlo z))]
    exact hhi z
  have hraw := hasDerivAt_entropy_raw t ht hg hε hlo hhi hdgb
  let C : ℝ := (∫ x, g x ∂γ) * Real.log (∫ x, g x ∂γ)
  have hshift := hraw.sub_const C
  have heq : GaussianEntropyDissipation.entropyTrajectory g =ᶠ[𝓝 t]
      (fun s => (∫ x, GaussianMehler.mehler s g x *
        Real.log (GaussianMehler.mehler s g x) ∂γ) - C) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact GaussianEntropyDissipation.entropyTrajectory_eq_invariant_mean
      hg.continuous hgb s hs.le
  exact hshift.congr_of_eventuallyEq heq
/-- The Fisher integrand of the evolved positive bounded density is genuinely integrable. -/
theorem evolved_fisher_integrable (t : ℝ) (ht : 0 ≤ t)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {ε M B : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
    (hhi : ∀ z, g z ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
    Integrable (fun x => (deriv (GaussianMehler.mehler t g) x) ^ 2 /
      GaussianMehler.mehler t g x) γ := by
  have hgb : ∀ z, ‖g z‖ ≤ M := by
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hlo z))]
    exact hhi z
  exact GaussianFisher.fisherInformation_integrable hε
    (GaussianMehler.mehler_continuous hg.continuous hgb t).measurable
    (mehler_contDiff_one t hg hgb hdgb).continuous_deriv_one.measurable
    (fun x => (mehler_bounds t hg.continuous hε hlo hhi x).1)
    (fun x => by simpa only [Real.norm_eq_abs] using
      mehler_deriv_bound t ht hg hgb hdgb x)
/-- Fixed-time rotation identifies the raw entropy pairing with negative
Fisher information. Every product integral is established integrable first. -/
theorem entropy_pairing_eq_neg_fisher (t : ℝ) (ht : 0 < t)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {ε M B : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
    (hhi : ∀ z, g z ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
    (∫ x, logFactor t g x * timeVelocity t g x ∂γ) =
      -GaussianFisher.fisherInformation (GaussianMehler.mehler t g) := by
  let a : ℝ := GaussianMehlerTimeDerivative.a t
  let b : ℝ := GaussianMehlerTimeDerivative.b t
  let ψ : ℝ → ℝ := logFactor t g
  let k : ℝ → ℝ := deriv g
  let u : ℝ → ℝ := GaussianMehler.mehler t g
  let L : ℝ := 1 + |Real.log ε| + |Real.log M|
  have hbpos : 0 < b := GaussianMehlerTimeDerivative.b_pos t ht
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hab : a ^ 2 + b ^ 2 = 1 :=
    GaussianMehlerTimeDerivative.a_sq_add_b_sq t ht.le
  have hgb : ∀ z, ‖g z‖ ≤ M := by
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hlo z))]
    exact hhi z
  have hkmeas : Measurable k := (hg.continuous_deriv le_rfl).measurable
  have hkbound : ∀ z, |k z| ≤ B := by
    intro z
    simpa only [k, Real.norm_eq_abs] using hdgb z
  have hψC1 : ContDiff ℝ 1 ψ := logFactor_contDiff_one t hg hε hlo hhi hdgb
  have hψbound : ∀ x, |ψ x| ≤ L := fun x =>
    logFactor_bound t hg.continuous hε hlo hhi x
  have hψdbound : ∀ x, |deriv ψ x| ≤ B / ε := by
    intro x
    simpa only [ψ, Real.norm_eq_abs] using
      deriv_logFactor_bound t ht.le hg hε hlo hhi hdgb x
  obtain ⟨hL, hR, _, _⟩ := GaussianRotationStein.rotated_stein_integrable
    a b k ψ hkmeas hψC1 hkbound hψbound hψdbound
  have hrot := GaussianRotationStein.rotated_stein_identity
    a b hab k ψ hkmeas hψC1 hkbound hψbound hψdbound
  have hvel (x y : ℝ) :
      ψ x * (k (a * x + b * y) * (-a * x + (a ^ 2 / b) * y)) =
        (a / b) * (ψ x * k (a * x + b * y) * (-b * x + a * y)) := by
    field_simp
  have hinner (x : ℝ) : ψ x * timeVelocity t g x =
      (a / b) * (∫ y, ψ x * k (a * x + b * y) * (-b * x + a * y) ∂γ) := by
    calc
      ψ x * timeVelocity t g x =
          ∫ y, ψ x * (k (a * x + b * y) *
            (-a * x + (a ^ 2 / b) * y)) ∂γ := by
              rw [integral_const_mul]
              rfl
      _ = ∫ y, (a / b) * (ψ x * k (a * x + b * y) *
            (-b * x + a * y)) ∂γ := by
              apply integral_congr_ae
              filter_upwards with y
              exact hvel x y
      _ = (a / b) * ∫ y, ψ x * k (a * x + b * y) *
            (-b * x + a * y) ∂γ := integral_const_mul _ _
  have hpair : (∫ x, ψ x * timeVelocity t g x ∂γ) =
      (a / b) * ∫ p : ℝ × ℝ,
        ψ p.1 * k (a * p.1 + b * p.2) * (-b * p.1 + a * p.2) ∂(γ.prod γ) := by
    calc
      _ = ∫ x, (a / b) * (∫ y, ψ x * k (a * x + b * y) *
          (-b * x + a * y) ∂γ) ∂γ := by
        apply integral_congr_ae
        filter_upwards with x
        exact hinner x
      _ = (a / b) * ∫ x, (∫ y, ψ x * k (a * x + b * y) *
          (-b * x + a * y) ∂γ) ∂γ := integral_const_mul _ _
      _ = (a / b) * ∫ p : ℝ × ℝ,
          ψ p.1 * k (a * p.1 + b * p.2) * (-b * p.1 + a * p.2) ∂(γ.prod γ) := by
        rw [integral_prod _ hL]
  have hFubini : (∫ p : ℝ × ℝ,
      deriv ψ p.1 * k (a * p.1 + b * p.2) ∂(γ.prod γ)) =
      ∫ x, deriv ψ x * GaussianMehler.mehler t k x ∂γ := by
    rw [integral_prod _ hR]
    apply integral_congr_ae
    filter_upwards with x
    rw [integral_const_mul]
    rfl
  have hUderiv (x : ℝ) : deriv u x = a * GaussianMehler.mehler t k x := by
    have hbound : ∀ z, ‖g z‖ ≤ max M B := fun z => (hgb z).trans (le_max_left M B)
    have hdbound : ∀ z, ‖deriv g z‖ ≤ max M B :=
      fun z => (hdgb z).trans (le_max_right M B)
    exact GaussianFisher.deriv_mehler_C1 t hg hbound hdbound x
  have hpoint (x : ℝ) :
      -(a * (deriv ψ x * GaussianMehler.mehler t k x)) =
        -(deriv u x ^ 2 / u x) := by
    have huPos : 0 < u x :=
      hε.trans_le (mehler_bounds t hg.continuous hε hlo hhi x).1
    rw [deriv_logFactor t hg hε hlo hhi hdgb x, hUderiv x]
    dsimp [ψ, k, u] at *
    field_simp
  calc
    (∫ x, logFactor t g x * timeVelocity t g x ∂γ) =
        (a / b) * ∫ p : ℝ × ℝ,
          ψ p.1 * k (a * p.1 + b * p.2) * (-b * p.1 + a * p.2) ∂(γ.prod γ) := hpair
    _ = (a / b) * (-b * ∫ p : ℝ × ℝ,
          deriv ψ p.1 * k (a * p.1 + b * p.2) ∂(γ.prod γ)) := by rw [hrot]
    _ = -a * ∫ p : ℝ × ℝ,
          deriv ψ p.1 * k (a * p.1 + b * p.2) ∂(γ.prod γ) := by
          field_simp
    _ = -a * ∫ x, deriv ψ x * GaussianMehler.mehler t k x ∂γ := by rw [hFubini]
    _ = ∫ x, -(a * (deriv ψ x * GaussianMehler.mehler t k x)) ∂γ := by
          rw [integral_neg, integral_const_mul]
          ring
    _ = -GaussianFisher.fisherInformation u := by
          rw [GaussianFisher.fisherInformation, integral_neg]
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          exact neg_inj.mp (hpoint x)

/-- Positive-time dissipation of the actual centered Gaussian entropy along the
existing Mehler semigroup, with variance-one normalization. -/
theorem hasDerivAt_entropy_dissipation (t : ℝ) (ht : 0 < t)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {ε M B : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
    (hhi : ∀ z, g z ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
    HasDerivAt (GaussianEntropyDissipation.entropyTrajectory g)
      (-GaussianFisher.fisherInformation (GaussianMehler.mehler t g)) t := by
  have h := hasDerivAt_entropyTrajectory_raw t ht hg hε hlo hhi hdgb
  rw [entropy_pairing_eq_neg_fisher t ht hg hε hlo hhi hdgb] at h
  exact h

/-- The same identity stated for Mathlib's actual time derivative. -/
theorem deriv_entropy_dissipation (t : ℝ) (ht : 0 < t)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {ε M B : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
    (hhi : ∀ z, g z ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
    deriv (GaussianEntropyDissipation.entropyTrajectory g) t =
      -GaussianFisher.fisherInformation (GaussianMehler.mehler t g) :=
  (hasDerivAt_entropy_dissipation t ht hg hε hlo hhi hdgb).deriv
end OperatorDerivativeRewrite.Foundation.GaussianEntropyDissipationProof
