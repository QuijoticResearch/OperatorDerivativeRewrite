import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Moments.Variance

/-! Differentiation of normalized exponential-tilt expectations for bounded observables.
All expectations below are actual integrals on the displayed probability space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.BoundedExponentialTiltResponse
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def weighted (X f : Ω → ℝ) (t : ℝ) : ℝ := ∫ ω, f ω * Real.exp (t * X ω) ∂μ
def partition (X : Ω → ℝ) (t : ℝ) : ℝ := weighted μ X (fun _ => 1) t
def expectation (X f : Ω → ℝ) (t : ℝ) : ℝ := weighted μ X f t / partition μ X t
def variance (X f : Ω → ℝ) (t : ℝ) : ℝ :=
  expectation μ X (fun ω => f ω ^ 2) t - (expectation μ X f t)^2

theorem weighted_zero (X f : Ω → ℝ) : weighted μ X f 0 = ∫ ω, f ω ∂μ := by
  simp [weighted]

theorem partition_zero (X : Ω → ℝ) : partition μ X 0 = 1 := by
  simp [partition, weighted]

theorem expectation_zero (X f : Ω → ℝ) : expectation μ X f 0 = ∫ ω, f ω ∂μ := by
  rw [expectation, weighted_zero, partition_zero, div_one]

theorem exponential_integrable (X : Ω → ℝ) (hX : Measurable X)
    (hXb : ∀ ω, |X ω| ≤ 1) (t : ℝ) : Integrable (fun ω => Real.exp (t * X ω)) μ := by
  apply Integrable.mono' (integrable_const (Real.exp |t|))
    ((measurable_const.mul hX).exp.aestronglyMeasurable)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * X ω ≤ |t * X ω| := le_abs_self _
    _ = |t| * |X ω| := abs_mul _ _
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (hXb ω) (abs_nonneg t)
    _ = |t| := mul_one _

theorem partition_pos (X : Ω → ℝ) (hX : Measurable X)
    (hXb : ∀ ω, |X ω| ≤ 1) (t : ℝ) : 0 < partition μ X t := by
  unfold partition weighted
  simp only [one_mul]
  apply (integral_pos_iff_support_of_nonneg (fun ω => (Real.exp_pos (t * X ω)).le)
    (exponential_integrable μ X hX hXb t)).mpr
  have hs : Function.support (fun ω => Real.exp (t * X ω)) = univ := by
    ext ω; simp [Function.mem_support, Real.exp_ne_zero]
  rw [hs]
  simp

def density (X : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ := Real.exp (t * X ω) / partition μ X t
def tiltedMeasure (X : Ω → ℝ) (t : ℝ) : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (density μ X t ω))

theorem density_nonneg (X : Ω → ℝ) (hX : Measurable X)
    (hXb : ∀ ω, |X ω| ≤ 1) (t : ℝ) (ω : Ω) : 0 ≤ density μ X t ω :=
  (div_pos (Real.exp_pos _) (partition_pos μ X hX hXb t)).le

theorem density_integral (X : Ω → ℝ) (hX : Measurable X)
    (hXb : ∀ ω, |X ω| ≤ 1) (t : ℝ) : (∫ ω, density μ X t ω ∂μ) = 1 := by
  change (∫ ω, Real.exp (t * X ω) / partition μ X t ∂μ) = 1
  rw [integral_div]
  have hz : (∫ ω, Real.exp (t * X ω) ∂μ) = partition μ X t := by
    simp only [partition, weighted, one_mul]
  rw [hz]
  exact div_self (partition_pos μ X hX hXb t).ne'

theorem tiltedMeasure_probability (X : Ω → ℝ) (hX : Measurable X)
    (hXb : ∀ ω, |X ω| ≤ 1) (t : ℝ) : IsProbabilityMeasure (tiltedMeasure μ X t) := by
  constructor
  rw [tiltedMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hi : Integrable (density μ X t) μ :=
    (exponential_integrable μ X hX hXb t).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (density_nonneg μ X hX hXb t)), density_integral μ X hX hXb t]
  norm_num

theorem tilted_integral (X f : Ω → ℝ) (hX : Measurable X)
    (hXb : ∀ ω, |X ω| ≤ 1) (t : ℝ) :
    (∫ ω, f ω ∂tiltedMeasure μ X t) = expectation μ X f t := by
  have hm : Measurable (density μ X t) := (measurable_const.mul hX).exp.div_const _
  rw [tiltedMeasure, integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (density_nonneg μ X hX hXb t _), smul_eq_mul]
  have he : (fun ω => density μ X t ω * f ω) =
      fun ω => (f ω * Real.exp (t * X ω)) / partition μ X t := by
    ext ω; unfold density; ring
  rw [he, integral_div]
  rfl

theorem weighted_hasDerivAt_zero (X f : Ω → ℝ) (hX : Measurable X) (hf : Measurable f)
    (hXb : ∀ ω, |X ω| ≤ 1) (M : ℝ) (hM : 0 ≤ M) (hfb : ∀ ω, |f ω| ≤ M) :
    HasDerivAt (weighted μ X f) (∫ ω, f ω * X ω ∂μ) 0 := by
  let F := fun t ω => f ω * Real.exp (t * X ω)
  let F' := fun t ω => f ω * (X ω * Real.exp (t * X ω))
  have hs : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hmeas : ∀ t, AEStronglyMeasurable (F t) μ := fun t =>
    (hf.mul ((measurable_const.mul hX).exp)).aestronglyMeasurable
  have hint : Integrable (F 0) μ := by
    apply Integrable.mono' (integrable_const M) (hmeas 0)
    filter_upwards with ω
    simpa [F, Real.norm_eq_abs] using hfb ω
  have hdmeas : AEStronglyMeasurable (F' 0) μ := by
    exact (hf.mul (hX.mul ((measurable_const.mul hX).exp))).aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂μ, ∀ t ∈ Ioo (-1 : ℝ) 1, ‖F' t ω‖ ≤ M * Real.exp 1 := by
    filter_upwards with ω t ht
    have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
    have htx : t * X ω ≤ 1 := by
      calc
        t * X ω ≤ |t * X ω| := le_abs_self _
        _ = |t| * |X ω| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul hta (hXb ω) (abs_nonneg _) (by norm_num)
        _ = 1 := one_mul _
    calc
      ‖F' t ω‖ = |f ω| * (|X ω| * Real.exp (t * X ω)) := by
        simp [F', norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ M * (1 * Real.exp 1) := by
        gcongr
        · exact hfb ω
        · exact hXb ω
      _ = M * Real.exp 1 := by ring
  have hdiff : ∀ᵐ ω ∂μ, ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt (F · ω) (F' t ω) t := by
    filter_upwards with ω t _
    have hd := ((Real.hasDerivAt_exp (t * X ω)).comp t
      ((hasDerivAt_id t).mul_const (X ω))).const_mul (f ω)
    simpa only [F, F', Function.comp_def, id_eq, one_mul, mul_comm, mul_left_comm,
      mul_assoc] using hd
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall hmeas) hint hdmeas hbound (integrable_const _) hdiff
  change HasDerivAt (fun t => ∫ ω, f ω * Real.exp (t * X ω) ∂μ) _ 0
  simpa only [F, F', zero_mul, Real.exp_zero, mul_one] using hd

theorem expectation_hasDerivAt_zero (X f : Ω → ℝ) (hX : Measurable X) (hf : Measurable f)
    (hXb : ∀ ω, |X ω| ≤ 1) (M : ℝ) (hM : 0 ≤ M) (hfb : ∀ ω, |f ω| ≤ M) :
    HasDerivAt (expectation μ X f)
      ((∫ ω, f ω * X ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, X ω ∂μ)) 0 := by
  have hd := weighted_hasDerivAt_zero μ X f hX hf hXb M hM hfb
  have hz := weighted_hasDerivAt_zero μ X (fun _ => 1) hX measurable_const hXb 1
    (by norm_num) (fun _ => by norm_num)
  have hp : HasDerivAt (partition μ X) (∫ ω, X ω ∂μ) 0 := by
    change HasDerivAt (weighted μ X (fun _ => 1)) _ 0
    simpa only [one_mul] using hz
  have hq := hd.div hp (by rw [partition_zero]; norm_num)
  rw [show expectation μ X f = weighted μ X f / partition μ X from rfl]
  simpa only [weighted_zero, partition_zero, mul_one, one_pow, div_one] using hq

theorem variance_hasDerivAt_zero (X f : Ω → ℝ) (hX : Measurable X) (hf : Measurable f)
    (hXb : ∀ ω, |X ω| ≤ 1) (M : ℝ) (hM : 0 ≤ M) (hfb : ∀ ω, |f ω| ≤ M) :
    HasDerivAt (variance μ X f)
      (((∫ ω, f ω^2 * X ω ∂μ) - (∫ ω, f ω^2 ∂μ) * (∫ ω, X ω ∂μ)) -
        2 * (∫ ω, f ω ∂μ) *
          ((∫ ω, f ω * X ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, X ω ∂μ))) 0 := by
  have hf2 : ∀ ω, |f ω ^ 2| ≤ M^2 := by
    intro ω
    simpa only [sq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg (f ω)) (hfb ω) 2
  have hd2 := expectation_hasDerivAt_zero μ X (fun ω => f ω^2) hX (hf.pow_const 2)
    hXb (M^2) (sq_nonneg M) hf2
  have hd := expectation_hasDerivAt_zero μ X f hX hf hXb M hM hfb
  have hout := hd2.sub (hd.pow 2)
  rw [show variance μ X f = expectation μ X (fun ω => f ω^2) - (expectation μ X f)^2 from rfl]
  simpa only [expectation_zero, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by rfl,
    pow_one] using hout

theorem bounded_power_integrable (X : Ω → ℝ) (hX : Measurable X)
    (hXb : ∀ ω, |X ω| ≤ 1) (k : ℕ) : Integrable (fun ω => X ω^k) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (hX.pow_const k).aestronglyMeasurable
  filter_upwards with ω
  simpa only [Real.norm_eq_abs, abs_pow, one_pow] using
    pow_le_pow_left₀ (abs_nonneg (X ω)) (hXb ω) k

/-- The moment conditions are hypotheses on actual integrals, not a sphere-law construction. -/
theorem polynomial_variance_hasDerivAt_zero (X : Ω → ℝ) (hX : Measurable X)
    (hXb : ∀ ω, |X ω| ≤ 1)
    (h1 : (∫ ω, X ω ∂μ) = 0) (h2 : (∫ ω, X ω^2 ∂μ) = 1/4)
    (h3 : (∫ ω, X ω^3 ∂μ) = 0) (h4 : (∫ ω, X ω^4 ∂μ) = 1/8)
    (h5 : (∫ ω, X ω^5 ∂μ) = 0) :
    HasDerivAt (variance μ X (fun ω => X ω + X ω^2)) (1/8) 0 := by
  have hi := bounded_power_integrable μ X hX hXb
  have hi1 : Integrable X μ := by simpa only [pow_one] using hi 1
  have hfb : ∀ ω, |X ω + X ω^2| ≤ 2 := by
    intro ω
    have hs : |X ω^2| ≤ 1 := by
      simpa only [abs_pow, one_pow] using pow_le_pow_left₀ (abs_nonneg (X ω)) (hXb ω) 2
    calc
      |X ω + X ω^2| ≤ |X ω| + |X ω^2| := abs_add_le _ _
      _ ≤ 2 := by linarith [hXb ω]
  have hf : (∫ ω, X ω + X ω^2 ∂μ) = 1/4 := by
    rw [integral_add hi1 (hi 2), h1, h2]; norm_num
  have hfx : (∫ ω, (X ω + X ω^2) * X ω ∂μ) = 1/4 := by
    calc
      _ = ∫ ω, X ω^2 + X ω^3 ∂μ := by apply integral_congr_ae; filter_upwards with ω; ring
      _ = _ := by rw [integral_add (hi 2) (hi 3), h2, h3]; norm_num
  have hf2x : (∫ ω, (X ω + X ω^2)^2 * X ω ∂μ) = 1/4 := by
    calc
      _ = ∫ ω, (X ω^3 + 2 * X ω^4) + X ω^5 ∂μ := by
        apply integral_congr_ae; filter_upwards with ω; ring
      _ = _ := by
        have hsum : Integrable (fun ω => X ω^3 + 2 * X ω^4) μ :=
          (hi 3).add ((hi 4).const_mul 2)
        rw [integral_add hsum (hi 5),
          integral_add (hi 3) ((hi 4).const_mul 2), integral_const_mul, h3, h4, h5]
        norm_num
  have hd := variance_hasDerivAt_zero μ X (fun ω => X ω + X ω^2) hX
    (hX.add (hX.pow_const 2)) hXb 2 (by norm_num) hfb
  rw [h1, hf, hfx, hf2x] at hd
  norm_num at hd
  exact hd

theorem positive_derivative_arbitrarily_small_increase (v : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt v d 0) (hpos : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ t, 0 < t ∧ t < ε ∧ v 0 < v t := by
  have hs := hd.tendsto_slope_zero_right.eventually (eventually_gt_nhds hpos)
  have heps : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε :=
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < ε ∧ v 0 < v t := by
    filter_upwards [hs, heps, self_mem_nhdsWithin] with t hs heps ht
    refine ⟨ht, heps, ?_⟩
    simp only [zero_add, smul_eq_mul] at hs
    have htinv : 0 ≤ t⁻¹ := le_of_lt (inv_pos.mpr ht)
    by_contra h
    have hn : v t - v 0 ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
    have := mul_nonpos_of_nonneg_of_nonpos htinv hn
    linarith
  exact he.exists

theorem polynomial_variance_increases_near_zero (X : Ω → ℝ) (hX : Measurable X)
    (hXb : ∀ ω, |X ω| ≤ 1)
    (h1 : (∫ ω, X ω ∂μ) = 0) (h2 : (∫ ω, X ω^2 ∂μ) = 1/4)
    (h3 : (∫ ω, X ω^3 ∂μ) = 0) (h4 : (∫ ω, X ω^4 ∂μ) = 1/8)
    (h5 : (∫ ω, X ω^5 ∂μ) = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ t, 0 < t ∧ t < ε ∧
      variance μ X (fun ω => X ω + X ω^2) 0 < variance μ X (fun ω => X ω + X ω^2) t :=
  positive_derivative_arbitrarily_small_increase _ _
    (polynomial_variance_hasDerivAt_zero μ X hX hXb h1 h2 h3 h4 h5) (by norm_num) ε hε

end OperatorDerivativeRewrite.Foundation.BoundedExponentialTiltResponse
