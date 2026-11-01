import Foundation.IBMConstructedSources
import Foundation.StochasticCauchyGaussianNormalization
import Mathlib.Probability.Distributions.Gaussian.Basic

/-! A genuine continuous circular Brownian realization from the existing
constructed Brownian paths on independent Gaussian factors.  This module does
not assert a two-source predictable stochastic integral or a Cauchy projector. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyBrownianRealization
open InfiniteGaussian IBMSourceLaws IBMConstructedSources
open StochasticCauchyGaussianNormalization

/-- Both real sources are the already constructed continuous Brownian path,
on independent factors of the existing product probability space. -/
def path (w : JointSample) : C(ℝ≥0, ℂ) :=
  ⟨fun t => z (clockPath w.1 t, clockPath w.2 t), by unfold z; fun_prop⟩

def value (t : ℝ≥0) (w : JointSample) : ℂ := path w t

theorem value_eq (t : ℝ≥0) (w : JointSample) :
    value t w = (clockPath w.1 t : ℂ) + Complex.I * (clockPath w.2 t : ℂ) := rfl

theorem value_continuous (w : JointSample) : Continuous (fun t => value t w) :=
  (path w).continuous

theorem value_measurable (t : ℝ≥0) : Measurable (value t) := by
  exact z_measurable.comp
    (((ContinuousMap.measurable_eval t).comp (clockPath_measurable.comp measurable_fst)).prodMk
     ((ContinuousMap.measurable_eval t).comp (clockPath_measurable.comp measurable_snd)))

theorem path_measurable : Measurable path :=
  ContinuousMap.measurable_iff_eval.mpr value_measurable

theorem value_jointly_measurable :
    Measurable (fun p : ℝ≥0 × JointSample => value p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable value_continuous value_measurable

theorem source_paths_independent :
    IndepFun (fun w : JointSample => clockPath w.1)
      (fun w : JointSample => clockPath w.2) jointMeasure :=
  indepFun_prod clockPath_measurable clockPath_measurable

theorem real_isBrownian :
    IsBrownianReal (fun t w => (value t w).re) jointMeasure := by
  have he (t : ℝ≥0) (w : JointSample) : (value t w).re = clockPath w.1 t := by
    simp [value_eq]
  constructor
  · constructor
    intro I
    simpa only [he, jointMeasure, Function.comp_def] using
      (clock_isBrownian.toIsPreBrownianReal.hasLaw I).comp
      (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).hasLaw
  · exact Filter.Eventually.of_forall fun w =>
      Complex.continuous_re.comp (value_continuous w)

theorem imag_isBrownian :
    IsBrownianReal (fun t w => (value t w).im) jointMeasure := by
  have he (t : ℝ≥0) (w : JointSample) : (value t w).im = clockPath w.2 t := by
    simp [value_eq]
  constructor
  · constructor
    intro I
    simpa only [he, jointMeasure, Function.comp_def] using
      (clock_isBrownian.toIsPreBrownianReal.hasLaw I).comp
      (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).hasLaw
  · exact Filter.Eventually.of_forall fun w =>
      Complex.continuous_im.comp (value_continuous w)

/-- Every terminal marginal matches the exact product-law normalization already
audited in the Cauchy library: E|Z_t|²=2t. -/
private theorem coordinates_hasLaw (t : ℝ≥0) :
    HasLaw (fun w : JointSample => (clockPath w.1 t, clockPath w.2 t)) (law t) jointMeasure := by
  have hm : Measurable (fun w => clockPath w t) :=
    (ContinuousMap.measurable_eval t).comp clockPath_measurable
  have hl := clock_isBrownian.toIsPreBrownianReal.hasLaw_eval t
  have hx := hl.comp (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).hasLaw
  have hy := hl.comp (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).hasLaw
  exact (indepFun_prod hm hm).hasLaw_prod hx hy

theorem value_hasLaw (t : ℝ≥0) : HasLaw (value t) (complexLaw t) jointMeasure :=
  (hasLaw_z t).comp (coordinates_hasLaw t)

/-- Exact complex increment law, including reversed and equal times. -/
theorem increment_hasLaw (s t : ℝ≥0) :
    HasLaw (fun w => value t w - value s w)
      (complexLaw (nndist (t : ℝ) (s : ℝ))) jointMeasure := by
  have hm : Measurable (fun w => clockPath w t - clockPath w s) :=
    ((ContinuousMap.measurable_eval t).comp clockPath_measurable).sub
      ((ContinuousMap.measurable_eval s).comp clockPath_measurable)
  have hl := clock_isBrownian.toIsPreBrownianReal.hasLaw_sub t s
  have hx := hl.comp (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).hasLaw
  have hy := hl.comp (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).hasLaw
  have hz := (hasLaw_z (nndist (t : ℝ) (s : ℝ))).comp
    ((indepFun_prod hm hm).hasLaw_prod hx hy)
  have hz' : HasLaw (fun w : JointSample =>
      z (clockPath w.1 t - clockPath w.1 s, clockPath w.2 t - clockPath w.2 s))
      (complexLaw (nndist (t : ℝ) (s : ℝ))) jointMeasure := by
    simpa only [Function.comp_def, Pi.sub_apply, jointMeasure] using hz
  convert hz' using 1
  funext w
  simp only [value_eq, z, Complex.ofReal_sub]
  ring

/-- This continuous linear map combines two real coordinate vectors. -/
def finiteJoin (I : Finset ℝ≥0) : ((I → ℝ) × (I → ℝ)) →L[ℝ] (I → ℂ) where
  toFun q i := z (q.1 i, q.2 i)
  map_add' q r := by ext i; simp [z]; ring
  map_smul' c q := by ext i; simp [z, Complex.real_smul]; ring
  cont := by unfold z; fun_prop

/-- Explicit finite-dimensional law from the two standard Brownian projective
families. Their real covariance matrices are the verified min(s,t) matrices. -/
def finiteLaw (I : Finset ℝ≥0) : Measure (I → ℂ) :=
  ((BrownianReal.projectiveFamily I).prod (BrownianReal.projectiveFamily I)).map (finiteJoin I)

theorem finiteLaw_gaussian (I : Finset ℝ≥0) : IsGaussian (finiteLaw I) := by
  unfold finiteLaw
  infer_instance

/-- All finite-dimensional distributions, not merely pairwise covariances. -/
theorem finite_hasLaw (I : Finset ℝ≥0) :
    HasLaw (fun w => I.restrict (value · w)) (finiteLaw I) jointMeasure := by
  have hm : Measurable (fun w : SampleSpace => I.restrict (fun t => clockPath w t)) :=
    Measurable.of_eval fun i => by
      change Measurable (fun w : SampleSpace => clockPath w (i : ℝ≥0))
      exact (ContinuousMap.measurable_eval (i : ℝ≥0)).comp clockPath_measurable
  have hl := clock_isBrownian.toIsPreBrownianReal.hasLaw I
  have hx := hl.comp (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).hasLaw
  have hy := hl.comp (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).hasLaw
  have hp := (indepFun_prod hm hm).hasLaw_prod hx hy
  have hj : HasLaw (finiteJoin I) (finiteLaw I)
      ((BrownianReal.projectiveFamily I).prod (BrownianReal.projectiveFamily I)) :=
    ⟨(finiteJoin I).measurable.aemeasurable, rfl⟩
  exact hj.comp hp

theorem isGaussianProcess : IsGaussianProcess value jointMeasure where
  hasGaussianLaw I := by
    have := finiteLaw_gaussian I
    exact (finite_hasLaw I).hasGaussianLaw


/-- Independence of the actual entire real and imaginary coordinate families. -/
theorem components_independent :
    IndepFun (fun w : JointSample => fun t => (value t w).re)
      (fun w : JointSample => fun t => (value t w).im) jointMeasure := by
  have hm : Measurable (fun w : SampleSpace => fun t : ℝ≥0 => clockPath w t) :=
    Measurable.of_eval fun t => (ContinuousMap.measurable_eval t).comp clockPath_measurable
  simpa only [value_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, mul_zero, sub_zero, zero_add, add_zero, jointMeasure] using
    indepFun_prod hm hm

private theorem re_memLp (t : ℝ≥0) : MemLp (fun w => (value t w).re) 2 jointMeasure :=
  (real_isBrownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval t).memLp_two

private theorem im_memLp (t : ℝ≥0) : MemLp (fun w => (value t w).im) 2 jointMeasure :=
  (imag_isBrownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval t).memLp_two

private theorem inner_coordinates (x y : ℂ) :
    inner ℝ x y = x.re*y.re+x.im*y.im := by simp [Complex.inner]; ring

/-- Full real-bilinear covariance, which distinguishes complex covariance from
merely a scalar second-moment identity. -/
theorem inner_covariance (s t : ℝ≥0) (x y : ℂ) :
    cov[(fun w => inner ℝ x (value s w)), (fun w => inner ℝ y (value t w)); jointMeasure] =
      inner ℝ x y * (min s t : ℝ≥0) := by
  have hcross (a b : ℝ≥0) :
      cov[(fun w => (value a w).re), (fun w => (value b w).im); jointMeasure]=0 := by
    have hi := components_independent.comp (measurable_pi_apply a) (measurable_pi_apply b)
    exact hi.covariance_eq_zero (re_memLp a) (im_memLp b)
  have hcross' (a b : ℝ≥0) :
      cov[(fun w => (value a w).im), (fun w => (value b w).re); jointMeasure]=0 := by
    rw [covariance_comm]
    exact hcross b a
  simp_rw [inner_coordinates]
  change cov[x.re • (fun w => (value s w).re) + x.im • (fun w => (value s w).im),
    y.re • (fun w => (value t w).re) + y.im • (fun w => (value t w).im); jointMeasure] = _
  rw [covariance_add_left ((re_memLp s).const_smul _) ((im_memLp s).const_smul _)
    (((re_memLp t).const_smul _).add ((im_memLp t).const_smul _)),
    covariance_add_right ((re_memLp s).const_smul _)
      ((re_memLp t).const_smul _) ((im_memLp t).const_smul _),
    covariance_add_right ((im_memLp s).const_smul _)
      ((re_memLp t).const_smul _) ((im_memLp t).const_smul _)]
  simp only [covariance_smul_left, covariance_smul_right, hcross, hcross',
    real_isBrownian.toIsPreBrownianReal.covariance_fun_eval,
    imag_isBrownian.toIsPreBrownianReal.covariance_fun_eval]
  ring

private theorem inner_memLp (t : ℝ≥0) (x : ℂ) :
    MemLp (fun w => inner ℝ x (value t w)) 2 jointMeasure := by
  exact ((isGaussianProcess.hasGaussianLaw_eval t).map (innerSL ℝ x)).memLp_two

private theorem separated_increment_covariance (r s t u : ℝ≥0)
    (hrs : r ≤ s) (hst : s ≤ t) (htu : t ≤ u) (x y : ℂ) :
    cov[(fun w => inner ℝ x (value s w-value r w)),
      (fun w => inner ℝ y (value u w-value t w)); jointMeasure]=0 := by
  simp_rw [inner_sub_right]
  rw [covariance_fun_sub_fun_sub (inner_memLp s x) (inner_memLp r x)
    (inner_memLp u y) (inner_memLp t y)]
  simp only [inner_covariance, min_eq_left (hst.trans htu), min_eq_left hst,
    min_eq_left (hrs.trans (hst.trans htu)), min_eq_left (hrs.trans hst)]
  ring

/-- All finite chronological increment families are independent, on the actual
joint probability space; this is not inferred from marginals alone. -/
theorem independent_increments : HasIndepIncrements value jointMeasure := by
  intro n t ht
  refine (isGaussianProcess.hasGaussianLaw_increments (t := t)).iIndepFun_of_covariance_inner ?_
  intro i j hij x y
  rcases lt_or_gt_of_ne hij with h | h
  · exact separated_increment_covariance _ _ _ _
      (ht (Fin.castSucc_le_succ i))
      (ht (Fin.succ_le_castSucc_iff.mpr h)) (ht (Fin.castSucc_le_succ j)) x y
  · rw [covariance_comm]
    exact separated_increment_covariance _ _ _ _
      (ht (Fin.castSucc_le_succ j))
      (ht (Fin.succ_le_castSucc_iff.mpr h)) (ht (Fin.castSucc_le_succ i)) y x


theorem value_zero_ae : ∀ᵐ w ∂jointMeasure, value 0 w = 0 := by
  filter_upwards [real_isBrownian.toIsPreBrownianReal.eval_zero_ae_eq_zero,
    imag_isBrownian.toIsPreBrownianReal.eval_zero_ae_eq_zero] with w hr hi
  exact Complex.ext (by simpa using hr) (by simpa using hi)

theorem value_memLp (t : ℝ≥0) : MemLp (value t) 2 jointMeasure :=
  (isGaussianProcess.hasGaussianLaw_eval t).memLp_two

/-- Integrability is transported from the actual independent Gaussian pair;
the following moment identities are genuine integrals. -/
theorem exponential_memLp (t : ℝ≥0) :
    MemLp (fun w => Complex.exp (value t w)) 2 jointMeasure :=
  (coordinates_hasLaw t).memLp_comp (StochasticCauchyGaussianNormalization.exponential_memLp t)

theorem second_moment (t : ℝ≥0) :
    (∫ w, ‖value t w‖ ^ 2 ∂jointMeasure) = 2 * (t : ℝ) := by
  have he := (coordinates_hasLaw t).integral_comp (f := fun q => ‖z q‖ ^ 2)
    ((z_measurable.norm.pow_const 2).aestronglyMeasurable)
  exact he.trans (z_second_moment t)

/-- A direct realized consequence, now without a supplied process-law premise. -/
theorem exponential_mean (t : ℝ≥0) :
    (∫ w, Complex.exp (value t w) ∂jointMeasure) = 1 :=
  exponential_mean_of_hasLaw t (value_hasLaw t)

theorem exponential_centered_energy (t : ℝ≥0) :
    (∫ w, ‖Complex.exp (value t w) - 1‖ ^ 2 ∂jointMeasure) = Real.exp (2 * (t : ℝ)) - 1 :=
  centered_energy_of_hasLaw t (value_hasLaw t)

/-- Correct energy of the normalized process obtained by deterministic half-time. -/
theorem normalized_exponential_energy (t : ℝ≥0) :
    (∫ w, ‖Complex.exp (value (t/2) w)-1‖ ^ 2 ∂jointMeasure) = Real.exp (t : ℝ)-1 := by
  rw [exponential_centered_energy]
  push_cast
  ring_nf

/-- The manuscript's displayed energy fails for an actual normalized process,
not only for a proposed terminal Gaussian marginal. -/
theorem normalized_exponential_counter (t : ℝ≥0) (ht : 0 < t) :
    (∫ w, ‖Complex.exp (value (t/2) w)-1‖ ^ 2 ∂jointMeasure) < manuscriptEnergy t := by
  rw [exponential_centered_energy]
  simpa only [centered_energy] using normalized_counter t ht

theorem unnormalized_exponential_counter (t : ℝ≥0) (ht : 0 < t) :
    manuscriptEnergy t < (∫ w, ‖Complex.exp (value t w)-1‖ ^ 2 ∂jointMeasure) := by
  rw [exponential_centered_energy]
  simpa only [centered_energy] using unnormalized_counter t ht

end OperatorDerivativeRewrite.Foundation.StochasticCauchyBrownianRealization
