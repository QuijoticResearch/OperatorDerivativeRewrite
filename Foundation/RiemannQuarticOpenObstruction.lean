import Foundation.RiemannQuarticPolynomialLimitObstruction

/-! The certified quartic Laguerre obstruction persists on an open time
interval. The interval radius is existential, not a numerical bound. -/
noncomputable section
open Polynomial Filter Set Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticOpenObstruction
open RiemannQuarticFlow RiemannQuarticEvolution RiemannQuarticReality
open RiemannQuarticRealDerivatives RiemannQuarticPolynomialLimitObstruction

theorem real_jet_time_continuous (n : ℕ) (x : ℝ) :
    Continuous (fun t : ℝ => iteratedDeriv n (realFlow t) x) := by
  simp_rw [realFlow_iteratedDeriv]
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := ((jet_time_hasDerivAt n t (x : ℂ)).add
    ((jet_time_hasDerivAt n t (-(x : ℂ))).const_mul ((-1 : ℂ)^n))).div_const 2
  exact Complex.continuous_re.continuousAt.comp h.continuousAt

theorem real_laguerre_time_continuous (x : ℝ) :
    Continuous (fun t : ℝ => (deriv (realFlow t) x)^2 -
      realFlow t x * iteratedDeriv 2 (realFlow t) x) := by
  have h := ((real_jet_time_continuous 1 x).pow 2).sub
    ((real_jet_time_continuous 0 x).mul (real_jet_time_continuous 2 x))
  convert h using 1
  ext t
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, iteratedDeriv_zero, iteratedDeriv_one]

theorem exists_open_time_laguerre_obstruction :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t-8| < δ →
      (deriv (realFlow t) (632083/10000))^2 -
        realFlow t (632083/10000) * iteratedDeriv 2 (realFlow t) (632083/10000) < 0 := by
  have hn : (deriv (realFlow 8) (632083/10000))^2 -
      realFlow 8 (632083/10000) * iteratedDeriv 2 (realFlow 8) (632083/10000) < 0 := by
    have h := RiemannQuarticLaguerreWitness.actual_real_derivative_negative
    linarith
  have he := (real_laguerre_time_continuous (632083/10000)).continuousAt.eventually
    (Iio_mem_nhds hn)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ,hδ,fun t ht => hd (by simpa only [Real.dist_eq] using ht)⟩

theorem exists_open_time_no_polynomial_limit :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t-8| < δ →
      ¬ ∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
        TendstoLocallyUniformlyOn
          (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow t) atTop univ := by
  obtain ⟨δ,hδ,hd⟩ := exists_open_time_laguerre_obstruction
  refine ⟨δ,hδ,?_⟩
  intro t ht h
  obtain ⟨P,hP,hlim⟩ := h
  have hp := real_jet_laguerre_nonneg_of_polynomial_limit_on
    t P univ isOpen_univ hP hlim (632083/10000) (mem_univ _)
  exact (not_lt_of_ge hp) (hd t ht)

theorem eventual_polynomial_limit_start_strictly_above_eight :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : ℝ,
      (∀ t : ℝ, T ≤ t → ∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
        TendstoLocallyUniformlyOn
          (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow t) atTop univ) →
      8 + ε < T := by
  obtain ⟨δ,hδ,hd⟩ := exists_open_time_no_polynomial_limit
  refine ⟨δ/2,by positivity,?_⟩
  intro T hT
  by_contra h
  have ht : T ≤ 8+δ/2 := le_of_not_gt h
  exact hd (8+δ/2) (by rw [show 8+δ/2-8=δ/2 by ring, abs_of_pos (by positivity)]; linarith)
    (hT (8+δ/2) ht)

/-- Actual starting times for eventual locally uniform approximation by
split real polynomials. Nonemptiness is not assumed by this definition. -/
def polynomialLimitStarts : Set ℝ :=
  {T | ∀ t : ℝ, T ≤ t → ∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
    TendstoLocallyUniformlyOn
      (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow t) atTop univ}

theorem strict_infimum_lower_bound_of_nonempty (hS : polynomialLimitStarts.Nonempty) :
    8 < sInf polynomialLimitStarts := by
  obtain ⟨ε,hε,hbound⟩ := eventual_polynomial_limit_start_strictly_above_eight
  have hlower : 8+ε ≤ sInf polynomialLimitStarts :=
    le_csInf hS fun T hT => (hbound T hT).le
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticOpenObstruction
