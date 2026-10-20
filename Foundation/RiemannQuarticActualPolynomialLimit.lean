import Foundation.RiemannQuarticDenominatorLimit
import Foundation.RiemannQuarticOpenObstruction

/-! Actual real split polynomials approximate the quartic transform
whenever all its zeros are real. The convergence is locally uniform on
the whole complex plane, with the actual H_t(0) normalization restored. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn Polynomial
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticActualPolynomialLimit
open RiemannQuarticFlow RiemannQuarticPolynomialFactors
open RiemannQuarticCanonicalReconstruction RiemannQuarticOpenObstruction

theorem actual_polynomial_limit_of_real_zeros (t : ℝ)
    (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) :
    ∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
      TendstoLocallyUniformlyOn
        (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow t) atTop univ := by
  obtain ⟨r,h,hdata,hB,hscale⟩ :=
    RiemannQuarticCanonicalProductLimit.exists_actual_product_approximation t
  have hr : Tendsto r atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨max 1 b,?_⟩
    intro R hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    have hrl := (hdata R hR1).1
    linarith [(le_max_right 1 b).trans hR]
  have hD := RiemannQuarticDenominatorLimit.denominator_locally_uniform_along t hreal r hr
  have hmul : TendstoLocallyUniformly (fun R z => denominatorProduct t (r R) hreal z *
      (flow t 0*(inverseZeroProduct t (r R) z/inverseZeroProduct t (r R) 0)))
      (flow t) atTop := by
    have hh := hD.mul₀ hscale continuous_const (flow_differentiable t).continuous
    have he : (fun _ : ℂ => (1 : ℂ)) * flow t = flow t := by
      funext z
      simp
    rw [he] at hh
    exact hh
  let Q : ℝ → ℝ[X] := fun R => C (RiemannQuarticReality.realFlow t 0)*numeratorPoly t (r R) hreal
  have hQsplit (R : ℝ) : (Q R).Splits :=
    (numeratorPoly_splits t (r R) hreal).C_mul _
  have hQeq (R : ℝ) (hR : 1 ≤ R) (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (r R)) :
      ((Q R).map (algebraMap ℝ ℂ)).eval z = denominatorProduct t (r R) hreal z *
        (flow t 0*(inverseZeroProduct t (r R) z/inverseZeroProduct t (r R) 0)) := by
    have hrp : 0 < r R := by linarith [(hdata R hR).1]
    have hc : (RiemannQuarticReality.realFlow t 0 : ℂ) = flow t 0 := by
      simpa only [Complex.ofReal_zero] using (RiemannQuarticReality.flow_real t 0).symm
    dsimp [Q]
    rw [Polynomial.map_mul,Polynomial.map_C,eval_mul,eval_C,
      numerator_reconstruction t (r R) hrp hreal z hz,Complex.coe_algebraMap,hc]
    ring
  have hQ : TendstoLocallyUniformly
      (fun R z => ((Q R).map (algebraMap ℝ ℂ)).eval z) (flow t) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨ρ,hρ,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    apply (tendstoLocallyUniformly_iff_forall_isCompact.mp hmul K hK).congr
    filter_upwards [eventually_ge_atTop (max 1 (ρ+1))] with R hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    intro z hz
    have hzr : z ∈ closedBall (0 : ℂ) (r R) := mem_closedBall_zero_iff.mpr (by
      have hn := mem_closedBall_zero_iff.mp (hsub hz)
      linarith [(hdata R hR1).1,(le_max_right 1 (ρ+1)).trans hR])
    exact (hQeq R hR1 z hzr).symm
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  refine ⟨fun n => Q ((n : ℝ)+1),fun n => hQsplit _,?_⟩
  apply tendstoLocallyUniformlyOn_univ.mpr
  intro u hu x
  obtain ⟨s,hs,hsmall⟩ := hQ u hu x
  exact ⟨s,hs,hnat.eventually hsmall⟩

theorem eventually_actual_polynomial_limit :
    ∀ᶠ t : ℝ in atTop, ∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
      TendstoLocallyUniformlyOn
        (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow t) atTop univ := by
  filter_upwards [RiemannQuarticUniformFarScale.eventually_all_zeros_real] with t hreal
  exact actual_polynomial_limit_of_real_zeros t hreal

theorem actual_start_set_nonempty : polynomialLimitStarts.Nonempty := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp eventually_actual_polynomial_limit
  exact ⟨T,hT⟩

theorem actual_start_infimum_strictly_above_eight : 8 < sInf polynomialLimitStarts :=
  strict_infimum_lower_bound_of_nonempty actual_start_set_nonempty

theorem actual_time_eight_has_nonreal_zero :
    ∃ z : ℂ, flow 8 z = 0 ∧ z.im ≠ 0 := by
  by_contra h
  have hr : ∀ z : ℂ, flow 8 z = 0 → z.im = 0 := by
    intro z hz
    by_contra him
    exact h ⟨z,hz,him⟩
  exact RiemannQuarticPolynomialLimitObstruction.actual_time_eight_not_polynomial_limit
    (actual_polynomial_limit_of_real_zeros 8 hr)

theorem actual_open_time_nonreal_zeros :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t-8| < δ → ∃ z : ℂ, flow t z = 0 ∧ z.im ≠ 0 := by
  obtain ⟨δ,hδ,hbad⟩ := exists_open_time_no_polynomial_limit
  refine ⟨δ,hδ,?_⟩
  intro t ht
  by_contra h
  have hr : ∀ z : ℂ, flow t z = 0 → z.im = 0 := by
    intro z hz
    by_contra him
    exact h ⟨z,hz,him⟩
  exact hbad t ht (actual_polynomial_limit_of_real_zeros t hr)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticActualPolynomialLimit
