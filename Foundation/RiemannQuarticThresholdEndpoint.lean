import Foundation.RiemannQuarticTimeCompact
import Foundation.RiemannQuarticActualPolynomialLimit

/-! Attainment of the literal eventual split-polynomial threshold. This
uses an explicit diagonal polynomial approximation, not a zero-limit assertion. -/
noncomputable section
open Set Filter Metric Complex Polynomial
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticThresholdEndpoint
open RiemannQuarticFlow RiemannQuarticOpenObstruction RiemannQuarticActualPolynomialLimit

theorem polynomial_limit_of_time_sequence (s : ℕ → ℝ) (t : ℝ)
    (hs : Tendsto s atTop (𝓝 t))
    (hP : ∀ n, ∃ P : ℕ → ℝ[X], (∀ j, (P j).Splits) ∧
      TendstoLocallyUniformlyOn
        (fun j z => ((P j).map (algebraMap ℝ ℂ)).eval z) (flow (s n)) atTop univ) :
    ∃ Q : ℕ → ℝ[X], (∀ n, (Q n).Splits) ∧
      TendstoLocallyUniformlyOn
        (fun n z => ((Q n).map (algebraMap ℝ ℂ)).eval z) (flow t) atTop univ := by
  have hchoose (n : ℕ) : ∃ q : ℝ[X], q.Splits ∧
      ∀ z ∈ closedBall (0 : ℂ) (n : ℝ),
        dist (flow (s n) z) ((q.map (algebraMap ℝ ℂ)).eval z) < 1/((n : ℝ)+1) := by
    obtain ⟨P,hPs,hlim⟩ := hP n
    have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hlim
      (closedBall (0 : ℂ) (n : ℝ)) (subset_univ _) (isCompact_closedBall ..)
    have he := (Metric.tendstoUniformlyOn_iff.mp hu) (1/((n : ℝ)+1)) (by positivity)
    obtain ⟨j,hj⟩ := he.exists
    exact ⟨P j,hPs j,hj⟩
  choose Q hQs hQ using hchoose
  refine ⟨Q,hQs,tendstoLocallyUniformlyOn_univ.mpr ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R,hR,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  have htime : TendstoUniformlyOn (fun n z => flow (s n) z) (flow t) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact hs.eventually (Metric.tendstoUniformlyOn_iff.mp
      (RiemannQuarticTimeCompact.flow_time_tendsto_uniformly_on t K hK) ε hε)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hinv : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcast : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)
  filter_upwards [hcast,hinv.eventually (gt_mem_nhds (half_pos hε)),
    (Metric.tendstoUniformlyOn_iff.mp htime) (ε/2) (half_pos hε)] with n hn hi ht
  intro z hz
  have hzn : z ∈ closedBall (0 : ℂ) (n : ℝ) :=
    (closedBall_subset_closedBall hn) (hsub hz)
  exact (dist_triangle _ (flow (s n) z) _).trans_lt
    (by linarith [ht z hz,(hQ n z hzn).trans hi])

theorem polynomial_limit_above_infimum (t : ℝ)
    (ht : sInf polynomialLimitStarts < t) :
    ∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
      TendstoLocallyUniformlyOn
        (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow t) atTop univ := by
  obtain ⟨T,hT,hTt⟩ := exists_lt_of_csInf_lt actual_start_set_nonempty ht
  exact hT t hTt.le

theorem polynomial_limit_at_infimum :
    ∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
      TendstoLocallyUniformlyOn
        (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z)
        (flow (sInf polynomialLimitStarts)) atTop univ := by
  apply polynomial_limit_of_time_sequence
    (fun n => sInf polynomialLimitStarts+1/((n : ℝ)+1))
    (sInf polynomialLimitStarts)
  · simpa using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro n
    apply polynomial_limit_above_infimum
    have hp : 0 < 1/((n : ℝ)+1) := by positivity
    linarith

theorem infimum_mem_actual_starts : sInf polynomialLimitStarts ∈ polynomialLimitStarts := by
  intro t ht
  rcases eq_or_lt_of_le ht with he | he
  · rw [← he]
    exact polynomial_limit_at_infimum
  · exact polynomial_limit_above_infimum t he

theorem actual_starts_eq_Ici_infimum :
    polynomialLimitStarts = Ici (sInf polynomialLimitStarts) := by
  have hb : BddBelow polynomialLimitStarts := by
    obtain ⟨ε,hε,hbound⟩ := eventual_polynomial_limit_start_strictly_above_eight
    exact ⟨8+ε,fun T hT => (hbound T hT).le⟩
  ext T
  constructor
  · intro hT
    exact csInf_le hb hT
  · intro hT t ht
    exact infimum_mem_actual_starts t (hT.trans ht)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticThresholdEndpoint
