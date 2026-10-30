import Foundation.PeriodicSpatialHolonomy
import Foundation.PeriodicGroundMass

/-! A robust joint holonomy second-moment test on actual periodic fields.
Centering and time-Dirichlet estimates are separate obligations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicHolonomyMass
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicSpatialHolonomy
open PeriodicWilsonSlab PeriodicSlabGround SU2HolonomyTraceObstruction

def score (v : SpatialVertex) (i j : Fin 3) (U : State) : ℝ :=
  jointSquare (winding U v i) (winding U v j)

theorem score_nonnegative (v : SpatialVertex) (i j : Fin 3) (U : State) :
    0 ≤ score v i j U := by unfold score jointSquare; positivity

theorem score_gauge (a : Gauge) (v : SpatialVertex) (i j : Fin 3) (U : State) :
    score v i j (PeriodicSlabGauge.gaugeAction a U)=score v i j U := by
  unfold score jointSquare
  rw [trace_gauge,trace_gauge,product_trace_gauge]

private theorem winding_continuous (v : SpatialVertex) (i : Fin 3) :
    Continuous (fun U : State => winding U v i) := by unfold winding; fun_prop

theorem score_continuous (v : SpatialVertex) (i j : Fin 3) : Continuous (score v i j) := by
  unfold score jointSquare
  exact (((PeriodicLowActionBlock.trace_continuous.comp (winding_continuous v i)).pow 2).add
    ((PeriodicLowActionBlock.trace_continuous.comp (winding_continuous v j)).pow 2)).add
    ((PeriodicLowActionBlock.trace_continuous.comp
      ((winding_continuous v i).mul (winding_continuous v j))).pow 2)

theorem robust_lower (v : SpatialVertex) (i j : Fin 3) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ U : State,spatialAction U < eta → (1/4 : ℝ) ≤ score v i j U := by
  let E : Set State := {U | score v i j U ≤ (1/4 : ℝ)}
  have hE : IsCompact E := (isClosed_le (score_continuous v i j) continuous_const).isCompact
  by_cases hn : E.Nonempty
  · obtain ⟨U,hU,hmin⟩ := hE.exists_isMinOn hn PeriodicLowActionBlock.spatial_continuous.continuousOn
    have hp : 0 < spatialAction U := by
      have hz := (spatial_action_bounds U).1
      by_contra h
      have he : spatialAction U=0 := le_antisymm (le_of_not_gt h) hz
      have hl := action_zero_joint_lower U he v i j
      change score v i j U ≤ (1/4 : ℝ) at hU
      change (1/2 : ℝ) ≤ score v i j U at hl
      linarith
    refine ⟨spatialAction U,hp,?_⟩
    intro V hv
    by_contra hs
    have hm := hmin (show V∈E from (lt_of_not_ge hs).le)
    exact (not_le_of_gt hv) hm
  · refine ⟨1,zero_lt_one,?_⟩
    intro U _
    by_contra hs
    exact hn ⟨U,(lt_of_not_ge hs).le⟩

theorem score_bound (v : SpatialVertex) (i j : Fin 3) (U : State) :
    |score v i j U| ≤ 3 := by
  rw [abs_of_nonneg (score_nonnegative v i j U)]
  have ha := abs_le.mp (halfTrace_bound (winding U v i))
  have hb := abs_le.mp (halfTrace_bound (winding U v j))
  have hc := abs_le.mp (halfTrace_bound (winding U v i*winding U v j))
  unfold score jointSquare
  nlinarith

theorem score_small_tail_tendsto_zero (v : SpatialVertex) (i j : Fin 3) :
    Tendsto (fun beta : ℝ => (ground beta).stationary.real
      {U | score v i j U < (1/4 : ℝ)}) atTop (𝓝 0) := by
  obtain ⟨eta,he,hb⟩ := robust_lower v i j
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_
    (PeriodicGroundMass.action_tail_tendsto_zero eta he)
  apply Eventually.of_forall
  intro beta
  letI : IsProbabilityMeasure (ground beta).stationary := (ground beta).stationary_probability
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro U hu
  change eta ≤ spatialAction U
  by_contra hs
  have h := hb U (lt_of_not_ge hs)
  exact (not_le_of_gt hu) h

theorem moment_lower_from_tail {beta : ℝ} (g : GroundData beta)
    (v : SpatialVertex) (i j : Fin 3) (eta : ℝ)
    (hb : ∀ U : State,spatialAction U < eta → (1/4 : ℝ) ≤ score v i j U) :
    (1/4 : ℝ)*(1-g.stationary.real {U | eta ≤ spatialAction U}) ≤
      ∫ U,score v i j U ∂g.stationary := by
  letI : IsProbabilityMeasure g.stationary := g.stationary_probability
  let T : Set State := {U | eta ≤ spatialAction U}
  have hT : MeasurableSet T := measurableSet_le measurable_const spatial_action_measurable
  have hi : Integrable (score v i j) g.stationary :=
    Integrable.of_bound (score_continuous v i j).measurable.aestronglyMeasurable 3
      (ae_of_all _ (score_bound v i j))
  have hind : Integrable (T.indicator (fun _ => (1 : ℝ))) g.stationary :=
    (integrable_const 1).indicator hT
  have hp (U : State) : (1/4 : ℝ)-(1/4 : ℝ)*T.indicator (fun _ => (1 : ℝ)) U ≤ score v i j U := by
    by_cases hu : U∈T
    · simpa only [Set.indicator_of_mem hu, mul_one,sub_self] using score_nonnegative v i j U
    · have he : spatialAction U < eta := lt_of_not_ge hu
      simpa only [Set.indicator_of_notMem hu,mul_zero,sub_zero] using hb U he
  have hm := integral_mono ((integrable_const (1/4 : ℝ)).sub (hind.const_mul (1/4))) hi hp
  simp only [Pi.sub_apply] at hm
  have hti : (∫ U,T.indicator (fun _ => (1 : ℝ)) U ∂g.stationary)=g.stationary.real T :=
    integral_indicator_one hT
  rw [integral_sub (integrable_const _) (hind.const_mul _),integral_const_mul,hti] at hm
  simpa only [integral_const,probReal_univ,one_smul,T,mul_sub,mul_one] using hm

theorem eventual_moment_lower (v : SpatialVertex) (i j : Fin 3) :
    ∀ᶠ beta : ℝ in atTop,∀ g : GroundData beta,
      (1/8 : ℝ) ≤ ∫ U,score v i j U ∂g.stationary := by
  obtain ⟨eta,he,hb⟩ := robust_lower v i j
  obtain ⟨C,hC,htail⟩ := PeriodicGroundMass.action_tail_exponential eta he
  have ht : Tendsto (fun beta : ℝ => C*Real.exp (-beta*eta/2)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp
      (Filter.tendsto_id.const_mul_atTop_of_neg (by linarith : -eta/2 < 0))).const_mul C
    have hx : (fun beta : ℝ => C*Real.exp (-beta*eta/2))=
        (fun beta : ℝ => C*Real.exp ((-eta/2)*beta)) := by
      funext beta
      congr 2 <;> ring
    rw [hx]
    simpa only [Function.comp_apply,id_eq,mul_zero] using h
  filter_upwards [eventually_ge_atTop (0 : ℝ),ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))]
    with beta hbeta hsmall
  intro g
  have h := htail beta hbeta g
  have hm := moment_lower_from_tail g v i j eta hb
  linarith

theorem eventual_nonvanishing_channel (v : SpatialVertex) (i j : Fin 3) :
    ∀ᶠ beta : ℝ in atTop,∀ g : GroundData beta,
      (1/24 : ℝ) ≤ (∫ U,halfTrace (winding U v i)^2 ∂g.stationary) ∨
      (1/24 : ℝ) ≤ (∫ U,halfTrace (winding U v j)^2 ∂g.stationary) ∨
      (1/24 : ℝ) ≤ (∫ U,halfTrace (winding U v i*winding U v j)^2 ∂g.stationary) := by
  filter_upwards [eventual_moment_lower v i j] with beta hb
  intro g
  letI : IsProbabilityMeasure g.stationary := g.stationary_probability
  have hi (F : State → SU2) (hc : Continuous F) :
      Integrable (fun U => halfTrace (F U)^2) g.stationary := by
    apply Integrable.of_bound ((PeriodicLowActionBlock.trace_continuous.comp hc).pow 2).measurable.aestronglyMeasurable 1
    filter_upwards with U
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    change halfTrace (F U)^2 ≤ 1
    have h := abs_le.mp (halfTrace_bound (F U))
    nlinarith
  have ha := hi (fun U => winding U v i) (winding_continuous v i)
  have hb' := hi (fun U => winding U v j) (winding_continuous v j)
  have hc := hi (fun U => winding U v i*winding U v j)
    ((winding_continuous v i).mul (winding_continuous v j))
  have hm := hb g
  unfold score jointSquare at hm
  have hab := integral_add ha hb'
  have habc := integral_add (ha.add hb') hc
  simp only [Pi.add_apply] at hab habc
  rw [habc,hab] at hm
  by_contra h
  push_neg at h
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicHolonomyMass
