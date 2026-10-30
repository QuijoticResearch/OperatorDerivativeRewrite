import Foundation.PeriodicGroundSeamParity

/-! Genuine centered holonomy trials under every actual periodic ground law.
Their variance does not collapse at large coupling. No time-energy bound is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicCenteredHolonomy
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicSpatialHolonomy
open PeriodicWilsonSlab PeriodicSlabGround PeriodicCenterSeam PeriodicGroundSeamParity

def origin : SpatialVertex := fun _ => 0

theorem winding_flip_same (i : Fin 3) (U : State) :
    winding (flip i U) origin i=SU2StapleExtremes.minusOne*winding U origin i := by
  have h0 : (0 : ZMod 4)≠3 := by decide
  have h1 : (1 : ZMod 4)≠3 := by decide
  have h2 : (2 : ZMod 4)≠3 := by decide
  norm_num [winding,PeriodicCenterSeam.flip,seam,origin,twice,thrice,shift,h0,h1,h2]
  simp only [center_commute]
  group

theorem winding_flip_other (i j : Fin 3) (hij : j≠i) (U : State) (v : SpatialVertex) :
    winding (flip i U) v j=winding U v j := by
  simp [winding,PeriodicCenterSeam.flip,seam,hij]

def first (U : State) : ℝ := halfTrace (winding U origin 0)
def second (U : State) : ℝ := halfTrace (winding U origin 1)
def mixed (U : State) : ℝ := halfTrace (winding U origin 0*winding U origin 1)

theorem first_odd (U : State) : first (flip 0 U)= -first U := by
  unfold first
  rw [winding_flip_same,SU2StrongCouplingCovariance.halfTrace_center_neg]

theorem second_odd (U : State) : second (flip 1 U)= -second U := by
  unfold second
  rw [winding_flip_same,SU2StrongCouplingCovariance.halfTrace_center_neg]

theorem mixed_odd (U : State) : mixed (flip 0 U)= -mixed U := by
  unfold mixed
  rw [winding_flip_same,winding_flip_other 0 1 (by decide),mul_assoc,
    SU2StrongCouplingCovariance.halfTrace_center_neg]

theorem flipped_identity_not_gauge :
    ¬ ∃ a : Gauge,PeriodicSlabGauge.gaugeAction a (1 : State)=flip 0 (1 : State) := by
  rintro ⟨a,ha⟩
  have h := congrArg first ha
  have hg : first (PeriodicSlabGauge.gaugeAction a (1 : State))=first 1 :=
    trace_gauge a 1 origin 0
  rw [hg,first_odd] at h
  have h1 : first (1 : State)=1 := by
    norm_num [first,winding,SU2OpenLinkGaugeObstruction.halfTrace_one]
  rw [h1] at h
  linarith

theorem first_measurable : Measurable first :=
  halfTrace_measurable.comp (by unfold winding; fun_prop)

theorem second_measurable : Measurable second :=
  halfTrace_measurable.comp (by unfold winding; fun_prop)

theorem mixed_measurable : Measurable mixed :=
  halfTrace_measurable.comp (by unfold winding; fun_prop)

variable {beta : ℝ} (g : GroundData beta)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability

theorem first_mean_zero : (∫ U,first U ∂g.stationary)=0 := odd_mean_zero g 0 first first_odd
theorem second_mean_zero : (∫ U,second U ∂g.stationary)=0 := odd_mean_zero g 1 second second_odd
theorem mixed_mean_zero : (∫ U,mixed U ∂g.stationary)=0 := odd_mean_zero g 0 mixed mixed_odd

private theorem bounded_memLp (f : State → ℝ) (hf : Measurable f) (hb : ∀ U,|f U| ≤ 1) :
    MemLp f 2 g.stationary :=
  MemLp.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using hb U))

theorem first_memLp : MemLp first 2 g.stationary :=
  bounded_memLp g first first_measurable (fun U => halfTrace_bound _)

theorem second_memLp : MemLp second 2 g.stationary :=
  bounded_memLp g second second_measurable (fun U => halfTrace_bound _)

theorem mixed_memLp : MemLp mixed 2 g.stationary :=
  bounded_memLp g mixed mixed_measurable (fun U => halfTrace_bound _)

theorem first_variance : variance first g.stationary=∫ U,first U^2 ∂g.stationary := by
  rw [variance_eq_sub (first_memLp g),first_mean_zero]
  norm_num

theorem second_variance : variance second g.stationary=∫ U,second U^2 ∂g.stationary := by
  rw [variance_eq_sub (second_memLp g),second_mean_zero]
  norm_num

theorem mixed_variance : variance mixed g.stationary=∫ U,mixed U^2 ∂g.stationary := by
  rw [variance_eq_sub (mixed_memLp g),mixed_mean_zero]
  norm_num

theorem joint_variance : variance first g.stationary+variance second g.stationary+
    variance mixed g.stationary=∫ U,PeriodicHolonomyMass.score origin 0 1 U ∂g.stationary := by
  rw [first_variance,second_variance,mixed_variance]
  have h1 := integral_add (first_memLp g).integrable_sq (second_memLp g).integrable_sq
  have h2 := integral_add ((first_memLp g).integrable_sq.add (second_memLp g).integrable_sq)
    (mixed_memLp g).integrable_sq
  simp only [Pi.add_apply] at h1 h2
  rw [← h1,← h2]
  rfl

theorem eventual_joint_variance : ∀ᶠ beta : ℝ in atTop,∀ g : GroundData beta,
    (1/8 : ℝ) ≤ variance first g.stationary+variance second g.stationary+variance mixed g.stationary := by
  filter_upwards [PeriodicHolonomyMass.eventual_moment_lower origin 0 1] with beta hb
  intro g
  rw [joint_variance]
  exact hb g

theorem eventual_variance_channel : ∀ᶠ beta : ℝ in atTop,∀ g : GroundData beta,
    (1/24 : ℝ) ≤ variance first g.stationary ∨ (1/24 : ℝ) ≤ variance second g.stationary ∨
      (1/24 : ℝ) ≤ variance mixed g.stationary := by
  filter_upwards [PeriodicHolonomyMass.eventual_nonvanishing_channel origin 0 1] with beta hb
  intro g
  rw [first_variance,second_variance,mixed_variance]
  exact hb g

end OperatorDerivativeRewrite.Foundation.PeriodicCenteredHolonomy
