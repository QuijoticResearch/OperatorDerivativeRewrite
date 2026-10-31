import Foundation.PeriodicQuarticCurvature
/-! The periodic quartic family is genuinely far from the ENTIRE flat locus.
A commuting-pair quaternion minor gives an orthogonal-axis distance bound.
Actual winding-loop variation then bounds every flat-field gauge-alignment
cost below at quadratic parameter scale, while spatial action is quartic.
Thus no uniform quadratic flat-recovery estimate holds, even allowing all flat
holonomies and gauge transformations. No native spectral quasimode or ground
concentration is constructed from this pointwise geometric obstruction. -/

noncomputable section
open scoped Quaternion Topology
open Filter MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
namespace OperatorDerivativeRewrite.Foundation.PeriodicFlatLocusQuarticObstruction
open QuaternionSU2Representation SU2JointPlaquetteCubic PeriodicLoopVariation
open PeriodicTemporalSlab PeriodicSpatialHolonomy PeriodicWilsonSlab
attribute [local irreducible] boundaryHaar gaugeHaar kernel spatialAction temporalAction FourCubePinnedCoercivity.defect

private theorem lift_mul (A B : SU2) : lift (A*B)=lift A*lift B :=
  congrArg (fun u : QuaternionAngularHaar.Group => (u : ℍ)) (equiv.symm.map_mul A B)

private theorem lift_axis (i : Fin 3) (r : ℝ) : lift (axis i r)=axisRaw i r := by
  unfold axis lift
  change ((equiv.symm (equiv _) : QuaternionAngularHaar.Group) : ℍ)=_
  rw [equiv.symm_apply_apply]

theorem commuting_minor (A B : SU2) (hc : A*B=B*A) :
    (lift A).imI*(lift B).imJ-(lift A).imJ*(lift B).imI=0 := by
  have h := congrArg (fun X : SU2 => (lift X).imK) hc
  rw [lift_mul,lift_mul] at h
  simp only [Quaternion.imK_mul] at h
  nlinarith

private theorem axis0_distance (r : ℝ) (A : SU2) :
    distance (axis 0 r) A^2=(Real.cos r-(lift A).re)^2+(Real.sin r-(lift A).imI)^2+
      (lift A).imJ^2+(lift A).imK^2 := by
  unfold distance
  rw [pow_two,← Quaternion.normSq_eq_norm_mul_self,lift_axis]
  norm_num [axisRaw,Quaternion.normSq_def',Quaternion.re_sub,Quaternion.imI_sub,
    Quaternion.imJ_sub,Quaternion.imK_sub]

private theorem axis1_distance (r : ℝ) (B : SU2) :
    distance (axis 1 r) B^2=(Real.cos r-(lift B).re)^2+(lift B).imI^2+
      (Real.sin r-(lift B).imJ)^2+(lift B).imK^2 := by
  unfold distance
  rw [pow_two,← Quaternion.normSq_eq_norm_mul_self,lift_axis]
  norm_num [axisRaw,Quaternion.normSq_def',Quaternion.re_sub,Quaternion.imI_sub,
    Quaternion.imJ_sub,Quaternion.imK_sub]

theorem commuting_axes_distance (r : ℝ) (A B : SU2) (hc : A*B=B*A) :
    Real.sin r^2≤distance (axis 0 r) A^2+distance (axis 1 r) B^2 := by
  have h := commuting_minor A B hc
  rw [axis0_distance,axis1_distance]
  nlinarith [sq_nonneg ((lift A).imI+(lift B).imJ-Real.sin r),
    sq_nonneg ((lift A).imJ-(lift B).imI),sq_nonneg (Real.cos r-(lift A).re),
    sq_nonneg (Real.cos r-(lift B).re),sq_nonneg (lift A).imK,sq_nonneg (lift B).imK]

private theorem axis_add (i : Fin 3) (r s : ℝ) : axis i r*axis i s=axis i (r+s) := by
  unfold axis
  rw [← hom.map_mul]
  apply congrArg hom
  apply Subtype.ext
  change axisRaw i r*axisRaw i s=axisRaw i (r+s)
  fin_cases i <;> ext <;>
    norm_num [axisRaw,Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,
      Real.cos_add,Real.sin_add] <;> ring

private theorem axis_four (i : Fin 3) (t : ℝ) :
    axis i t*axis i t*axis i t*axis i t=axis i (4*t) := by
  rw [axis_add,axis_add,axis_add]
  apply congrArg (axis i)
  ring

theorem winding_field_zero (t : ℝ) (v : SpatialVertex) :
    winding (PeriodicQuarticCurvature.field t) v 0=axis 0 (4*t) := by
  change axis 0 t*axis 0 t*axis 0 t*axis 0 t=_
  exact axis_four 0 t

theorem winding_field_one (t : ℝ) (v : SpatialVertex) :
    winding (PeriodicQuarticCurvature.field t) v 1=axis 1 (4*t) := by
  change axis 1 t*axis 1 t*axis 1 t*axis 1 t=_
  exact axis_four 1 t


theorem winding_square_temporal (U V : State) (a : PeriodicTemporalSlab.Gauge) (v : SpatialVertex) (i : Fin 3) :
    distance (winding U v i) (winding (PeriodicSlabGauge.gaugeAction a V) v i)^2≤32*temporalAction U V a := by
  have hd := winding_distance U V a v i
  have hs := Real.sq_sqrt (show 0≤2*temporalAction U V a by linarith [(temporal_action_bounds U V a).1])
  have h := pow_le_pow_left₀ (show 0≤distance (winding U v i) (winding (PeriodicSlabGauge.gaugeAction a V) v i) from norm_nonneg _) hd 2
  nlinarith

theorem temporal_distance_identity (U V : State) (a : PeriodicTemporalSlab.Gauge) :
    (∑ e : SpatialEdge,distance (U e) (PeriodicSlabGauge.gaugeAction a V e)^2)=2*temporalAction U V a := by
  simp_rw [distance_sq,← PeriodicTemporalConcentration.temporal_word_alignment]
  unfold temporalAction
  rw [Finset.mul_sum]
  unfold FourCubePinnedCoercivity.defect
  rfl
theorem flat_separation (t : ℝ) (V : State) (hV : spatialAction V=0) (a : PeriodicTemporalSlab.Gauge) (v : SpatialVertex) :
    Real.sin (4*t)^2≤64*temporalAction (PeriodicQuarticCurvature.field t) V a := by
  have hz : spatialAction (PeriodicSlabGauge.gaugeAction a V)=0 :=
    (PeriodicSlabGauge.spatial_action_invariant a V).trans hV
  have hc := flat_commute (PeriodicSlabGauge.gaugeAction a V)
    (action_zero_flat _ hz) v 0 1
  have h := commuting_axes_distance (4*t)
    (winding (PeriodicSlabGauge.gaugeAction a V) v 0)
    (winding (PeriodicSlabGauge.gaugeAction a V) v 1) hc
  rw [← winding_field_zero t v,← winding_field_one t v] at h
  have h0 := winding_square_temporal (PeriodicQuarticCurvature.field t) V a v 0
  have h1 := winding_square_temporal (PeriodicQuarticCurvature.field t) V a v 1
  linarith

private theorem sin_sinc (x : ℝ) : Real.sin x=x*Real.sinc x := by
  by_cases hx : x=0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

theorem eventually_sine_floor : ∀ᶠ t : ℝ in 𝓝 0,t^2≤Real.sin (4*t)^2 := by
  have hs : Tendsto (fun t : ℝ => Real.sinc (4*t)) (𝓝 0) (𝓝 (1 : ℝ)) := by
    have hm : Tendsto (fun t : ℝ => 4*t) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).const_mul 4
    simpa only [Function.comp_def,Real.sinc_zero] using (Real.continuous_sinc.tendsto (0 : ℝ)).comp hm
  filter_upwards [hs.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1))] with t ht
  change (1/2 : ℝ)<Real.sinc (4*t) at ht
  have hsq : (1/4 : ℝ)≤Real.sinc (4*t)^2 := by nlinarith [sq_nonneg (Real.sinc (4*t)-1/2)]
  have hm := mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg t)
  rw [sin_sinc]
  nlinarith [sq_nonneg t]

theorem eventual_flat_distance_floor : ∀ᶠ t : ℝ in 𝓝 0,∀ V : State,spatialAction V=0 →
    ∀ a : PeriodicTemporalSlab.Gauge,t^2≤64*temporalAction (PeriodicQuarticCurvature.field t) V a := by
  filter_upwards [eventually_sine_floor] with t ht
  intro V hV a
  exact ht.trans (flat_separation t V hV a (fun _ => 0))

theorem eventual_no_flat_recovery (C : ℝ) (hC : 0<C) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ V : State,spatialAction V=0 → ∀ a : PeriodicTemporalSlab.Gauge,
      C*spatialAction (PeriodicQuarticCurvature.field t)<temporalAction (PeriodicQuarticCurvature.field t) V a := by
  have hc : 0<(1/(64*C) : ℝ) := by positivity
  filter_upwards [PeriodicQuarticCurvature.eventual_subquadratic (1/(64*C)) hc,
    eventual_flat_distance_floor.filter_mono nhdsWithin_le_nhds] with t hS hD
  intro V hV a
  have hkin := hD V hV a
  have hscaled := mul_lt_mul_of_pos_left hS hC
  have he : C*((1/(64*C))*t^2)=t^2/64 := by field_simp [hC.ne']
  rw [he] at hscaled
  linarith

theorem no_uniform_flat_recovery :
    ¬ ∃ C : ℝ,0<C ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0,∃ V : State,∃ a : PeriodicTemporalSlab.Gauge,
      spatialAction V=0 ∧ temporalAction (PeriodicQuarticCurvature.field t) V a≤C*spatialAction (PeriodicQuarticCurvature.field t) := by
  rintro ⟨C,hC,h⟩
  obtain ⟨t,ht,hs⟩ := ((eventual_no_flat_recovery C hC).and h).exists
  obtain ⟨V,a,hV,ha⟩ := hs
  exact (not_le_of_gt (ht V hV a)) ha

end OperatorDerivativeRewrite.Foundation.PeriodicFlatLocusQuarticObstruction
