import Foundation.SU2TransverseHaarLower
import Foundation.PeriodicNoncentralHaarUpper
import Foundation.PeriodicQuarticKernelBlock
/-! Positive actual full-Haar lower blocks at common-axis flat backgrounds.
A quadratic-mass root tube and all63 relative caps yield a191-power lower
bound for arbitrary nonconstant boundary velocities. Combining the prior
noncentral upper bound gives two-sided191-power control, without an exact
coefficient, stationary normalization or physical mass-gap conclusion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Quaternion Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicNoncentralHaarLower
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereJets
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge PeriodicGaugeSaturatedGround
open PeriodicLoopVariation PeriodicQuarticGaugeOverlap PeriodicQuarticKernelBlock
open PeriodicFlatBackgroundHessian
open PeriodicChargedFourier (background background_commutes)
open PeriodicAnchoredHaarLimit (base)
open PeriodicRootedHaarControl (chartState budget budget_nonneg)

private theorem root_displacement (α : Fin 3 → ℝ) (r : ℝ) (hr : 0≤r) (c : SU2)
    (hc : c∈SU2TransverseHaarLower.tube (r/3)) (e : SpatialEdge) :
    distance (c*base (background α) e*c⁻¹) (base (background α) e)≤r := by
  change SU2TwoAxisStabilizerHaar.turn 0 (α e.2) c≤r
  have hh := SU2TwoAxisStabilizerHaar.turn_zero_square (α e.2) c
  change SU2TwoAxisStabilizerHaar.turn 0 (α e.2) c^2=
    4*Real.sin (α e.2)^2*SU2TransverseHaar.transverse c at hh
  have hq : SU2TransverseHaar.transverse c≤2*(r/3)^2 := hc
  have hs : Real.sin (α e.2)^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq (α e.2),sq_nonneg (Real.cos (α e.2))]
  have hm := mul_le_mul_of_nonneg_right hs (SU2TransverseHaar.transverse_nonneg c)
  simp only [one_mul] at hm
  nlinarith [SU2TwoAxisStabilizerHaar.turn_nonneg 0 (α e.2) c]

private theorem aligned_distance (α : Fin 3 → ℝ) (U V : State) (r : ℝ) (hr : 0≤r)
    (hU : U∈packet (base (background α)) r) (hV : V∈packet (base (background α)) r)
    (c : SU2) (hc : c∈SU2TransverseHaarLower.tube (r/3))
    (h : RelField) (hh : h∈relBox (r/3)) (e : SpatialEdge) :
    distance (U e) (gaugeAction (assemble c h) V e)≤5*r := by
  let C := base (background α)
  let a := assemble c h
  have hcenter : distance (gaugeAction a C e) (C e)≤3*r := by
    have h1 := assembled_center_distance C c h r (anchored_close r hr h hh) e
    have h2 := root_displacement α r hr c hc e
    linarith [distance_triangle (gaugeAction a C e) (c*C e*c⁻¹) (C e)]
  have hcov : distance (gaugeAction a C e) (gaugeAction a V e)≤r := by
    rw [framed_distance,distance_symm]
    exact hV e
  have hrcenter : distance (C e) (gaugeAction a C e)≤3*r := by rw [distance_symm]; exact hcenter
  have hu : distance (U e) (C e)≤r := hU e
  change distance (U e) (gaugeAction a V e)≤_
  linarith [distance_triangle (U e) (C e) (gaugeAction a V e),
    distance_triangle (C e) (gaugeAction a C e) (gaugeAction a V e)]

private theorem temporal_packet_bound (α : Fin 3 → ℝ) (U V : State) (r : ℝ) (hr : 0≤r)
    (hU : U∈packet (base (background α)) r) (hV : V∈packet (base (background α)) r)
    (c : SU2) (hc : c∈SU2TransverseHaarLower.tube (r/3))
    (h : RelField) (hh : h∈relBox (r/3)) : temporalAction U V (assemble c h)≤2400*r^2 := by
  have hp (e : SpatialEdge) : distance (U e) (gaugeAction (assemble c h) V e)^2≤25*r^2 := by
    have hd := aligned_distance α U V r hr hU hV c hc h hh e
    have hs := pow_le_pow_left₀ (show 0≤distance (U e) (gaugeAction (assemble c h) V e) from norm_nonneg _) hd 2
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hp e)
  rw [Finset.sum_const,Finset.card_univ,edge_count,nsmul_eq_mul,
    PeriodicFlatLocusQuarticObstruction.temporal_distance_identity] at hs
  norm_num at hs
  nlinarith only [hs]

private theorem spatial_base (α : Fin 3 → ℝ) : spatialAction (base (background α))=0 := by
  have hh := spatial_base_zero (background α) (0 : Velocity) (background_commutes α)
  rw [state_zero] at hh
  exact hh

private theorem halfAction_packet_bound (α : Fin 3 → ℝ) (U V : State) (r : ℝ) (hr : 0≤r)
    (hU : U∈packet (base (background α)) r) (hV : V∈packet (base (background α)) r)
    (c : SU2) (hc : c∈SU2TransverseHaarLower.tube (r/3))
    (h : RelField) (hh : h∈relBox (r/3)) : halfAction U V (assemble c h)≤5472*r^2 := by
  have h1 := spatial_packet_upper U (base (background α)) r hU
  have h2 := spatial_packet_upper V (base (background α)) r hV
  rw [spatial_base α] at h1 h2
  have h3 := temporal_packet_bound α U V r hr hU hV c hc h hh
  unfold halfAction
  linarith

attribute [local irreducible] kernel PeriodicWilsonSlab.weight halfAction gaugeHaar boundaryHaar

theorem kernel_packet_lower (α : Fin 3 → ℝ) (β r : ℝ) (hb : 0≤β) (hr : 0≤r)
    (U V : State) (hU : U∈packet (base (background α)) r) (hV : V∈packet (base (background α)) r) :
    law.real (SU2TransverseHaarLower.tube (r/3))*(law.real (SU2HaarSmallCap.cap (r/3)))^63*
      Real.exp (-β*(5472*r^2))≤kernel β U V := by
  have hm : Measurable (PeriodicWilsonSlab.weight β U V) := PeriodicAnchoredHaarLimit.weight_measurable β U V
  have hi := assemble_preserving.integrable_comp_of_integrable (weight_integrable β U V)
  let S : Set (SU2 × RelField) := SU2TransverseHaarLower.tube (r/3) ×ˢ relBox (r/3)
  have hS : MeasurableSet S := (SU2TransverseHaarLower.tube_measurable _).prod (relBox_measurable _)
  have hp (p : SU2 × RelField) (hh : p∈S) :
      Real.exp (-β*(5472*r^2))≤PeriodicWilsonSlab.weight β U V (assemble p.1 p.2) := by
    have ha := halfAction_packet_bound α U V r hr hU hV p.1 hh.1 p.2 hh.2
    unfold PeriodicWilsonSlab.weight
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left ha hb
    linarith
  have hmass : (law.prod relFieldHaar).real S=
      law.real (SU2TransverseHaarLower.tube (r/3))*(law.real (SU2HaarSmallCap.cap (r/3)))^63 := by
    change ((law.prod relFieldHaar) (_ ×ˢ _)).toReal=_
    rw [Measure.prod_prod,ENNReal.toReal_mul]
    change _*relFieldHaar.real (relBox (r/3))=_
    rw [relBox_mass]
    rfl
  have hlow := setIntegral_mono_on (integrable_const (Real.exp (-β*(5472*r^2)))).integrableOn hi.integrableOn hS hp
  rw [setIntegral_const,smul_eq_mul,hmass] at hlow
  have hfull := setIntegral_le_integral (s := S) hi
    (ae_of_all _ (fun p => (Real.exp_pos _).le.trans (weight_bounds β U V (assemble p.1 p.2)).1))
  have he := integral_split (PeriodicWilsonSlab.weight β U V) hm
  unfold kernel
  exact hlow.trans (hfull.trans_eq he.symm)

theorem kernel_packet_power_lower (α : Fin 3 → ℝ) (β r : ℝ) (hb : 0≤β) (hr : 0≤r) (h1 : r≤1)
    (U V : State) (hU : U∈packet (base (background α)) r) (hV : V∈packet (base (background α)) r) :
    (1/(4*Real.pi^2))^64*(r/3)^191*Real.exp (-β*(5472*r^2))≤kernel β U V := by
  have hroot := SU2TransverseHaarLower.tube_mass_lower (r/3) (by positivity) (by linarith)
  have hcap := SU2HaarSmallCap.mass_lower (r/3) (by positivity) (by linarith)
  have hl0 : (0 : ℝ)≤(1/(4*Real.pi^2))*(r/3)^3 :=
    mul_nonneg (by positivity) (pow_nonneg (div_nonneg hr (by norm_num)) 3)
  have hp := pow_le_pow_left₀ hl0 hcap 63
  have hl := pow_nonneg hl0 63
  have hn : 0≤law.real (SU2TransverseHaarLower.tube (r/3)) := measureReal_nonneg
  have hm := mul_le_mul hroot hp hl hn
  have he := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-β*(5472*r^2))).le
  have hh := he.trans (kernel_packet_lower α β r hb hr U V hU hV)
  convert hh using 1 <;> ring


private def scale (X Y : Velocity) : ℝ := budget X Y+1
private theorem scale_pos (X Y : Velocity) : 0<scale X Y := by
  have hh := budget_nonneg X Y
  unfold scale
  linarith
private theorem scale_swap (X Y : Velocity) : scale Y X=scale X Y := by unfold scale budget; ring

private theorem term_le_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i,0≤f i) (i : ι) : f i≤∑ j,f j :=
  Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

private theorem size_le_budget (X Y : Velocity) (e : SpatialEdge) : sizeSq (X e)≤budget X Y := by
  have hh := term_le_sum (fun e : SpatialEdge => sizeSq (X e)) (fun _ => sizeSq_nonneg _) e
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun e _ => sizeSq_nonneg (Y e))
  unfold budget
  linarith

private theorem chart_packet (H : State) (X Y : Velocity) (t : ℝ) :
    chartState H X t∈packet H (scale X Y*|t|) := by
  intro e
  have hd : distance (chartState H X t e) (H e)=distance (hemisphereChart (t • X e)) 1 := by
    change distance (hemisphereChart (t • X e)*H e) (H e)=_
    simpa only [one_mul] using SU2TwoAxisStabilizerHaar.right_distance_isometry (hemisphereChart (t • X e)) 1 (H e)
  rw [hd]
  have he := distance_sq (hemisphereChart (t • X e)) 1
  simp only [inv_one,mul_one] at he
  have hc := PeriodicRelativeGaugeTails.chart_scaled_cost (X e) t
  have hb := size_le_budget X Y e
  have hB := budget_nonneg X Y
  have hM : 2*budget X Y≤scale X Y^2 := by unfold scale; nlinarith [sq_nonneg (budget X Y)]
  have hp := mul_le_mul_of_nonneg_left hb (sq_nonneg t)
  have hm := mul_le_mul_of_nonneg_left hM (sq_nonneg t)
  have hr : 0≤scale X Y*|t| := mul_nonneg (scale_pos X Y).le (abs_nonneg _)
  apply (sq_le_sq₀ (show 0≤distance (hemisphereChart (t • X e)) 1 from norm_nonneg _) hr).mp
  rw [mul_pow,sq_abs]
  nlinarith

def lowerConstant (X Y : Velocity) : ℝ :=
  (1/(4*Real.pi^2))^64*(scale X Y/3)^191*Real.exp (-5472*scale X Y^2)

theorem lowerConstant_pos (X Y : Velocity) : 0<lowerConstant X Y := by
  have hh := scale_pos X Y
  unfold lowerConstant
  positivity

theorem scaled_kernel_lower (α : Fin 3 → ℝ) (X Y : Velocity) (t : ℝ) (ht : t≠0)
    (hsmall : (budget X Y+1)*|t|≤1) :
    lowerConstant X Y*|t|^191≤kernel (1/t^2) (chartState (base (background α)) X t)
      (chartState (base (background α)) Y t) := by
  have hU := chart_packet (base (background α)) X Y t
  have hV := chart_packet (base (background α)) Y X t
  rw [scale_swap] at hV
  have hh := kernel_packet_power_lower α (1/t^2) (scale X Y*|t|) (by positivity)
    (mul_nonneg (scale_pos X Y).le (abs_nonneg _)) hsmall _ _ hU hV
  have he : -(1/t^2)*(5472*(scale X Y*|t|)^2)= -5472*scale X Y^2 := by
    rw [mul_pow,sq_abs]
    field_simp [ht]
  rw [he] at hh
  unfold lowerConstant
  convert hh using 1 <;> ring

/-- Positive actual full64-variable Haar lower bound at ALL common-axis
backgrounds. Noncentral winding is needed only for the matching upper bound. -/
theorem commonAxis_eventual_lower (α : Fin 3 → ℝ) (X Y : Velocity) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,lowerConstant X Y*|t|^191≤kernel (1/t^2)
      (chartState (base (background α)) X t) (chartState (base (background α)) Y t) := by
  have hc : Continuous (fun t : ℝ => scale X Y*|t|) := continuous_const.mul continuous_abs
  have hl : Tendsto (fun t : ℝ => scale X Y*|t|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero,mul_zero] using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ)≤𝓝 0)
  filter_upwards [self_mem_nhdsWithin,hl.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))] with t ht hr
  exact scaled_kernel_lower α X Y t ht hr.le

/-- Exact two-sided191-POWER control, without an asserted asymptotic coefficient. -/
theorem commonAxis_two_sided (α : Fin 3 → ℝ) (X Y : Velocity) (i : Fin 3) (hi : Real.sin (4*α i)≠0) :
    0<lowerConstant X Y ∧ 0<PeriodicNoncentralHaarUpper.upperConstant X Y (4*α i) ∧
      ∀ᶠ t : ℝ in 𝓝[≠] 0,
        lowerConstant X Y*|t|^191≤kernel (1/t^2) (chartState (base (background α)) X t)
          (chartState (base (background α)) Y t) ∧
        kernel (1/t^2) (chartState (base (background α)) X t) (chartState (base (background α)) Y t)≤
          PeriodicNoncentralHaarUpper.upperConstant X Y (4*α i)*|t|^191 :=
  ⟨lowerConstant_pos X Y,PeriodicNoncentralHaarUpper.upperConstant_pos X Y (4*α i),
    (commonAxis_eventual_lower α X Y).and (PeriodicNoncentralHaarUpper.commonAxis_eventual_power_bound α X Y i hi)⟩

end OperatorDerivativeRewrite.Foundation.PeriodicNoncentralHaarLower
