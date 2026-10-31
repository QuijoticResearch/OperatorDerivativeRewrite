import Foundation.PeriodicRelativeGaugeGaussian
import Foundation.FourCubeHaarPartitionAsymptotic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! Actual periodic Wilson relative-gauge tail control with explicit fixed-cell
boundary budgets. The full product-Haar exterior is negligible at scale189;
inside a fixed physical cap the actual chart-ray weights have an integrable
Gaussian envelope. A global chart Gaussian bound is rigorously impossible.
These estimates do not yet identify the rescaled full Haar integral: exact
63-factor chart transport and its Jacobian remain separate obligations. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicRelativeGaugeTails
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open SU2HemisphereJets (sizeSq sizeSq_nonneg)
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicConstantQuarticJet PeriodicConstantRootLimit
open PeriodicGaugeSaturatedGround PeriodicRelativeGaugeGaussian FourCubePinnedCoercivity
attribute [local irreducible] temporalAction spatialAction halfAction weight sizeSq

def linkCost (U : State) : ℝ := ∑ e : SpatialEdge,defect (U e)

theorem edge_comparison (U V : State) (g : Gauge) (e : SpatialEdge) :
    defect (g (shift e.1 e.2)*(g e.1)⁻¹) ≤
      3*(defect (U e)+defect (temporalWord U V g e)+defect (V e)) := by
  have he : (U e)⁻¹*temporalWord U V g e*(g e.1*V e*(g e.1)⁻¹)=
      g (shift e.1 e.2)*(g e.1)⁻¹ := by unfold temporalWord; group
  have h := defect_triple (U e)⁻¹ (temporalWord U V g e) (g e.1*V e*(g e.1)⁻¹)
  rw [he,defect_inv] at h
  have hc : defect (g e.1*V e*(g e.1)⁻¹)=defect (V e) := by
    unfold defect
    rw [halfTrace_conjugate]
  rwa [hc] at h

theorem temporal_comparison (U V : State) (g : Gauge) :
    temporalAction (1 : State) 1 g ≤ 3*(linkCost U+temporalAction U V g+linkCost V) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun e _ => edge_comparison U V g e)
  have he (e : SpatialEdge) : temporalWord (1 : State) 1 g e=g (shift e.1 e.2)*(g e.1)⁻¹ := by
    simp [temporalWord]
  unfold temporalAction linkCost
  simpa only [he,defect,Finset.sum_add_distrib,← Finset.mul_sum] using h

def sourceBudget (a b : Velocities) : ℝ :=
  64*(∑ i : Fin 3,sizeSq (a i))+64*(∑ i : Fin 3,sizeSq (b i))

theorem sourceBudget_nonneg (a b : Velocities) : 0 ≤ sourceBudget a b := by
  unfold sourceBudget
  exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sizeSq_nonneg _)))
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sizeSq_nonneg _)))

theorem chart_scaled_cost (u : Triple) (t : ℝ) :
    defect (hemisphereChart (t • u)) ≤ t^2*sizeSq u := by
  have h := SU2HaarSmallCap.chart_defect_upper (t • u)
  have he : chartRate (t • u)-1=t^2*sizeSq u := by
    unfold chartRate sizeSq
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rwa [he] at h

theorem linkCost_constant_bound (a : Velocities) (t : ℝ) :
    linkCost (constantState a t) ≤ 64*t^2*∑ i : Fin 3,sizeSq (a i) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (e : SpatialEdge) _ => chart_scaled_cost (a e.2) t)
  have he : (∑ e : SpatialEdge,t^2*sizeSq (a e.2))=64*t^2*∑ i : Fin 3,sizeSq (a i) := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    norm_num [SpatialVertex,Fintype.card_fun]
    ring
  exact h.trans_eq he

theorem temporal_ray_comparison (a b : Velocities) (t : ℝ) (g : Gauge) :
    temporalAction (1 : State) 1 g ≤
      3*(temporalAction (constantState a t) (constantState b t) g+t^2*sourceBudget a b) := by
  have h := temporal_comparison (constantState a t) (constantState b t) g
  have ha := linkCost_constant_bound a t
  have hb := linkCost_constant_bound b t
  unfold sourceBudget
  nlinarith

theorem relative_ray_comparison (a b : Velocities) (t : ℝ) (g : Gauge) (v : SpatialVertex) :
    defect (g v*(g root)⁻¹) ≤ (3*4^10 : ℝ)*
      (temporalAction (constantState a t) (constantState b t) g+t^2*sourceBudget a b) := by
  have h := gauge_relative_point_bound g v
  have hc := mul_le_mul_of_nonneg_left (temporal_ray_comparison a b t g) (by norm_num : (0:ℝ)≤4^10)
  exact h.trans (by convert hc using 1 <;> ring)

def smallGauge : Set Gauge := {g | ∀ v : SpatialVertex,defect (g v*(g root)⁻¹)<1/4}

theorem smallGauge_measurable : MeasurableSet smallGauge := by
  simp only [smallGauge,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro v
  have hm : Measurable (fun g : Gauge => defect (g v*(g root)⁻¹)) :=
    measurable_const.sub (halfTrace_measurable.comp
      ((measurable_pi_apply v).mul (measurable_pi_apply root).inv))
  exact measurableSet_lt hm measurable_const

def exteriorRate : ℝ := 1/(12*4^10)

theorem exteriorRate_pos : 0 < exteriorRate := by norm_num [exteriorRate]

theorem outside_action (a b : Velocities) (t : ℝ) (g : Gauge) (hg : g∈smallGaugeᶜ) :
    exteriorRate ≤ temporalAction (constantState a t) (constantState b t) g+t^2*sourceBudget a b := by
  have hn : ¬ ∀ v : SpatialVertex,defect (g v*(g root)⁻¹)<1/4 := hg
  obtain ⟨v,hv⟩ := not_forall.mp hn
  have h := relative_ray_comparison a b t g v
  have hh := le_of_not_gt hv
  norm_num [exteriorRate] at h ⊢
  linarith

theorem halfAction_temporal (U V : State) (g : Gauge) : temporalAction U V g ≤ halfAction U V g := by
  unfold halfAction
  linarith [(spatial_action_bounds U).1,(spatial_action_bounds V).1]

theorem outside_weight_bound (a b : Velocities) (t : ℝ) (ht : t≠0)
    (g : Gauge) (hg : g∈smallGaugeᶜ) :
    weight (1/t^2) (constantState a t) (constantState b t) g ≤
      Real.exp (sourceBudget a b)*Real.exp (-exteriorRate/t^2) := by
  have h := outside_action a b t g hg
  have ha := halfAction_temporal (constantState a t) (constantState b t) g
  have had := div_le_div_of_nonneg_right ha (sq_nonneg t)
  rw [← Real.exp_add]
  unfold weight
  apply Real.exp_le_exp.mpr
  have he : (temporalAction (constantState a t) (constantState b t) g+t^2*sourceBudget a b)/t^2=
      temporalAction (constantState a t) (constantState b t) g/t^2+sourceBudget a b := by
    field_simp [ht]
  have hh := div_le_div_of_nonneg_right h (sq_nonneg t)
  rw [he] at hh
  simp only [div_eq_mul_inv,one_mul] at had hh ⊢
  nlinarith

theorem chart_size_local (y : Triple) (hy : defect (hemisphereChart y)<1/4) :
    sizeSq y ≤ 6*defect (hemisphereChart y) := by
  have hq := FourCubeHemisphereCoercivity.small_defect_chartRate (hemisphereChart y) hy
  rw [coordinates_chart] at hq
  have hp := radius_positive y
  have hs := radius_square y
  have hr : radius y≤2 := by
    have hh : (radius y)^2≤2 := by rw [radius,Real.sq_sqrt (chartRate_positive y).le]; exact hq
    nlinarith
  have he : sizeSq y=radius y*(radius y+1)*defect (hemisphereChart y) := by
    rw [defect,chart_halfTrace]
    field_simp [hp.ne']
    nlinarith
  rw [he]
  exact mul_le_mul_of_nonneg_right (by nlinarith : radius y*(radius y+1)≤6) (defect_nonneg _)

theorem gaugeRay_relative (Z : Field) (c : SU2) (t : ℝ) (v : SpatialVertex) :
    gaugeRay Z c t v*(gaugeRay Z c t root)⁻¹=hemisphereChart (t • velocity Z v) := by
  rw [gaugeRay_apply,gaugeRay_apply,velocity_root,smul_zero,CubeChartAction.chart_zero]
  group

def envelopeRate : ℝ := 1/(1134*4^10)

theorem envelopeRate_pos : 0 < envelopeRate := by norm_num [envelopeRate]

theorem inside_action (a b : Velocities) (Z : Field) (c : SU2) (t : ℝ) (ht : t≠0)
    (hg : gaugeRay Z c t∈smallGauge) :
    envelopeRate*fieldSizeSq Z ≤
      temporalAction (constantState a t) (constantState b t) (gaugeRay Z c t)/t^2+sourceBudget a b := by
  have he (v : RelFieldIndex) : t^2*sizeSq (Z v) ≤ (18*4^10 : ℝ)*
      (temporalAction (constantState a t) (constantState b t) (gaugeRay Z c t)+t^2*sourceBudget a b) := by
    have hv := hg v.val
    change defect (gaugeRay Z c t v.val*(gaugeRay Z c t root)⁻¹)<1/4 at hv
    rw [gaugeRay_relative,velocity_rel] at hv
    have hl := chart_size_local (t • Z v) hv
    have h := relative_ray_comparison a b t (gaugeRay Z c t) v.val
    rw [gaugeRay_relative,velocity_rel] at h
    have hs : sizeSq (t • Z v)=t^2*sizeSq (Z v) := by
      unfold sizeSq; simp only [Pi.smul_apply,smul_eq_mul]; ring
    rw [hs] at hl
    nlinarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => he v)
  simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,rel_count,nsmul_eq_mul] at h
  change t^2*fieldSizeSq Z ≤ _ at h
  have hf : t^2*fieldSizeSq Z ≤ t^2*((1134*4^10 : ℝ)*
      (temporalAction (constantState a t) (constantState b t) (gaugeRay Z c t)/t^2+sourceBudget a b)) := by
    convert h using 1 <;> field_simp [ht] <;> ring
  have hd := le_of_mul_le_mul_left hf (sq_pos_of_ne_zero ht)
  unfold envelopeRate
  norm_num at hd ⊢
  linarith

theorem inside_weight_bound (a b : Velocities) (Z : Field) (c : SU2) (t : ℝ) (ht : t≠0)
    (hg : gaugeRay Z c t∈smallGauge) :
    weight (1/t^2) (constantState a t) (constantState b t) (gaugeRay Z c t) ≤
      Real.exp (sourceBudget a b)*Real.exp (-envelopeRate*fieldSizeSq Z) := by
  have h := inside_action a b Z c t ht hg
  have ha := div_le_div_of_nonneg_right
    (halfAction_temporal (constantState a t) (constantState b t) (gaugeRay Z c t)) (sq_nonneg t)
  rw [← Real.exp_add]
  unfold weight
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv,one_mul] at h ha ⊢
  nlinarith


def insidePartition (a b : Velocities) (t : ℝ) : ℝ :=
  ∫ g in smallGauge,weight (1/t^2) (constantState a t) (constantState b t) g ∂gaugeHaar

def outsidePartition (a b : Velocities) (t : ℝ) : ℝ :=
  ∫ g in smallGaugeᶜ,weight (1/t^2) (constantState a t) (constantState b t) g ∂gaugeHaar

theorem kernel_split (a b : Velocities) (t : ℝ) :
    kernel (1/t^2) (constantState a t) (constantState b t)=insidePartition a b t+outsidePartition a b t :=
  (integral_add_compl smallGauge_measurable (weight_integrable (1/t^2) (constantState a t) (constantState b t))).symm

theorem outside_nonneg (a b : Velocities) (t : ℝ) : 0 ≤ outsidePartition a b t :=
  by
    unfold outsidePartition
    apply integral_nonneg
    intro g
    unfold weight
    exact (Real.exp_pos _).le

theorem outside_bound (a b : Velocities) (t : ℝ) (ht : t≠0) :
    outsidePartition a b t ≤ Real.exp (sourceBudget a b)*Real.exp (-exteriorRate/t^2) := by
  let C := Real.exp (sourceBudget a b)*Real.exp (-exteriorRate/t^2)
  have h := norm_setIntegral_le_of_norm_le_const (μ := gaugeHaar) (s := smallGaugeᶜ)
    (f := weight (1/t^2) (constantState a t) (constantState b t)) (measure_lt_top _ _)
    (fun g hg => by
      rw [Real.norm_eq_abs,abs_of_pos (by unfold weight; exact Real.exp_pos _)]
      exact outside_weight_bound a b t ht g hg)
  have hm : gaugeHaar.real smallGaugeᶜ ≤ 1 := measureReal_le_one
  have hc : 0 ≤ C := by unfold C; positivity
  have hh := mul_le_mul_of_nonneg_left hm hc
  simp only [mul_one] at hh
  exact (le_abs_self _).trans (h.trans hh)

theorem exponential_scale_limit :
    Tendsto (fun t : ℝ => Real.exp (-exteriorRate/t^2)/|t|^189) (𝓝[≠] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (95 : ℝ) exteriorRate exteriorRate_pos).comp
    FourCubeHaarPartitionAsymptotic.inverse_square_tendsto
  simp only [Real.rpow_ofNat,Function.comp_def] at h
  have h190 : Tendsto (fun t : ℝ => Real.exp (-exteriorRate/t^2)/|t|^190) (𝓝[≠] 0) (𝓝 0) := by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hp : |t|^(190 : ℕ)=(t^2)^(95 : ℕ) := by
      calc
        _ = (|t|^2)^95 := by rw [← pow_mul]
        _ = _ := by rw [sq_abs]
    rw [div_pow,one_pow,← hp]
    have he : -exteriorRate*(1/t^2)=-exteriorRate/t^2 := by ring
    rw [he]
    ring
  have hz : Tendsto (fun t : ℝ => |t|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero] using continuous_abs.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ)≤𝓝 0)
  have hh := hz.mul h190
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : |t|≠0 := abs_ne_zero.mpr ht
  rw [show (190 : ℕ)=189+1 by decide,pow_succ]
  field_simp

theorem outside_scaled_limit (a b : Velocities) :
    Tendsto (fun t : ℝ => outsidePartition a b t/|t|^189) (𝓝[≠] 0) (𝓝 0) := by
  have hh := exponential_scale_limit.const_mul (Real.exp (sourceBudget a b))
  simp only [mul_zero] at hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => div_nonneg (outside_nonneg a b t) (by positivity)))
    ?_ hh
  filter_upwards [self_mem_nhdsWithin] with t ht
  have h := div_le_div_of_nonneg_right (outside_bound a b t ht) (by positivity : 0≤|t|^189)
  simpa only [mul_div_assoc] using h

theorem gaussian_envelope_integrable (a b : Velocities) :
    Integrable (fun Z : Field => Real.exp (sourceBudget a b)*Real.exp (-envelopeRate*fieldSizeSq Z)) :=
  (fieldGaussian_integrable envelopeRate envelopeRate_pos).const_mul _


theorem gaugeRay_eventually_small (Z : Field) (c : SU2) :
    ∀ᶠ t : ℝ in 𝓝 0,gaugeRay Z c t∈smallGauge := by
  have hv (v : SpatialVertex) : ∀ᶠ t : ℝ in 𝓝 0,
      defect (hemisphereChart (t • velocity Z v))<1/4 := by
    have hlim : Tendsto (fun t : ℝ => t^2*sizeSq (velocity Z v)) (𝓝 0) (𝓝 0) := by
      simpa only [id_eq,zero_pow (by decide : 2≠0),zero_mul] using
        ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).pow 2).mul_const (sizeSq (velocity Z v))
    filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/4))] with t ht
    exact (chart_scaled_cost (velocity Z v) t).trans_lt ht
  filter_upwards [Filter.eventually_all.mpr hv] with t ht
  intro v
  rw [gaugeRay_relative]
  exact ht v

def cutoffWeight (a b : Velocities) (t : ℝ) (c : SU2) (Z : Field) : ℝ :=
  smallGauge.indicator (weight (1/t^2) (constantState a t) (constantState b t)) (gaugeRay Z c t)

theorem cutoffWeight_bound (a b : Velocities) (t : ℝ) (ht : t≠0) (c : SU2) (Z : Field) :
    |cutoffWeight a b t c Z| ≤ Real.exp (sourceBudget a b)*Real.exp (-envelopeRate*fieldSizeSq Z) := by
  unfold cutoffWeight
  by_cases hg : gaugeRay Z c t∈smallGauge
  · rw [Set.indicator_of_mem hg,abs_of_pos (by unfold weight; exact Real.exp_pos _)]
    exact inside_weight_bound a b Z c t ht hg
  · rw [Set.indicator_of_notMem hg,abs_zero]
    positivity

theorem cutoffWeight_tendsto (a b : Velocities) (c : SU2) (Z : Field) :
    Tendsto (fun t : ℝ => cutoffWeight a b t c Z) (𝓝[≠] 0)
      (𝓝 (gaussianIntegrand a b c*Real.exp (-graphEnergy Z))) := by
  apply (mixed_weight_limit a b Z c).congr'
  filter_upwards [(gaugeRay_eventually_small Z c).filter_mono nhdsWithin_le_nhds] with t ht
  exact (Set.indicator_of_mem ht _).symm

def constantField (s : ℝ) : Field := fun _ => ![s,0,0]

theorem fieldSizeSq_constant (s : ℝ) : fieldSizeSq (constantField s)=63*s^2 := by
  simp [fieldSizeSq,constantField,sizeSq,rel_count]

/-- A cutoff cannot be silently discarded: a compact-group weight has a
strict positive global lower bound at fixed coupling, whereas every positive
Gaussian in the unbounded chart coordinates vanishes at infinity. -/
theorem no_global_gaussian_bound (a b : Velocities) (t γ C : ℝ) (hγ : 0<γ) :
    ¬ ∀ Z : Field,weight (1/t^2) (constantState a t) (constantState b t) (gaugeRay Z 1 t) ≤
      C*Real.exp (-γ*fieldSizeSq Z) := by
  intro h
  have he := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) (63*γ) (by positivity)
  simp only [Real.rpow_zero,one_mul] at he
  have hh := he.comp (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ)≠0))
  have hc := hh.const_mul C
  simp only [mul_zero,Function.comp_def] at hc
  have hp (s : ℝ) : Real.exp (-768*|1/t^2|) ≤ C*Real.exp (-(63*γ)*s^2) := by
    have hb := (weight_bounds (1/t^2) (constantState a t) (constantState b t)
      (gaugeRay (constantField s) 1 t)).1
    have hn := h (constantField s)
    rw [fieldSizeSq_constant] at hn
    have heq : -γ*(63*s^2)=-(63*γ)*s^2 := by ring
    rw [heq] at hn
    exact hb.trans hn
  have hz := le_of_tendsto_of_tendsto tendsto_const_nhds hc (Filter.Eventually.of_forall hp)
  exact (not_le_of_gt (Real.exp_pos _)) hz

end OperatorDerivativeRewrite.Foundation.PeriodicRelativeGaugeTails
