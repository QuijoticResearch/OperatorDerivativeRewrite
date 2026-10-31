import Foundation.PeriodicAnchoredCovariantGaussian
import Foundation.PeriodicFullHaarGaussianLimit
/-! Actual nonlinear temporal Wilson control at a pinned identity root,
including arbitrary link backgrounds, boundary perturbations, local Gaussian
prelimit envelopes and exterior suppression. The compact common root is not
integrated or removed. Constants refer to the fixed side-four periodic cell. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicRootedHaarControl
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart SU2HemisphereJets
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicGaugeSaturatedGround PeriodicRelativeGaugeGaussian
open FourCubePinnedCoercivity

theorem defect_conjugate (U A : SU2) : defect (U*A*U⁻¹)=defect A := by
  unfold defect
  rw [halfTrace_conjugate]

theorem temporal_step (U : State) (g : Gauge) (e : SpatialEdge) :
    defect (g (shift e.1 e.2))≤3*(defect (temporalWord U U g e)+defect (g e.1)) := by
  have he : U e*g (shift e.1 e.2)*(U e)⁻¹=temporalWord U U g e*g e.1 := by
    unfold temporalWord
    group
  rw [← defect_conjugate (U e),he]
  exact FourCubeBoundaryCoercivity.defect_mul _ _

private theorem term_le_sum {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i,0≤f i) (i : ι) : f i≤∑ j,f j := by
  exact Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

theorem temporal_term_le (U V : State) (g : Gauge) (e : SpatialEdge) :
    defect (temporalWord U V g e)≤temporalAction U V g := by
  have h := term_le_sum (fun k => defect (temporalWord U V g k))
    (fun k => defect_nonneg (temporalWord U V g k)) e
  simpa only [defect,temporalAction] using h

theorem rooted_defect (U : State) (g : Gauge) (hg : g root=1) (v : SpatialVertex) :
    defect (g v)≤((3 : ℝ)^(depth v+1)-3)/2*temporalAction U U g := by
  generalize hn : depth v=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v=root
    · subst v
      rw [← hn]
      simp [hg,depth,root,defect_one]
    · have hd := parent_depth v hv
      have hprev := ih (depth (parent v)) (by omega) (parent v) rfl
      have hs := temporal_step U g (parent v,axis v)
      rw [parent_shift v hv] at hs
      have ht := temporal_term_le U U g (parent v,axis v)
      have hp : ((3 : ℝ)^(depth v+1)-3)/2=
          3+3*(((3 : ℝ)^(depth (parent v)+1)-3)/2) := by
        rw [← hd,pow_succ]
        ring
      rw [← hn,hp]
      linarith

theorem rooted_uniform (U : State) (g : Gauge) (hg : g root=1) (v : SpatialVertex) :
    defect (g v)≤29523*temporalAction U U g := by
  have h := rooted_defect U g hg v
  have hp : (3 : ℝ)^(depth v+1)≤3^10 :=
    pow_le_pow_right₀ (by norm_num) (by have hd := depth_le v; omega)
  have hn := (temporal_action_bounds U U g).1
  nlinarith

def boundaryCost (H U : State) : ℝ := ∑ e : SpatialEdge,defect (U e*(H e)⁻¹)

theorem edge_comparison (H U V : State) (g : Gauge) (e : SpatialEdge) :
    defect (temporalWord H H g e)≤3*(defect (U e*(H e)⁻¹)+
      defect (temporalWord U V g e)+defect (V e*(H e)⁻¹)) := by
  have he : (H e*(U e)⁻¹)*temporalWord U V g e*(g e.1*(V e*(H e)⁻¹)*(g e.1)⁻¹)=
      temporalWord H H g e := by unfold temporalWord; group
  have h := defect_triple (H e*(U e)⁻¹) (temporalWord U V g e)
    (g e.1*(V e*(H e)⁻¹)*(g e.1)⁻¹)
  rw [he,defect_conjugate] at h
  have hi : H e*(U e)⁻¹=(U e*(H e)⁻¹)⁻¹ := by group
  rwa [hi,defect_inv] at h

theorem temporal_comparison (H U V : State) (g : Gauge) :
    temporalAction H H g≤3*(boundaryCost H U+temporalAction U V g+boundaryCost H V) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun e _ => edge_comparison H U V g e)
  unfold boundaryCost temporalAction
  simpa only [defect,Finset.sum_add_distrib,← Finset.mul_sum] using h

def chartState (H : State) (X : PeriodicFlatBackgroundHessian.Velocity) (t : ℝ) : State :=
  fun e => hemisphereChart (t • X e)*H e

def budget (X Y : PeriodicFlatBackgroundHessian.Velocity) : ℝ :=
  (∑ e : SpatialEdge,sizeSq (X e))+(∑ e : SpatialEdge,sizeSq (Y e))

theorem budget_nonneg (X Y : PeriodicFlatBackgroundHessian.Velocity) : 0≤budget X Y :=
  add_nonneg (Finset.sum_nonneg (fun _ _ => sizeSq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sizeSq_nonneg _))

theorem chart_boundary_bound (H : State) (X : PeriodicFlatBackgroundHessian.Velocity) (t : ℝ) :
    boundaryCost H (chartState H X t)≤t^2*∑ e : SpatialEdge,sizeSq (X e) := by
  unfold boundaryCost chartState
  simp only [mul_inv_cancel_right]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun e _ => PeriodicRelativeGaugeTails.chart_scaled_cost (X e) t)
  simpa only [Finset.mul_sum] using h

theorem ray_comparison (H : State) (X Y : PeriodicFlatBackgroundHessian.Velocity)
    (t : ℝ) (g : Gauge) :
    temporalAction H H g≤3*(temporalAction (chartState H X t) (chartState H Y t) g+t^2*budget X Y) := by
  have h := temporal_comparison H (chartState H X t) (chartState H Y t) g
  have hx := chart_boundary_bound H X t
  have hy := chart_boundary_bound H Y t
  unfold budget
  nlinarith

theorem rooted_ray_bound (H : State) (X Y : PeriodicFlatBackgroundHessian.Velocity)
    (t : ℝ) (g : Gauge) (hg : g root=1) (v : SpatialVertex) :
    defect (g v)≤88569*(temporalAction (chartState H X t) (chartState H Y t) g+t^2*budget X Y) := by
  have h := rooted_uniform H g hg v
  have hc := mul_le_mul_of_nonneg_left (ray_comparison H X Y t g) (by norm_num : (0 : ℝ)≤29523)
  nlinarith

open PeriodicRelativeGaugeTails (smallGauge chart_size_local halfAction_temporal)

def exteriorRate : ℝ := 1/354276
def envelopeRate : ℝ := 1/33479082

theorem exteriorRate_pos : 0<exteriorRate := by norm_num [exteriorRate]
theorem envelopeRate_pos : 0<envelopeRate := by norm_num [envelopeRate]

private theorem ray_root (Z : Field) (t : ℝ) : gaugeRay Z 1 t root=1 := by
  rw [gaugeRay_apply,velocity_root,smul_zero,CubeChartAction.chart_zero,mul_one]

theorem outside_action (H : State) (X Y : PeriodicFlatBackgroundHessian.Velocity)
    (t : ℝ) (g : Gauge) (hr : g root=1) (hg : g∉smallGauge) :
    exteriorRate≤temporalAction (chartState H X t) (chartState H Y t) g+t^2*budget X Y := by
  have hn : ¬∀ v : SpatialVertex,defect (g v*(g root)⁻¹)<1/4 := hg
  obtain ⟨v,hv⟩ := not_forall.mp hn
  have hh := rooted_ray_bound H X Y t g hr v
  rw [hr,inv_one,mul_one] at hv
  have hv' : (1 : ℝ)/4≤defect (g v) := le_of_not_gt hv
  unfold exteriorRate
  linarith

theorem outside_weight_bound (H : State) (X Y : PeriodicFlatBackgroundHessian.Velocity)
    (t : ℝ) (ht : t≠0) (g : Gauge) (hr : g root=1) (hg : g∉smallGauge) :
    PeriodicWilsonSlab.weight (1/t^2) (chartState H X t) (chartState H Y t) g≤
      Real.exp (budget X Y)*Real.exp (-exteriorRate/t^2) := by
  have h := outside_action H X Y t g hr hg
  have ha := halfAction_temporal (chartState H X t) (chartState H Y t) g
  have hb : exteriorRate/t^2≤halfAction (chartState H X t) (chartState H Y t) g/t^2+budget X Y := by
    apply (div_le_iff₀ (sq_pos_of_ne_zero ht)).mpr
    rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 ht)]
    nlinarith
  rw [← Real.exp_add]
  unfold PeriodicWilsonSlab.weight
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv,one_mul] at hb ⊢
  linarith

theorem inside_action (H : State) (X Y : PeriodicFlatBackgroundHessian.Velocity)
    (Z : Field) (t : ℝ) (ht : t≠0) (hg : gaugeRay Z 1 t∈smallGauge) :
    envelopeRate*fieldSizeSq Z≤
      temporalAction (chartState H X t) (chartState H Y t) (gaugeRay Z 1 t)/t^2+budget X Y := by
  have he (v : RelFieldIndex) : t^2*sizeSq (Z v)≤531414*
      (temporalAction (chartState H X t) (chartState H Y t) (gaugeRay Z 1 t)+t^2*budget X Y) := by
    have hv := hg v.val
    change defect (gaugeRay Z 1 t v.val*(gaugeRay Z 1 t root)⁻¹)<1/4 at hv
    rw [PeriodicRelativeGaugeTails.gaugeRay_relative,velocity_rel] at hv
    have hl := chart_size_local (t • Z v) hv
    have hh := rooted_ray_bound H X Y t (gaugeRay Z 1 t) (ray_root Z t) v.val
    rw [gaugeRay_apply,velocity_rel,mul_one] at hh
    have hs : sizeSq (t • Z v)=t^2*sizeSq (Z v) := by
      unfold sizeSq
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
    rw [hs] at hl
    linarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => he v)
  simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,rel_count,nsmul_eq_mul] at h
  change t^2*fieldSizeSq Z≤_ at h
  have hf : t^2*fieldSizeSq Z≤t^2*(33479082*
      (temporalAction (chartState H X t) (chartState H Y t) (gaugeRay Z 1 t)/t^2+budget X Y)) := by
    convert h using 1 <;> field_simp [ht] <;> ring
  have hd := le_of_mul_le_mul_left hf (sq_pos_of_ne_zero ht)
  unfold envelopeRate
  linarith

theorem inside_weight_bound (H : State) (X Y : PeriodicFlatBackgroundHessian.Velocity)
    (Z : Field) (t : ℝ) (ht : t≠0) (hg : gaugeRay Z 1 t∈smallGauge) :
    PeriodicWilsonSlab.weight (1/t^2) (chartState H X t) (chartState H Y t) (gaugeRay Z 1 t)≤
      Real.exp (budget X Y)*Real.exp (-envelopeRate*fieldSizeSq Z) := by
  have h := inside_action H X Y Z t ht hg
  have ha := div_le_div_of_nonneg_right
    (halfAction_temporal (chartState H X t) (chartState H Y t) (gaugeRay Z 1 t)) (sq_nonneg t)
  rw [← Real.exp_add]
  unfold PeriodicWilsonSlab.weight
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv,one_mul] at h ha ⊢
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicRootedHaarControl
