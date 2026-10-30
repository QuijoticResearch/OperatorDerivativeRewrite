import Foundation.PeriodicCurvatureWeighted
import Foundation.SU2JointPlaquetteCubic
import Foundation.PeriodicSlabAction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
/-!
# A curved quartic family on the actual periodic SU(2) lattice

Spatially constant links in two different quaternion axes give an exact
commutator defect and quartic spatial/full Wilson actions. The continuous
family tends to the identity and is not pure gauge when its sine is nonzero.
The vanishing quadratic parameter profile is not a gauge-quotient distance
estimate or an assertion about stationary transfer measures or spectral gaps.
The actual first coordinate of its tangent reuses periodic winding to rule
out a scalar gradient. No full gauge-path linearization is asserted.
-/

noncomputable section
open scoped Quaternion Topology
open Filter
namespace OperatorDerivativeRewrite.Foundation.PeriodicQuarticCurvature
open QuaternionSU2Representation SU2JointPlaquetteCubic SU2HolonomyTraceObstruction
open PeriodicTemporalSlab PeriodicCurvatureVariance

private theorem axis_trace (a : Fin 3) (t : ℝ) : halfTrace (axis a t)=Real.cos t := by
  exact FourCubeWilsonCubic.axis_trace a t

private theorem product_trace (t : ℝ) : halfTrace (axis 0 t*axis 1 t)=Real.cos t^2 := by
  simp only [axis]
  rw [← hom.map_mul,halfTrace_map]
  norm_num [axisRaw,QuaternionAngularHaar.realCoordinate,Quaternion.re_mul]
  ring

theorem axis_commutator_trace (t : ℝ) :
    halfTrace (commutator (axis 0 t) (axis 1 t))=1-2*Real.sin t^4 := by
  have h := trace_commutator (axis 0 t) (axis 1 t)
  simp only [jointSquare,axis_trace,product_trace] at h
  have hs := Real.sin_sq_add_cos_sq t
  have h2 := congrArg (fun x : ℝ => x^2) hs
  have h3 := congrArg (fun x : ℝ => x*Real.cos t^2) hs
  nlinarith

def field (t : ℝ) : State := fun e => if e.2=0 then axis 0 t else if e.2=1 then axis 1 t else 1

def face01 : SpatialFace := ⟨((fun _ => 0),(0,1)),by decide⟩

theorem local_trace (t : ℝ) : plaquette face01 (field t)=1-2*Real.sin t^4 := by
  have hw : spatialWord (field t) face01=commutator (axis 0 t) (axis 1 t) := by
    simp [field,spatialWord,face01,SU2HolonomyTraceObstruction.commutator]
  rw [plaquette,hw,axis_commutator_trace]

theorem local_defect (t : ℝ) : 1-plaquette face01 (field t)=2*Real.sin t^4 := by
  rw [local_trace]
  ring

theorem not_pure_gauge (t : ℝ) (ht : Real.sin t ≠ 0) :
    ¬ ∃ a : Gauge,PeriodicSlabGauge.gaugeAction a (1 : State)=field t := by
  rintro ⟨a,ha⟩
  have h := congrArg (plaquette face01) ha
  rw [PeriodicCurvatureTransfer.plaquette_gauge,plaquette_one,local_trace] at h
  have hz : Real.sin t^4=0 := by linarith
  exact ht ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hz)

theorem face_defect (t : ℝ) (p : SpatialFace) :
    1-plaquette p (field t)=if p.val.2.1=0 ∧ p.val.2.2=1 then 2*Real.sin t^4 else 0 := by
  have hw : spatialWord (field t) p=
      if p.val.2.1=0 ∧ p.val.2.2=1 then
        SU2HolonomyTraceObstruction.commutator (axis 0 t) (axis 1 t) else 1 := by
    rcases p with ⟨⟨v,i,j⟩,hij⟩
    change i < j at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;>
      simp [spatialWord,field,SU2HolonomyTraceObstruction.commutator]
  rw [plaquette,hw]
  split_ifs <;> simp [axis_commutator_trace,SU2OpenLinkGaugeObstruction.halfTrace_one] <;> ring

private abbrev Pair3 := {ij : Fin 3 × Fin 3 // ij.1 < ij.2}
private def faceProduct : SpatialFace ≃ SpatialVertex × Pair3 where
  toFun p := (p.val.1,⟨p.val.2,p.property⟩)
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem spatial_action (t : ℝ) : PeriodicWilsonSlab.spatialAction (field t)=128*Real.sin t^4 := by
  change (∑ p : SpatialFace,(1-plaquette p (field t)))=_
  simp_rw [face_defect]
  rw [← faceProduct.symm.sum_comp]
  simp only [Fintype.sum_prod_type,faceProduct,Equiv.coe_fn_symm_mk]
  have hpairs : (Finset.univ : Finset Pair3)=
      {⟨(0,1),by decide⟩,⟨(0,2),by decide⟩,⟨(1,2),by decide⟩} := by decide
  simp only [hpairs]
  norm_num [Finset.sum_insert,SpatialVertex,Fintype.card_fun]
  ring

def fullField (t : ℝ) : PeriodicSU2FlatHolonomy.Links :=
  fun e => if e.2=0 then axis 0 t else if e.2=1 then axis 1 t else 1

theorem spatial_full (t : ℝ) (s : ZMod 4) : spatialField (fullField t) s=field t := by
  funext e
  rcases e with ⟨v,i⟩
  fin_cases i <;> rfl

theorem temporal_full (t : ℝ) (s : ZMod 4) : temporalField (fullField t) s=1 := by
  funext v
  rfl

theorem temporal_self (t : ℝ) : PeriodicWilsonSlab.temporalAction (field t) (field t) 1=0 := by
  unfold PeriodicWilsonSlab.temporalAction
  apply Finset.sum_eq_zero
  intro e _
  simp [temporalWord,SU2OpenLinkGaugeObstruction.halfTrace_one]

theorem full_action (t : ℝ) : PeriodicSU2FlatHolonomy.action (fullField t)=512*Real.sin t^4 := by
  rw [PeriodicSlabAction.cyclic_half_action]
  simp_rw [spatial_full,temporal_full]
  norm_num [PeriodicWilsonSlab.halfAction,temporal_self,spatial_action] <;> ring

theorem spatial_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => PeriodicWilsonSlab.spatialAction (field s))
      (512*Real.sin t^3*Real.cos t) t := by
  have he : (fun s => PeriodicWilsonSlab.spatialAction (field s))=(fun s => 128*Real.sin s^4) :=
    funext spatial_action
  rw [he]
  convert ((Real.hasDerivAt_sin t).pow 4).const_mul 128 using 1 <;> ring

theorem deriv_spatial (t : ℝ) :
    deriv (fun s => PeriodicWilsonSlab.spatialAction (field s)) t=512*Real.sin t^3*Real.cos t :=
  (spatial_hasDerivAt t).deriv

theorem spatial_first_zero : deriv (fun s => PeriodicWilsonSlab.spatialAction (field s)) 0=0 := by
  rw [deriv_spatial]
  norm_num

theorem spatial_second_zero : deriv (deriv (fun s => PeriodicWilsonSlab.spatialAction (field s))) 0=0 := by
  have he : deriv (fun s => PeriodicWilsonSlab.spatialAction (field s))=
      (fun t => 512*Real.sin t^3*Real.cos t) := funext deriv_spatial
  rw [he]
  have h : HasDerivAt (fun t : ℝ => 512*Real.sin t^3*Real.cos t) 0 0 := by
    convert (((Real.hasDerivAt_sin 0).pow 3).mul (Real.hasDerivAt_cos 0)).const_mul 512 using 1 <;>
      norm_num <;> ring
  exact h.deriv

private theorem sin_sinc (t : ℝ) : Real.sin t=t*Real.sinc t := by
  by_cases ht : t=0
  · simp [ht]
  · rw [Real.sinc_of_ne_zero ht]
    field_simp

theorem spatial_profile (t : ℝ) :
    PeriodicWilsonSlab.spatialAction (field t)=128*t^4*Real.sinc t^4 := by
  rw [spatial_action,sin_sinc]
  ring

theorem quadratic_ratio_limit :
    Tendsto (fun t : ℝ => PeriodicWilsonSlab.spatialAction (field t)/t^2) (𝓝 0) (𝓝 0) := by
  have hp : (fun t : ℝ => PeriodicWilsonSlab.spatialAction (field t)/t^2)=
      (fun t => 128*t^2*Real.sinc t^4) := by
    funext t
    rw [spatial_profile]
    by_cases ht : t=0
    · simp [ht]
    · field_simp
  rw [hp]
  have hi : Tendsto (fun t : ℝ => t) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_id
  have hs := Real.continuous_sinc.tendsto (0 : ℝ)
  simpa using ((hi.pow 2).const_mul 128).mul (hs.pow 4)

theorem quartic_ratio_limit :
    Tendsto (fun t : ℝ => PeriodicWilsonSlab.spatialAction (field t)/t^4) (𝓝[≠] 0) (𝓝 128) := by
  have hs : Tendsto Real.sinc (𝓝[≠] (0 : ℝ)) (𝓝 (Real.sinc 0)) :=
    (Real.continuous_sinc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have h := (hs.pow 4).const_mul 128
  have hh : Tendsto (fun t : ℝ => 128*Real.sinc t^4) (𝓝[≠] 0) (𝓝 (128 : ℝ)) := by simpa using h
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : t ≠ 0 := ht
  rw [spatial_profile]
  field_simp

theorem eventual_subquadratic (c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,PeriodicWilsonSlab.spatialAction (field t) < c*t^2 := by
  have h : Tendsto (fun t : ℝ => PeriodicWilsonSlab.spatialAction (field t)/t^2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := quadratic_ratio_limit.mono_left nhdsWithin_le_nhds
  filter_upwards [h.eventually (gt_mem_nhds hc),self_mem_nhdsWithin] with t ht hn
  exact (div_lt_iff₀ (sq_pos_of_ne_zero (show t ≠ 0 from hn))).mp ht

theorem no_quadratic_floor :
    ¬ ∃ c : ℝ,0 < c ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0,c*t^2 ≤ PeriodicWilsonSlab.spatialAction (field t) := by
  rintro ⟨c,hc,h⟩
  obtain ⟨t,hl,hu⟩ := (h.and (eventual_subquadratic c hc)).exists
  exact (not_le_of_gt hu) hl

theorem axis_at_zero (a : Fin 3) : axis a 0=1 := by
  apply (FourCubePinnedCoercivity.defect_zero_iff _).mp
  norm_num [FourCubePinnedCoercivity.defect,FourCubeWilsonCubic.axis_trace]

theorem field_at_zero : field 0=1 := by
  funext e
  simp [field,axis_at_zero]

theorem full_at_zero : fullField 0=1 := by
  funext e
  simp [fullField,axis_at_zero]

def constantTangent (e : PeriodicInteriorGaugeKernel.Edge) : ℝ := if e.2=0 then 1 else 0

theorem tangent_closed (v : PeriodicInteriorGaugeKernel.Vertex) (i j : PeriodicInteriorGaugeKernel.Direction) :
    PeriodicInteriorGaugeKernel.curl constantTangent v i j=0 := by
  unfold PeriodicInteriorGaugeKernel.curl constantTangent
  ring

theorem tangent_winding : PeriodicInteriorHolonomy.winding constantTangent=4 := by
  norm_num [PeriodicInteriorHolonomy.winding,constantTangent]

theorem tangent_not_gradient :
    ¬ ∃ phi : PeriodicInteriorGaugeKernel.Vertex → ℝ,
      PeriodicInteriorGaugeKernel.gradientMap phi=constantTangent := by
  rintro ⟨phi,hphi⟩
  have h := PeriodicInteriorHolonomy.gradient_winding_zero phi
  rw [hphi,tangent_winding] at h
  norm_num at h

private theorem component_formula (t : ℝ) (e : PeriodicInteriorGaugeKernel.Edge) :
    (recover (fullField t e : SU2TraceHessianModel.M2)).imI=
      if e.2=0 then Real.sin t else 0 := by
  rcases e with ⟨v,i⟩
  fin_cases i <;> norm_num [fullField,axis,hom,axisRaw,recover,QuaternionSU2Representation.repr,Complex.mul_re,Complex.mul_im] <;>
    simp only [← Complex.ofReal_sin,Complex.ofReal_re]

theorem tangent_component (e : PeriodicInteriorGaugeKernel.Edge) :
    HasDerivAt (fun t : ℝ => (recover (fullField t e : SU2TraceHessianModel.M2)).imI)
      (constantTangent e) 0 := by
  have he : (fun t : ℝ => (recover (fullField t e : SU2TraceHessianModel.M2)).imI)=
      (fun t => if e.2=0 then Real.sin t else 0) := funext (fun t => component_formula t e)
  rw [he]
  by_cases h : e.2=0
  · simpa [h,constantTangent] using Real.hasDerivAt_sin (0 : ℝ)
  · simpa [h,constantTangent] using hasDerivAt_const (0 : ℝ) (0 : ℝ)

theorem no_full_quadratic_floor :
    ¬ ∃ c : ℝ,0 < c ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0,c*t^2 ≤ PeriodicSU2FlatHolonomy.action (fullField t) := by
  rintro ⟨c,hc,h⟩
  apply no_quadratic_floor
  refine ⟨c/4,by positivity,?_⟩
  filter_upwards [h] with t ht
  rw [full_action] at ht
  rw [spatial_action]
  linarith

theorem full_not_pure_gauge (t : ℝ) (ht : Real.sin t ≠ 0) :
    ¬ ∃ a : PeriodicSU2FlatHolonomy.Gauge,
      PeriodicSU2FlatHolonomy.gaugeAction a (1 : PeriodicSU2FlatHolonomy.Links)=fullField t := by
  rintro ⟨a,ha⟩
  have h := congrArg PeriodicSU2FlatHolonomy.action ha
  rw [PeriodicSU2FlatHolonomy.action_gauge,full_action] at h
  have hz : PeriodicSU2FlatHolonomy.action (1 : PeriodicSU2FlatHolonomy.Links)=0 := by
    have hs : PeriodicSU2FlatHolonomy.seam (1 : SU2)=(1 : PeriodicSU2FlatHolonomy.Links) := by
      funext e
      simp [PeriodicSU2FlatHolonomy.seam]
    have hh := PeriodicSU2FlatHolonomy.seam_action (1 : SU2)
    rw [hs] at hh
    exact hh
  rw [hz] at h
  have hs : Real.sin t^4=0 := by linarith
  exact ht ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hs)

private theorem axis_continuous (a : Fin 3) : Continuous (axis a) := by
  have he : axisRaw a = fun t : ℝ =>
      (Real.cos t : ℍ) + Real.sin t • generatorRaw a := by
    funext t
    fin_cases a <;> ext <;> simp [axisRaw,generatorRaw]
  have hraw : Continuous (axisRaw a) := by
    rw [he]
    exact (Quaternion.continuous_coe.comp Real.continuous_cos).add
      (Real.continuous_sin.smul continuous_const)
  unfold axis
  apply hom_continuous.comp
  exact hraw.subtype_mk _
theorem field_continuous : Continuous field := by
  apply continuous_pi
  intro e
  by_cases h0 : e.2=0
  · simpa [field,h0] using axis_continuous 0
  · by_cases h1 : e.2=1
    · simpa [field,h0,h1] using axis_continuous 1
    · simpa [field,h0,h1] using (continuous_const : Continuous (fun _ : ℝ => (1 : SU2)))

theorem full_continuous : Continuous fullField := by
  apply continuous_pi
  intro e
  by_cases h0 : e.2=0
  · simpa [fullField,h0] using axis_continuous 0
  · by_cases h1 : e.2=1
    · simpa [fullField,h0,h1] using axis_continuous 1
    · simpa [fullField,h0,h1] using (continuous_const : Continuous (fun _ : ℝ => (1 : SU2)))

theorem full_tendsto_identity : Tendsto fullField (𝓝 0) (𝓝 (1 : PeriodicSU2FlatHolonomy.Links)) := by
  simpa only [full_at_zero] using full_continuous.tendsto (0 : ℝ)
end OperatorDerivativeRewrite.Foundation.PeriodicQuarticCurvature
