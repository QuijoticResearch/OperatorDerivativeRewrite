import Foundation.SU2QuarticValleyNonintegrable
import Foundation.SU2HemisphereJets
/-! Exact constant-field soft-mode rays of the actual periodic Wilson slab.
The full nine-coordinate spatial quartic profile is128 times the pure-imaginary
commutator potential; its bare Gibbs density is therefore nonnormalizable.
The temporal quadratic profile at the IDENTITY gauge is also identified.
These are actual action/pointwise ray statements, not a gauge-integrated,
ground-normalized operator limit or a spectral/mass-gap conclusion. -/
noncomputable section
open scoped Quaternion Topology Matrix
open Filter
namespace OperatorDerivativeRewrite.Foundation.PeriodicConstantQuarticJet
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart SU2HemisphereJets
open SU2HolonomyTraceObstruction SU2QuarticValleyNonintegrable PeriodicTemporalSlab PeriodicWilsonSlab

def dot3 (u v : Triple) : ℝ := u 0*v 0+u 1*v 1+u 2*v 2

theorem radius_square (u : Triple) : (radius u)^2=1+sizeSq u := by
  rw [radius,Real.sq_sqrt (chartRate_positive u).le]
  unfold chartRate sizeSq
  ring

theorem chart_product_trace (u v : Triple) :
    halfTrace (hemisphereChart u*hemisphereChart v)=(1-dot3 u v)/(radius u*radius v) := by
  change SU2TraceHessianModel.traceReal ((hemisphereChart u : SU2TraceHessianModel.M2)*
    (hemisphereChart v : SU2TraceHessianModel.M2))/2=_
  rw [chart_matrix,chart_matrix,smul_mul_assoc,mul_smul_comm,smul_smul,← repr_mul]
  change SU2TraceHessianModel.traceReal
    ((((radius u)⁻¹*(radius v)⁻¹ : ℝ) : ℂ) • QuaternionSU2Representation.repr (rawPoint u*rawPoint v))/2=_
  rw [SU2ProductCurveHessian.traceReal_real_smul,repr_traceReal]
  simp only [Quaternion.re_mul,rawPoint]
  unfold dot3
  field_simp
  <;> ring

theorem chart_commutator_defect (u v : Triple) :
    1-halfTrace (commutator (hemisphereChart u) (hemisphereChart v))=
      2*crossSquare u v/((radius u)^2*(radius v)^2) := by
  rw [trace_commutator]
  simp only [jointSquare,chart_halfTrace,chart_product_trace]
  have hu := radius_square u
  have hv := radius_square v
  have huv : (radius u)^2*(radius v)^2=(1+sizeSq u)*(1+sizeSq v) := by rw [hu,hv]
  field_simp [(radius_positive u).ne',(radius_positive v).ne']
  nlinarith [huv,show crossSquare u v=sizeSq u*sizeSq v-(dot3 u v)^2 by
    unfold crossSquare sizeSq dot3; ring]

theorem crossSquare_smul (t : ℝ) (u v : Triple) :
    crossSquare (t • u) (t • v)=t^4*crossSquare u v := by
  simp only [crossSquare,Pi.smul_apply,smul_eq_mul]
  ring

theorem radius_scaled_square (t : ℝ) (u : Triple) :
    (radius (t • u))^2=1+t^2*sizeSq u := by
  rw [radius_square]
  simp only [sizeSq,Pi.smul_apply,smul_eq_mul]
  ring

theorem scaled_commutator_defect (t : ℝ) (u v : Triple) :
    1-halfTrace (commutator (hemisphereChart (t • u)) (hemisphereChart (t • v)))=
      t^4*(2*crossSquare u v/((1+t^2*sizeSq u)*(1+t^2*sizeSq v))) := by
  rw [chart_commutator_defect,crossSquare_smul,radius_scaled_square,radius_scaled_square]
  ring

theorem quartic_coefficient_tendsto (u v : Triple) :
    Tendsto (fun t : ℝ => 2*crossSquare u v/((1+t^2*sizeSq u)*(1+t^2*sizeSq v)))
      (𝓝 0) (𝓝 (2*crossSquare u v)) := by
  have hc : Continuous (fun t : ℝ => (1+t^2*sizeSq u)*(1+t^2*sizeSq v)) := by fun_prop
  convert (tendsto_const_nhds.div (hc.tendsto 0) (by norm_num : (1+(0:ℝ)^2*sizeSq u)*(1+0^2*sizeSq v)≠0)) using 1 <;> simp


abbrev Velocities := Fin 3 → Triple
abbrev Pair3 := {ij : Fin 3 × Fin 3 // ij.1 < ij.2}

def constantState (a : Velocities) (t : ℝ) : State := fun e => hemisphereChart (t • a e.2)

theorem constant_word (a : Velocities) (t : ℝ) (p : SpatialFace) :
    spatialWord (constantState a t) p=
      commutator (hemisphereChart (t • a p.val.2.1)) (hemisphereChart (t • a p.val.2.2)) := rfl

private def faceEquiv : SpatialFace ≃ SpatialVertex × Pair3 where
  toFun p := (p.val.1,⟨p.val.2,p.property⟩)
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def coefficient (a : Velocities) (t : ℝ) : ℝ :=
  64*∑ p : Pair3,2*crossSquare (a p.val.1) (a p.val.2)/
    ((1+t^2*sizeSq (a p.val.1))*(1+t^2*sizeSq (a p.val.2)))

theorem spatial_action_exact (a : Velocities) (t : ℝ) :
    spatialAction (constantState a t)=t^4*coefficient a t := by
  unfold spatialAction
  simp_rw [constant_word,scaled_commutator_defect]
  rw [← faceEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type,faceEquiv,Equiv.coe_fn_symm_mk]
  simp only [Finset.sum_const,Finset.card_univ]
  norm_num only [SpatialVertex,Fintype.card_fun,Fintype.card_fin,ZMod.card,show 4^3=64 by norm_num]
  simp only [← Finset.mul_sum]
  unfold coefficient
  ring

theorem coefficient_tendsto (a : Velocities) :
    Tendsto (coefficient a) (𝓝 0) (𝓝 (coefficient a 0)) := by
  have h := tendsto_finset_sum Finset.univ (fun p (_ : p∈(Finset.univ : Finset Pair3)) =>
    quartic_coefficient_tendsto (a p.val.1) (a p.val.2))
  unfold coefficient
  simpa only [zero_pow (by decide : (2:ℕ)≠0),zero_mul,add_zero,one_mul,div_one] using h.const_mul 64

theorem spatial_quartic_limit (a : Velocities) :
    Tendsto (fun t : ℝ => spatialAction (constantState a t)/t^4)
      (𝓝[≠] 0) (𝓝 (coefficient a 0)) := by
  apply (coefficient_tendsto a).mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change t≠0 at ht
  rw [spatial_action_exact]
  field_simp

def configVelocity (p : Config) : Velocities := ![X p,Y p,Z p]

theorem coefficient_config (p : Config) : coefficient (configVelocity p) 0=128*potential p := by
  have hpairs : (Finset.univ : Finset Pair3)=
      {⟨(0,1),by decide⟩,⟨(0,2),by decide⟩,⟨(1,2),by decide⟩} := by decide
  unfold coefficient
  rw [hpairs]
  norm_num [configVelocity,potential,Finset.sum_insert]
  <;> ring

/-- Actual Wilson spatial quartic profile in ALL nine constant Lie coordinates,
with the precise potential whose bare Lebesgue Gibbs partition diverges. -/
theorem nine_coordinate_quartic_limit (p : Config) :
    Tendsto (fun t : ℝ => spatialAction (constantState (configVelocity p) t)/t^4)
      (𝓝[≠] 0) (𝓝 (128*potential p)) := by
  simpa only [coefficient_config] using spatial_quartic_limit (configVelocity p)



theorem dot3_smul (t : ℝ) (u v : Triple) : dot3 (t • u) (t • v)=t^2*dot3 u v := by
  simp only [dot3,Pi.smul_apply,smul_eq_mul]
  ring

theorem difference_square (u v : Triple) : sizeSq (u-v)=sizeSq u+sizeSq v-2*dot3 u v := by
  simp only [sizeSq,dot3,Pi.sub_apply]
  ring

theorem crossSquare_identity (u v : Triple) : crossSquare u v=sizeSq u*sizeSq v-(dot3 u v)^2 := by
  unfold crossSquare sizeSq dot3
  ring

theorem chart_relative_trace (u v : Triple) :
    halfTrace (hemisphereChart u*(hemisphereChart v)⁻¹)=(1+dot3 u v)/(radius u*radius v) := by
  have h := SU2WilsonConvolution.trace_pair (hemisphereChart u) (hemisphereChart v)
  rw [chart_product_trace,chart_halfTrace,chart_halfTrace] at h
  field_simp [(radius_positive u).ne',(radius_positive v).ne'] at h ⊢
  nlinarith

def kineticCoefficient (u v : Triple) (t : ℝ) : ℝ :=
  (sizeSq (u-v)+t^2*crossSquare u v)/
    ((radius (t • u)*radius (t • v))*(radius (t • u)*radius (t • v)+1+t^2*dot3 u v))

theorem scaled_relative_defect (u v : Triple) (t : ℝ)
    (hden : radius (t • u)*radius (t • v)+1+t^2*dot3 u v≠0) :
    1-halfTrace (hemisphereChart (t • u)*(hemisphereChart (t • v))⁻¹)=
      t^2*kineticCoefficient u v t := by
  rw [chart_relative_trace,dot3_smul]
  unfold kineticCoefficient
  have hu := radius_scaled_square t u
  have hv := radius_scaled_square t v
  have huv : (radius (t • u)*radius (t • v))^2=
      (1+t^2*sizeSq u)*(1+t^2*sizeSq v) := by rw [mul_pow,hu,hv]
  rw [difference_square,crossSquare_identity]
  field_simp [(radius_positive (t • u)).ne',(radius_positive (t • v)).ne',hden]
  nlinarith [huv]

theorem radius_tendsto (u : Triple) : Tendsto (fun t : ℝ => radius (t • u)) (𝓝 0) (𝓝 1) := by
  have h : Continuous (fun t : ℝ => Real.sqrt (1+t^2*sizeSq u)) := by fun_prop
  simpa only [radius_smul,zero_pow (by decide : (2:ℕ)≠0),zero_mul,add_zero,Real.sqrt_one] using h.tendsto 0

theorem kinetic_denominator_tendsto (u v : Triple) :
    Tendsto (fun t : ℝ => radius (t • u)*radius (t • v)+1+t^2*dot3 u v) (𝓝 0) (𝓝 2) := by
  have hpow : Tendsto (fun t : ℝ => t^2*dot3 u v) (𝓝 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).pow 2).mul_const (dot3 u v)
  simpa only [one_mul,add_zero,show (1:ℝ)+1=2 by norm_num] using (((radius_tendsto u).mul (radius_tendsto v)).add_const 1).add hpow

theorem kinetic_coefficient_tendsto (u v : Triple) :
    Tendsto (kineticCoefficient u v) (𝓝 0) (𝓝 (sizeSq (u-v)/2)) := by
  have hnum : Tendsto (fun t : ℝ => sizeSq (u-v)+t^2*crossSquare u v) (𝓝 0) (𝓝 (sizeSq (u-v))) := by
    simpa using (((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).pow 2).mul_const (crossSquare u v)).const_add (sizeSq (u-v))
  have hden := ((radius_tendsto u).mul (radius_tendsto v)).mul (kinetic_denominator_tendsto u v)
  unfold kineticCoefficient
  have h := hnum.div hden (by norm_num : (1:ℝ)*1*2≠0)
  simp only [one_mul] at h
  convert h using 1

theorem relative_quadratic_limit (u v : Triple) :
    Tendsto (fun t : ℝ => (1-halfTrace (hemisphereChart (t • u)*(hemisphereChart (t • v))⁻¹))/t^2)
      (𝓝[≠] 0) (𝓝 (sizeSq (u-v)/2)) := by
  have hnonzero := (kinetic_denominator_tendsto u v).eventually
    (Ioi_mem_nhds (by norm_num : (0:ℝ)<2))
  apply (kinetic_coefficient_tendsto u v).mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [hnonzero.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t hden ht
  change t≠0 at ht
  rw [scaled_relative_defect u v t (ne_of_gt hden)]
  field_simp

/-- Temporal action at the IDENTITY gauge, not the Haar gauge integral or an
optimized/ground-normalized effective kinetic operator. -/
theorem temporal_identity_quadratic_limit (a b : Velocities) :
    Tendsto (fun t : ℝ => temporalAction (constantState a t) (constantState b t) 1/t^2)
      (𝓝[≠] 0) (𝓝 (32*∑ i : Fin 3,sizeSq (a i-b i))) := by
  have h := tendsto_finset_sum Finset.univ (fun e (_ : e∈(Finset.univ : Finset SpatialEdge)) =>
    relative_quadratic_limit (a e.2) (b e.2))
  have hf : (fun t : ℝ => temporalAction (constantState a t) (constantState b t) 1/t^2)=
      (fun t => ∑ e : SpatialEdge,(1-halfTrace (hemisphereChart (t • a e.2)*(hemisphereChart (t • b e.2))⁻¹))/t^2) := by
    funext t
    simp only [temporalAction,temporalWord,constantState,Pi.one_apply,mul_one,inv_one,Finset.sum_div]
  rw [hf]
  convert h using 1
  simp only [SpatialEdge,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ]
  norm_num only [SpatialVertex,Fintype.card_fun,Fintype.card_fin,ZMod.card,show 4^3=64 by norm_num]
  simp only [← Finset.sum_div]
  congr 1
  ring



theorem spatial_quadratic_vanish (a : Velocities) :
    Tendsto (fun t : ℝ => spatialAction (constantState a t)/t^2) (𝓝[≠] 0) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t^2) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).pow 2
  have h : Tendsto (fun t : ℝ => t^2*coefficient a t) (𝓝[≠] 0) (𝓝 ((0:ℝ)*coefficient a 0)) :=
    (ht.mul (coefficient_tendsto a)).mono_left nhdsWithin_le_nhds
  have hz : (0:ℝ)*coefficient a 0=0 := by ring
  rw [hz] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change t≠0 at ht
  rw [spatial_action_exact]
  field_simp
  <;> ring

theorem halfAction_identity_quadratic_limit (a b : Velocities) :
    Tendsto (fun t : ℝ => halfAction (constantState a t) (constantState b t) 1/t^2)
      (𝓝[≠] 0) (𝓝 (32*∑ i : Fin 3,sizeSq (a i-b i))) := by
  have h := (((spatial_quadratic_vanish a).div_const 2).add
    ((spatial_quadratic_vanish b).div_const 2)).add (temporal_identity_quadratic_limit a b)
  convert h using 1
  · funext t
    unfold halfAction
    ring
  · ring

theorem temporal_self (U : State) : temporalAction U U 1=0 := by
  unfold temporalAction temporalWord
  apply Finset.sum_eq_zero
  intro e _
  simp [SU2OpenLinkGaugeObstruction.halfTrace_one]

theorem halfAction_diagonal (a : Velocities) (t : ℝ) :
    halfAction (constantState a t) (constantState a t) 1=spatialAction (constantState a t) := by
  unfold halfAction
  rw [temporal_self]
  ring

theorem halfAction_diagonal_quartic_limit (p : Config) :
    Tendsto (fun t : ℝ => halfAction (constantState (configVelocity p) t) (constantState (configVelocity p) t) 1/t^4)
      (𝓝[≠] 0) (𝓝 (128*potential p)) := by
  simpa only [halfAction_diagonal] using nine_coordinate_quartic_limit p



/-- The precise quartic profile of the actual constant Wilson rays cannot be
normalized as a bare nine-dimensional Gibbs density. No kinetic operator,
Haar transverse marginal or actual stationary law is identified with it. -/
theorem limiting_profile_partition_eq_top (c : ℝ) (hc : 0≤c) :
    (∫⁻ p,ENNReal.ofReal (Real.exp (-c*coefficient (configVelocity p) 0))
      ∂SU2QuarticValleyNonintegrable.configMeasure)=⊤ := by
  have he (p : Config) : Real.exp (-c*coefficient (configVelocity p) 0)=
      SU2QuarticValleyNonintegrable.weight (128*c) p := by
    rw [coefficient_config]
    unfold SU2QuarticValleyNonintegrable.weight
    congr 1
    ring
  simp_rw [he]
  exact partition_eq_top (128*c) (by positivity)


end OperatorDerivativeRewrite.Foundation.PeriodicConstantQuarticJet
