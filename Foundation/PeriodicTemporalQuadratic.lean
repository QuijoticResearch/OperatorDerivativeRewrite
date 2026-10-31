import Foundation.PeriodicChargedSynthesis
import Foundation.SU2FourCurveJetTransfer
import Mathlib.Analysis.Calculus.Taylor
/-! The ACTUAL temporal Wilson slab around constant backgrounds. Exact word
factorization, full real-color second variations, charged Fourier gauge energy,
gauge covariance and the residual neutral zero mode are verified. Taylor reuse
gives punctured pointwise rescaled-action/Boltzmann limits at fixed velocities.
No Haar-integrated Gaussian limit, determinant, stationary spectral or mass-gap
conclusion is asserted. -/
noncomputable section
open scoped Quaternion Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.PeriodicTemporalQuadratic
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereJets SU2RootAdjoint
open SU2TraceHessianModel PeriodicTemporalSlab PeriodicWilsonSlab PeriodicFlatBackgroundHessian

def temporalGauge (Z : SpatialVertex → Triple) (t : ℝ) : Gauge := fun v => expLink (Z v) t

def temporalEnergy (h : Fin 3 → SU2) (X Y : Velocity) (Z : SpatialVertex → Triple) : ℝ :=
  ∑ e : SpatialEdge,sizeSq (X e-Y e-gaugeGradient h Z e)

theorem temporal_word (h : Fin 3 → SU2) (X Y : Velocity) (Z : SpatialVertex → Triple)
    (t : ℝ) (e : SpatialEdge) :
    temporalWord (state h X t) (state h Y t) (temporalGauge Z t) e=
      expLink (X e) t*expLink (rotate (h e.2) (Z (shift e.1 e.2))) t*
        (expLink (Y e) t)⁻¹*(expLink (Z e.1) t)⁻¹ := by
  unfold temporalWord state temporalGauge
  rw [← expLink_conjugate]
  group

private def wordAction (v : Fin 4 → Triple) : ℝ → ℝ :=
  fun t => 1-halfTrace (expLink (v 0) t*expLink (v 1) t*(expLink (v 2) t)⁻¹*(expLink (v 3) t)⁻¹)
private def wordSlope (v : Fin 4 → Triple) : ℝ → ℝ :=
  SU2FourWordVariation.actionSlope (SU2HemisphereJets.generator (v 0)) (SU2HemisphereJets.generator (v 1))
    (-SU2HemisphereJets.generator (v 2)) (-SU2HemisphereJets.generator (v 3))
private theorem word_first (v : Fin 4 → Triple) (t : ℝ) :
    HasDerivAt (wordAction v) (wordSlope v t) t := by
  unfold wordAction
  rw [word_action]
  exact SU2FourWordVariation.action_hasDerivAt _ _ _ _ t
private theorem word_second_slope (v : Fin 4 → Triple) :
    HasDerivAt (wordSlope v) (sizeSq (v 0+v 1-v 2-v 3)) 0 := by
  have he : deriv (wordAction v)=wordSlope v := funext (fun t => (word_first v t).deriv)
  have hd := SU2FourWordVariation.actionSlope_hasDerivAt
    (SU2HemisphereJets.generator (v 0)) (SU2HemisphereJets.generator (v 1))
    (-SU2HemisphereJets.generator (v 2)) (-SU2HemisphereJets.generator (v 3)) 0
  have hv := word_second (v 0) (v 1) (v 2) (v 3)
  change deriv (deriv (wordAction v)) 0=_ at hv
  change HasDerivAt (wordSlope v) _ 0 at hd
  rw [he,hd.deriv] at hv
  exact hv ▸ hd

private theorem family_first {ι : Type*} [Fintype ι] (v : ι → Fin 4 → Triple) (t : ℝ) :
    HasDerivAt (fun t => ∑ i,wordAction (v i) t) (∑ i,wordSlope (v i) t) t :=
  HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => word_first (v i) t)
private theorem family_second {ι : Type*} [Fintype ι] (v : ι → Fin 4 → Triple) :
    HasDerivAt (fun t => ∑ i,wordSlope (v i) t)
      (∑ i,sizeSq (v i 0+v i 1-v i 2-v i 3)) 0 :=
  HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => word_second_slope (v i))

private def edgeVectors (h : Fin 3 → SU2) (X Y : Velocity) (Z : SpatialVertex → Triple)
    (e : SpatialEdge) : Fin 4 → Triple :=
  ![X e,rotate (h e.2) (Z (shift e.1 e.2)),Y e,Z e.1]
private def faceVectors (h : Fin 3 → SU2) (X : Velocity) (p : SpatialFace) : Fin 4 → Triple :=
  ![X (p.val.1,p.val.2.1),rotate (h p.val.2.1) (X (shift p.val.1 p.val.2.1,p.val.2.2)),
    rotate (h p.val.2.2) (X (shift p.val.1 p.val.2.2,p.val.2.1)),X (p.val.1,p.val.2.2)]

private theorem temporal_model (h : Fin 3 → SU2) (X Y : Velocity) (Z : SpatialVertex → Triple) :
    (fun t => temporalAction (state h X t) (state h Y t) (temporalGauge Z t))=
      (fun t => ∑ e : SpatialEdge,wordAction (edgeVectors h X Y Z e) t) := by
  funext t
  unfold temporalAction
  apply Finset.sum_congr rfl
  intro e _
  rw [temporal_word]
  rfl
private theorem spatial_model (h : Fin 3 → SU2) (X : Velocity) (hc : ∀ i j,h i*h j=h j*h i) :
    (fun t => spatialAction (state h X t))=
      (fun t => ∑ p : SpatialFace,wordAction (faceVectors h X p) t) := by
  funext t
  unfold spatialAction
  apply Finset.sum_congr rfl
  intro p _
  rw [plaquette_word h X t p (hc _ _)]
  rfl

private theorem edge_energy (h : Fin 3 → SU2) (X Y : Velocity) (Z : SpatialVertex → Triple) :
    (∑ e : SpatialEdge,sizeSq (edgeVectors h X Y Z e 0+edgeVectors h X Y Z e 1-
      edgeVectors h X Y Z e 2-edgeVectors h X Y Z e 3))=temporalEnergy h X Y Z := by
  unfold temporalEnergy
  apply Finset.sum_congr rfl
  intro e _
  apply congrArg sizeSq
  ext i
  simp [edgeVectors,gaugeGradient]
  ring
private theorem face_energy (h : Fin 3 → SU2) (X : Velocity) :
    (∑ p : SpatialFace,sizeSq (faceVectors h X p 0+faceVectors h X p 1-
      faceVectors h X p 2-faceVectors h X p 3))=quadratic h X := by rfl

theorem temporal_second (h : Fin 3 → SU2) (X Y : Velocity) (Z : SpatialVertex → Triple) :
    deriv (deriv (fun t : ℝ => temporalAction (state h X t) (state h Y t) (temporalGauge Z t))) 0=
      temporalEnergy h X Y Z := by
  rw [temporal_model]
  have hf : deriv (fun t => ∑ e : SpatialEdge,wordAction (edgeVectors h X Y Z e) t)=
      (fun t => ∑ e : SpatialEdge,wordSlope (edgeVectors h X Y Z e) t) :=
    funext (fun t => (family_first (edgeVectors h X Y Z) t).deriv)
  rw [hf,(family_second (edgeVectors h X Y Z)).deriv,edge_energy]

theorem half_second (h : Fin 3 → SU2) (X Y : Velocity) (Z : SpatialVertex → Triple)
    (hc : ∀ i j,h i*h j=h j*h i) :
    deriv (deriv (fun t : ℝ => halfAction (state h X t) (state h Y t) (temporalGauge Z t))) 0=
      quadratic h X/2+temporalEnergy h X Y Z+quadratic h Y/2 := by
  have hm : (fun t : ℝ => halfAction (state h X t) (state h Y t) (temporalGauge Z t))=
      (fun t => (∑ p : SpatialFace,wordAction (faceVectors h X p) t)/2+
        (∑ e : SpatialEdge,wordAction (edgeVectors h X Y Z e) t)+
        (∑ p : SpatialFace,wordAction (faceVectors h Y p) t)/2) := by
    funext t
    unfold halfAction
    rw [congrFun (spatial_model h X hc) t,congrFun (spatial_model h Y hc) t,
      congrFun (temporal_model h X Y Z) t]
  rw [hm]
  have hf (t : ℝ) := ((family_first (faceVectors h X) t).div_const 2).add
    (family_first (edgeVectors h X Y Z) t) |>.add ((family_first (faceVectors h Y) t).div_const 2)
  rw [show deriv (fun t => (∑ p : SpatialFace,wordAction (faceVectors h X p) t)/2+
        (∑ e : SpatialEdge,wordAction (edgeVectors h X Y Z e) t)+
        (∑ p : SpatialFace,wordAction (faceVectors h Y p) t)/2)=
      (fun t => (∑ p : SpatialFace,wordSlope (faceVectors h X p) t)/2+
        (∑ e : SpatialEdge,wordSlope (edgeVectors h X Y Z e) t)+
        (∑ p : SpatialFace,wordSlope (faceVectors h Y p) t)/2) from funext (fun t => (hf t).deriv)]
  have hd := ((family_second (faceVectors h X)).div_const 2).add
    (family_second (edgeVectors h X Y Z)) |>.add ((family_second (faceVectors h Y)).div_const 2)
  change HasDerivAt (fun t => (∑ p : SpatialFace,wordSlope (faceVectors h X p) t)/2+
        (∑ e : SpatialEdge,wordSlope (edgeVectors h X Y Z e) t)+
        (∑ p : SpatialFace,wordSlope (faceVectors h Y p) t)/2) _ 0 at hd
  rw [hd.deriv,face_energy,edge_energy,face_energy]

theorem temporalEnergy_nonneg (h : Fin 3 → SU2) (X Y : Velocity) (Z : SpatialVertex → Triple) :
    0≤temporalEnergy h X Y Z := by
  unfold temporalEnergy
  apply Finset.sum_nonneg
  intro e _
  unfold sizeSq
  positivity

theorem temporalEnergy_gauge (h : Fin 3 → SU2) (X Y : Velocity) (Z A B : SpatialVertex → Triple) :
    temporalEnergy h (X+gaugeGradient h A) (Y+gaugeGradient h B) (Z+A-B)=
      temporalEnergy h X Y Z := by
  have hg (e : SpatialEdge) : gaugeGradient h (Z+A-B) e=
      gaugeGradient h Z e+gaugeGradient h A e-gaugeGradient h B e := by
    simp only [gaugeGradient,Pi.sub_apply,Pi.add_apply,rotate_sub,rotate_add]
    abel
  unfold temporalEnergy
  apply Finset.sum_congr rfl
  intro e _
  rw [hg]
  apply congrArg sizeSq
  simp only [Pi.add_apply]
  abel

theorem halfEnergy_gauge (h : Fin 3 → SU2) (X Y : Velocity) (Z A B : SpatialVertex → Triple)
    (hc : ∀ i j,h i*h j=h j*h i) :
    quadratic h (X+gaugeGradient h A)/2+
        temporalEnergy h (X+gaugeGradient h A) (Y+gaugeGradient h B) (Z+A-B)+
        quadratic h (Y+gaugeGradient h B)/2=
      quadratic h X/2+temporalEnergy h X Y Z+quadratic h Y/2 := by
  rw [quadratic_add_gauge h X A hc,quadratic_add_gauge h Y B hc,temporalEnergy_gauge]

open PeriodicChargedFourier PeriodicChargedSynthesis

def chargedResidual (α : Fin 3 → ℝ) (f g : SpatialEdge → ℂ) (Z : SpatialVertex → ℂ)
    (e : SpatialEdge) : ℂ :=
  f e-g e-Z e.1+phase (α e.2)*Z (shift e.1 e.2)

theorem charged_residual (α : Fin 3 → ℝ) (f g : SpatialEdge → ℂ) (Z : SpatialVertex → ℂ)
    (e : SpatialEdge) :
    encoded f e-encoded g e-gaugeGradient (background α) (fun v => lift (Z v)) e=
      lift (chargedResidual α f g Z e) := by
  simp only [encoded,gaugeGradient,background,rotate_lift]
  rw [← lift_sub,← lift_sub,← lift_sub]
  apply congrArg lift
  unfold chargedResidual
  ring

theorem residual_coefficients (α : Fin 3 → ℝ) (f g : SpatialEdge → ℂ) (Z : SpatialVertex → ℂ)
    (k : Frequency) (i : Fin 3) :
    coefficients (fun v => chargedResidual α f g Z (v,i)) k=
      modeCoefficients f k i-modeCoefficients g k i+delta α k i*coefficients Z k := by
  change coefficients (fun v => f (v,i)-g (v,i)-Z v+phase (α i)*Z (shift v i)) k=_
  rw [coefficients_add,coefficients_sub,coefficients_sub,coefficients_mul,coefficients_shift Z k i]
  unfold delta modeCoefficients
  ring

theorem charged_temporal (α : Fin 3 → ℝ) (f g : SpatialEdge → ℂ) (Z : SpatialVertex → ℂ) :
    temporalEnergy (background α) (encoded f) (encoded g) (fun v => lift (Z v))=
      64*∑ k : Frequency,∑ i : Fin 3,Complex.normSq
        (modeCoefficients f k i-modeCoefficients g k i+delta α k i*coefficients Z k) := by
  unfold temporalEnergy
  simp_rw [charged_residual,lift_size]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  have hp (i : Fin 3) :
      (∑ v : SpatialVertex,Complex.normSq (chargedResidual α f g Z (v,i)))=
      64*∑ k : Frequency,Complex.normSq
        (modeCoefficients f k i-modeCoefficients g k i+delta α k i*coefficients Z k) := by
    rw [parseval]
    simp_rw [residual_coefficients]
  simp_rw [hp]
  rw [← Finset.mul_sum,Finset.sum_comm]

theorem charged_gauge_energy (α : Fin 3 → ℝ) (Z : SpatialVertex → ℂ) :
    temporalEnergy (background α) (encoded (fun _ => 0)) (encoded (fun _ => 0)) (fun v => lift (Z v))=
      64*∑ k : Frequency,symbolSize α k*Complex.normSq (coefficients Z k) := by
  rw [charged_temporal]
  have hz (k : Frequency) (i : Fin 3) : modeCoefficients (fun _ => 0) k i=0 := by
    simp [modeCoefficients,coefficients]
  simp_rw [hz,sub_self,zero_add,map_mul,← Finset.sum_mul]
  rfl

theorem charged_gauge_injective (α : Fin 3 → ℝ) (Z : SpatialVertex → ℂ)
    (hhol : ∃ i,phase (α i)^4≠1)
    (hE : temporalEnergy (background α) (encoded (fun _ => 0)) (encoded (fun _ => 0))
      (fun v => lift (Z v))=0) : Z=0 := by
  rw [charged_gauge_energy] at hE
  have hs : (∑ k : Frequency,symbolSize α k*Complex.normSq (coefficients Z k))=0 := by
    linarith
  have ha (k : Frequency) : symbolSize α k*Complex.normSq (coefficients Z k)=0 := by
    have hi := Finset.single_le_sum
      (fun j (_ : j∈Finset.univ) => mul_nonneg (symbolSize_nonneg α j) (Complex.normSq_nonneg (coefficients Z j)))
      (Finset.mem_univ k)
    exact le_antisymm (hi.trans_eq hs) (mul_nonneg (symbolSize_nonneg α k) (Complex.normSq_nonneg _))
  apply coefficients_injective
  funext k
  have hn : Complex.normSq (coefficients Z k)=0 :=
    (mul_eq_zero.mp (ha k)).resolve_left (ne_of_gt (symbolSize_pos_of_holonomy α k hhol))
  have hz := Complex.normSq_eq_zero.mp hn
  simpa [coefficients] using hz


def neutral (x : ℝ) : Triple := ![x,0,0]

theorem rotate_neutral (α x : ℝ) :
    rotate (SU2JointPlaquetteCubic.axis 0 α) (neutral x)=neutral x := by
  let c := SU2JointPlaquetteCubic.axis 0 α
  have hr : recover (c : SU2TraceHessianModel.M2)=SU2JointPlaquetteCubic.axisRaw 0 α := recover_repr _
  change ![(recover (c : SU2TraceHessianModel.M2)*(⟨0,x,0,0⟩ : ℍ)*star (recover (c : SU2TraceHessianModel.M2))).imI,
    (recover (c : SU2TraceHessianModel.M2)*(⟨0,x,0,0⟩ : ℍ)*star (recover (c : SU2TraceHessianModel.M2))).imJ,
    (recover (c : SU2TraceHessianModel.M2)*(⟨0,x,0,0⟩ : ℍ)*star (recover (c : SU2TraceHessianModel.M2))).imK]=_
  rw [hr]
  ext i
  fin_cases i <;> norm_num [SU2JointPlaquetteCubic.axisRaw,neutral,Quaternion.re_mul,
    Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul]
  linear_combination x * (Real.sin_sq_add_cos_sq α)

theorem neutral_gauge_zero (α : Fin 3 → ℝ) (x : ℝ) :
    gaugeGradient (background α) (fun _ => neutral x)=0 := by
  funext e
  simp [gaugeGradient,background,rotate_neutral]

theorem neutral_temporal_zero (α : Fin 3 → ℝ) (x : ℝ) :
    temporalEnergy (background α) 0 0 (fun _ => neutral x)=0 := by
  simp [temporalEnergy,neutral_gauge_zero,sizeSq]

theorem full_temporal_noncoercive (α : Fin 3 → ℝ) :
    ∃ Z : SpatialVertex → Triple,Z≠0 ∧ temporalEnergy (background α) 0 0 Z=0 := by
  refine ⟨(fun _ => neutral 1),?_,neutral_temporal_zero α 1⟩
  intro h
  have he := congrArg (fun Z : SpatialVertex → Triple => Z (fun _ => 0) 0) h
  norm_num [neutral] at he

open Filter
open scoped Topology

private theorem word_contDiff (v : Fin 4 → Triple) : ContDiff ℝ 2 (wordAction v) := by
  have he : wordAction v=SU2FourCurveJetTransfer.traceAction ∘
      SU2FourCurveJetTransfer.model (fun i => frame (v i)) := by
    funext t
    rw [Function.comp_apply,SU2FourCurveJetTransfer.trace_model]
    exact congrFun (word_action (v 0) (v 1) (v 2) (v 3)) t
  rw [he]
  exact SU2FourCurveJetTransfer.traceAction_contDiff.comp (SU2FourCurveJetTransfer.model_contDiff _)

private theorem word_zero (v : Fin 4 → Triple) : wordAction v 0=0 := by
  simp [wordAction,expLink_zero,SU2OpenLinkGaugeObstruction.halfTrace_one]
private theorem word_first_zero (v : Fin 4 → Triple) : deriv (wordAction v) 0=0 := by
  rw [(word_first v 0).deriv]
  exact SU2FourWordVariation.signed_first_zero (frame (v 0)) (frame (v 1)) (frame (v 2)) (frame (v 3))
private theorem word_second_zero (v : Fin 4 → Triple) :
    deriv (deriv (wordAction v)) 0=sizeSq (v 0+v 1-v 2-v 3) :=
  word_second _ _ _ _

private theorem word_limit (v : Fin 4 → Triple) :
    Tendsto (fun t : ℝ => wordAction v t/t^2) (𝓝[≠] 0)
      (𝓝 (sizeSq (v 0+v 1-v 2-v 3)/2)) := by
  let q := sizeSq (v 0+v 1-v 2-v 3)/2
  have hp (t : ℝ) : taylorWithinEval (wordAction v) 2 Set.univ 0 t=q*t^2 := by
    simp [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_univ,
      iteratedDeriv_succ,iteratedDeriv_zero,word_zero,word_first_zero,word_second_zero,q]
    ring
  have hr : (fun t : ℝ => wordAction v t-q*t^2) =o[𝓝 0] (fun t : ℝ => t^2) := by
    simpa only [hp,sub_zero] using taylor_isLittleO_univ (x₀ := 0) (n := 2) (word_contDiff v)
  have hh := (hr.tendsto_div_nhds_zero.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).add_const q
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : t≠0 := ht
  field_simp [hn]
  ring

theorem temporal_scaled_limit (h : Fin 3 → SU2) (X Y : Velocity) (Z : SpatialVertex → Triple) :
    Tendsto (fun t : ℝ => temporalAction (state h X t) (state h Y t) (temporalGauge Z t)/t^2)
      (𝓝[≠] 0) (𝓝 (temporalEnergy h X Y Z/2)) := by
  have hh := tendsto_finsetSum Finset.univ (fun e (_ : e∈(Finset.univ : Finset SpatialEdge)) =>
    word_limit (edgeVectors h X Y Z e))
  have hf : (fun t : ℝ => temporalAction (state h X t) (state h Y t) (temporalGauge Z t)/t^2)=
      (fun t => ∑ e : SpatialEdge,wordAction (edgeVectors h X Y Z e) t/t^2) := by
    funext t
    rw [congrFun (temporal_model h X Y Z) t,Finset.sum_div]
  rw [hf]
  convert hh using 1
  rw [← Finset.sum_div,edge_energy]

theorem spatial_scaled_limit (h : Fin 3 → SU2) (X : Velocity) (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => spatialAction (state h X t)/t^2) (𝓝[≠] 0) (𝓝 (quadratic h X/2)) := by
  have hh := tendsto_finsetSum Finset.univ (fun p (_ : p∈(Finset.univ : Finset SpatialFace)) =>
    word_limit (faceVectors h X p))
  have hf : (fun t : ℝ => spatialAction (state h X t)/t^2)=
      (fun t => ∑ p : SpatialFace,wordAction (faceVectors h X p) t/t^2) := by
    funext t
    rw [congrFun (spatial_model h X hc) t,Finset.sum_div]
  rw [hf]
  convert hh using 1
  rw [← Finset.sum_div,face_energy]

theorem half_scaled_limit (h : Fin 3 → SU2) (X Y : Velocity) (Z : SpatialVertex → Triple)
    (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => halfAction (state h X t) (state h Y t) (temporalGauge Z t)/t^2)
      (𝓝[≠] 0) (𝓝 ((quadratic h X/2+temporalEnergy h X Y Z+quadratic h Y/2)/2)) := by
  have hh := (((spatial_scaled_limit h X hc).div_const 2).add (temporal_scaled_limit h X Y Z)).add
    ((spatial_scaled_limit h Y hc).div_const 2)
  convert hh using 1
  · funext t
    unfold halfAction
    ring
  · ring

theorem weight_scaled_limit (h : Fin 3 → SU2) (X Y : Velocity) (Z : SpatialVertex → Triple)
    (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => PeriodicWilsonSlab.weight (1/t^2) (state h X t) (state h Y t) (temporalGauge Z t))
      (𝓝[≠] 0) (𝓝 (Real.exp (-((quadratic h X/2+temporalEnergy h X Y Z+quadratic h Y/2)/2)))) := by
  have hh := (Real.continuous_exp.tendsto (-((quadratic h X/2+temporalEnergy h X Y Z+quadratic h Y/2)/2))).comp
    (half_scaled_limit h X Y Z hc).neg
  convert hh using 1
  funext t
  unfold PeriodicWilsonSlab.weight
  congr 1
  ring

end OperatorDerivativeRewrite.Foundation.PeriodicTemporalQuadratic
