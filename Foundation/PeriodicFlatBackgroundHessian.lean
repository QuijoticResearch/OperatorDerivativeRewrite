import Foundation.PeriodicConstantRootLimit
import Foundation.SU2FourWordVariation
/-! The actual periodic Wilson spatial Hessian at commuting constant SU(2)
backgrounds. Exact nonlinear plaquette factorization gives the adjoint-shifted
curl, the actual gauge tangent and its quadratic invariance. A rational
noncentral winding exhibits a constant charged field with zero ordinary curl
but strictly positive actual Hessian. No Fourier spectrum, integrated transfer
limit, ground moment estimate or physical mass gap is asserted. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.PeriodicFlatBackgroundHessian
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereJets SU2RootAdjoint
open SU2TraceHessianModel SU2MatrixExponentialBridge SU2ExponentialMembership
open PeriodicTemporalSlab PeriodicWilsonSlab

private def matrixUnit (c : SU2) : M2ˣ where
  val := c
  inv := (c⁻¹ : SU2)
  val_inv := by change ((c*c⁻¹ : SU2) : M2)=1; simp
  inv_val := by change ((c⁻¹*c : SU2) : M2)=1; simp

def expLink (u : Triple) (t : ℝ) : SU2 :=
  ⟨NormedSpace.exp (t • SU2HemisphereJets.generator u),scaled_algebraElement_exp_mem t (frame u)⟩

theorem generator_neg (u : Triple) : SU2HemisphereJets.generator (-u)= -SU2HemisphereJets.generator u := by
  have h := frame_smul u (-1)
  simp only [neg_one_smul] at h
  unfold SU2HemisphereJets.generator
  rw [h,SU2FourWordVariation.algebraElement_neg]

theorem expLink_inv (u : Triple) (t : ℝ) : (expLink u t)⁻¹=expLink (-u) t := by
  apply Subtype.ext
  change (NormedSpace.exp (t • SU2HemisphereJets.generator u))ᴴ=NormedSpace.exp (t • SU2HemisphereJets.generator (-u))
  rw [← Matrix.exp_conjTranspose,generator_neg]
  simp [Matrix.conjTranspose_smul,SU2HemisphereJets.generator,algebraElement_skewHermitian]

theorem expLink_conjugate (c : SU2) (u : Triple) (t : ℝ) :
    c*expLink u t*c⁻¹=expLink (rotate c u) t := by
  apply Subtype.ext
  have he : (c : M2)*(t • SU2HemisphereJets.generator u)*(c⁻¹ : SU2)=t • SU2HemisphereJets.generator (rotate c u) := by
    rw [generator_rotate]
    unfold CubeMixedForm.adjointVelocity
    rw [mul_smul_comm,smul_mul_assoc]
    rfl
  have hh := Matrix.exp_units_conj (matrixUnit c) (t • SU2HemisphereJets.generator u)
  change NormedSpace.exp ((c : M2)*(t • SU2HemisphereJets.generator u)*(c⁻¹ : SU2))=
    (c : M2)*NormedSpace.exp (t • SU2HemisphereJets.generator u)*(c⁻¹ : SU2) at hh
  rw [he] at hh
  exact hh.symm

theorem flat_word (A B E F G H : SU2) (h : A*B=B*A) :
    (E*A)*(F*B)*(G*A)⁻¹*(H*B)⁻¹=
      E*(A*F*A⁻¹)*(B*G*B⁻¹)⁻¹*H⁻¹ := by
  have hc : A*B*A⁻¹=B := by rw [h]; group
  calc
    _ = E*(A*F*A⁻¹)*(A*B*A⁻¹)*G⁻¹*B⁻¹*H⁻¹ := by group
    _ = _ := by rw [hc]; group

abbrev Velocity := SpatialEdge → Triple

def state (h : Fin 3 → SU2) (X : Velocity) (t : ℝ) : State :=
  fun e => expLink (X e) t*h e.2

def covariantCurl (h : Fin 3 → SU2) (X : Velocity) (v : SpatialVertex) (i j : Fin 3) : Triple :=
  X (v,i)+rotate (h i) (X (shift v i,j))-rotate (h j) (X (shift v j,i))-X (v,j)

theorem plaquette_word (h : Fin 3 → SU2) (X : Velocity) (t : ℝ) (p : SpatialFace)
    (hc : h p.val.2.1*h p.val.2.2=h p.val.2.2*h p.val.2.1) :
    spatialWord (state h X t) p=
      expLink (X (p.val.1,p.val.2.1)) t*
      expLink (rotate (h p.val.2.1) (X (shift p.val.1 p.val.2.1,p.val.2.2))) t*
      (expLink (rotate (h p.val.2.2) (X (shift p.val.1 p.val.2.2,p.val.2.1))) t)⁻¹*
      (expLink (X (p.val.1,p.val.2.2)) t)⁻¹ := by
  unfold spatialWord state
  rw [flat_word _ _ _ _ _ _ hc,expLink_conjugate,expLink_conjugate]

private theorem frame_add (u v : Triple) : frame (u+v)=frame u+frame v := by
  ext i
  fin_cases i <;> simp [frame] <;> ring

private theorem frame_neg (u : Triple) : frame (-u)= -frame u := by
  have h := frame_smul u (-1)
  simpa only [neg_one_smul] using h

theorem word_action (u v w z : Triple) :
    (fun t : ℝ => 1-halfTrace (expLink u t*expLink v t*(expLink w t)⁻¹*(expLink z t)⁻¹))=
      SU2FourWordVariation.action (SU2HemisphereJets.generator u) (SU2HemisphereJets.generator v) (-SU2HemisphereJets.generator w) (-SU2HemisphereJets.generator z) := by
  funext t
  rw [expLink_inv,expLink_inv]
  change wilson (NormedSpace.exp (t • SU2HemisphereJets.generator u)*NormedSpace.exp (t • SU2HemisphereJets.generator v)*
    NormedSpace.exp (t • SU2HemisphereJets.generator (-w))*NormedSpace.exp (t • SU2HemisphereJets.generator (-z)))=_
  rw [generator_neg,generator_neg]
  rfl

theorem word_second (u v w z : Triple) :
    deriv (deriv (fun t : ℝ => 1-halfTrace
      (expLink u t*expLink v t*(expLink w t)⁻¹*(expLink z t)⁻¹))) 0=sizeSq (u+v-w-z) := by
  rw [word_action]
  have h := SU2FourWordVariation.signed_second_zero (frame u) (frame v) (frame w) (frame z)
  have he : frame u+frame v-frame w-frame z=frame (u+v-w-z) := by
    simp only [sub_eq_add_neg,frame_add,frame_neg]
  rw [he,lengthSq_frame] at h
  change deriv (deriv (SU2FourWordVariation.action (SU2HemisphereJets.generator u) (SU2HemisphereJets.generator v) (-SU2HemisphereJets.generator w) (-SU2HemisphereJets.generator z))) 0=_
  exact h.trans (by ring)

theorem plaquette_second (h : Fin 3 → SU2) (X : Velocity) (p : SpatialFace)
    (hc : h p.val.2.1*h p.val.2.2=h p.val.2.2*h p.val.2.1) :
    deriv (deriv (fun t : ℝ => 1-halfTrace (spatialWord (state h X t) p))) 0=
      sizeSq (covariantCurl h X p.val.1 p.val.2.1 p.val.2.2) := by
  have he : (fun t : ℝ => 1-halfTrace (spatialWord (state h X t) p))=
      (fun t => 1-halfTrace
        (expLink (X (p.val.1,p.val.2.1)) t*
        expLink (rotate (h p.val.2.1) (X (shift p.val.1 p.val.2.1,p.val.2.2))) t*
        (expLink (rotate (h p.val.2.2) (X (shift p.val.1 p.val.2.2,p.val.2.1))) t)⁻¹*
        (expLink (X (p.val.1,p.val.2.2)) t)⁻¹)) := by
    funext t
    rw [plaquette_word h X t p hc]
  rw [he,word_second]
  rfl


private theorem generator_injective : Function.Injective SU2HemisphereJets.generator := by
  intro u v huv
  have he : SU2HemisphereChart.rawPoint u=SU2HemisphereChart.rawPoint v := by
    apply repr_injective
    rw [rawPoint_matrix,rawPoint_matrix,huv]
  funext i
  fin_cases i
  · exact congrArg (fun q : Quaternion ℝ => q.imI) he
  · exact congrArg (fun q : Quaternion ℝ => q.imJ) he
  · exact congrArg (fun q : Quaternion ℝ => q.imK) he

theorem rotate_mul (a b : SU2) (u : Triple) : rotate (a*b) u=rotate a (rotate b u) := by
  apply generator_injective
  rw [generator_rotate,generator_rotate,generator_rotate]
  unfold CubeMixedForm.adjointVelocity
  change ((a : M2)*(b : M2))*SU2HemisphereJets.generator u*((a : M2)*(b : M2))ᴴ=
    (a : M2)*((b : M2)*SU2HemisphereJets.generator u*(b : M2)ᴴ)*(a : M2)ᴴ
  rw [Matrix.conjTranspose_mul]
  noncomm_ring

theorem rotate_neg (c : SU2) (u : Triple) : rotate c (-u)= -rotate c u := by
  simpa only [neg_one_smul] using rotate_smul c (-1) u

theorem rotate_sub (c : SU2) (u v : Triple) : rotate c (u-v)=rotate c u-rotate c v := by
  simp only [sub_eq_add_neg,rotate_add,rotate_neg]

def gaugeGradient (h : Fin 3 → SU2) (Z : SpatialVertex → Triple) : Velocity :=
  fun e => Z e.1-rotate (h e.2) (Z (shift e.1 e.2))

theorem curl_gauge_zero (h : Fin 3 → SU2) (Z : SpatialVertex → Triple) (v : SpatialVertex) (i j : Fin 3)
    (hc : h i*h j=h j*h i) : covariantCurl h (gaugeGradient h Z) v i j=0 := by
  have hs : shift (shift v i) j=shift (shift v j) i := by
    funext k
    unfold shift
    abel
  have hr (u : Triple) : rotate (h i) (rotate (h j) u)=rotate (h j) (rotate (h i) u) := by
    rw [← rotate_mul,← rotate_mul,hc]
  unfold covariantCurl gaugeGradient
  rw [rotate_sub,rotate_sub,hs,hr]
  abel

def quadratic (h : Fin 3 → SU2) (X : Velocity) : ℝ :=
  ∑ p : SpatialFace,sizeSq (covariantCurl h X p.val.1 p.val.2.1 p.val.2.2)

theorem quadratic_nonneg (h : Fin 3 → SU2) (X : Velocity) : 0≤quadratic h X :=
  Finset.sum_nonneg (fun _ _ => sizeSq_nonneg _)

theorem quadratic_gauge_zero (h : Fin 3 → SU2) (Z : SpatialVertex → Triple)
    (hc : ∀ i j,h i*h j=h j*h i) : quadratic h (gaugeGradient h Z)=0 := by
  unfold quadratic
  apply Finset.sum_eq_zero
  intro p _
  rw [curl_gauge_zero h Z _ _ _ (hc _ _)]
  simp [sizeSq]

private def vectors (h : Fin 3 → SU2) (X : Velocity) (p : SpatialFace) : Fin 4 → Triple :=
  ![X (p.val.1,p.val.2.1),rotate (h p.val.2.1) (X (shift p.val.1 p.val.2.1,p.val.2.2)),
    rotate (h p.val.2.2) (X (shift p.val.1 p.val.2.2,p.val.2.1)),X (p.val.1,p.val.2.2)]

private def faceAction (v : Fin 4 → Triple) : ℝ → ℝ :=
  SU2FourWordVariation.action (SU2HemisphereJets.generator (v 0)) (SU2HemisphereJets.generator (v 1))
    (-SU2HemisphereJets.generator (v 2)) (-SU2HemisphereJets.generator (v 3))

private def faceSlope (v : Fin 4 → Triple) : ℝ → ℝ :=
  SU2FourWordVariation.actionSlope (SU2HemisphereJets.generator (v 0)) (SU2HemisphereJets.generator (v 1))
    (-SU2HemisphereJets.generator (v 2)) (-SU2HemisphereJets.generator (v 3))

private theorem spatial_action_model (h : Fin 3 → SU2) (X : Velocity)
    (hc : ∀ i j,h i*h j=h j*h i) :
    (fun t : ℝ => spatialAction (state h X t))=(fun t => ∑ p : SpatialFace,faceAction (vectors h X p) t) := by
  funext t
  unfold spatialAction
  apply Finset.sum_congr rfl
  intro p _
  rw [plaquette_word h X t p (hc _ _)]
  exact congrFun (word_action _ _ _ _) t

private theorem face_first (v : Fin 4 → Triple) (t : ℝ) :
    HasDerivAt (faceAction v) (faceSlope v t) t :=
  SU2FourWordVariation.action_hasDerivAt _ _ _ _ t

private theorem face_second (v : Fin 4 → Triple) :
    HasDerivAt (faceSlope v) (sizeSq (v 0+v 1-v 2-v 3)) 0 := by
  have hd := SU2FourWordVariation.actionSlope_hasDerivAt
    (SU2HemisphereJets.generator (v 0)) (SU2HemisphereJets.generator (v 1))
    (-SU2HemisphereJets.generator (v 2)) (-SU2HemisphereJets.generator (v 3)) 0
  have he := SU2FourWordVariation.signed_slope_second_zero (frame (v 0)) (frame (v 1)) (frame (v 2)) (frame (v 3))
  have hf : frame (v 0)+frame (v 1)-frame (v 2)-frame (v 3)=frame (v 0+v 1-v 2-v 3) := by
    simp only [sub_eq_add_neg,frame_add,frame_neg]
  rw [hf,lengthSq_frame] at he
  have heq : -traceReal (SU2FourWordVariation.pathSecond
      (SU2HemisphereJets.generator (v 0)) (SU2HemisphereJets.generator (v 1))
      (-SU2HemisphereJets.generator (v 2)) (-SU2HemisphereJets.generator (v 3)) 0)/2=
      sizeSq (v 0+v 1-v 2-v 3) := by
    change -traceReal (SU2FourWordVariation.pathSecond
      (algebraElement (frame (v 0))) (algebraElement (frame (v 1)))
      (-algebraElement (frame (v 2))) (-algebraElement (frame (v 3))) 0)/2=_
    linarith only [he]
  rw [heq] at hd
  exact hd

theorem spatial_second (h : Fin 3 → SU2) (X : Velocity) (hc : ∀ i j,h i*h j=h j*h i) :
    deriv (deriv (fun t : ℝ => spatialAction (state h X t))) 0=quadratic h X := by
  rw [spatial_action_model h X hc]
  have hf (t : ℝ) : HasDerivAt (fun t => ∑ p : SpatialFace,faceAction (vectors h X p) t)
      (∑ p : SpatialFace,faceSlope (vectors h X p) t) t :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun p _ => face_first (vectors h X p) t)
  rw [show deriv (fun t => ∑ p : SpatialFace,faceAction (vectors h X p) t)=
    (fun t => ∑ p : SpatialFace,faceSlope (vectors h X p) t) from funext (fun t => (hf t).deriv)]
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun p (_ : p∈(Finset.univ : Finset SpatialFace)) => face_second (vectors h X p))
  rw [hd.deriv]
  rfl


theorem expLink_zero (u : Triple) : expLink u 0=1 := by
  apply Subtype.ext
  simp [expLink]

theorem state_zero (h : Fin 3 → SU2) (X : Velocity) : state h X 0=(fun e => h e.2) := by
  funext e
  simp only [state,expLink_zero,one_mul]

theorem spatial_base_zero (h : Fin 3 → SU2) (X : Velocity) (hc : ∀ i j,h i*h j=h j*h i) :
    spatialAction (state h X 0)=0 := by
  unfold spatialAction
  apply Finset.sum_eq_zero
  intro p _
  rw [plaquette_word h X 0 p (hc _ _)]
  simp [expLink_zero,SU2OpenLinkGaugeObstruction.halfTrace_one]

theorem spatial_gauge_second_zero (h : Fin 3 → SU2) (Z : SpatialVertex → Triple)
    (hc : ∀ i j,h i*h j=h j*h i) :
    deriv (deriv (fun t : ℝ => spatialAction (state h (gaugeGradient h Z) t))) 0=0 := by
  rw [spatial_second h _ hc,quadratic_gauge_zero h Z hc]

theorem rotate_one (u : Triple) : rotate (1 : SU2) u=u := by
  apply generator_injective
  rw [generator_rotate]
  change (1 : M2)*SU2HemisphereJets.generator u*(1 : M2)ᴴ=SU2HemisphereJets.generator u
  simp

private def rawTwist : QuaternionAngularHaar.Group := ⟨⟨3/5,4/5,0,0⟩,by
  rw [Unitary.mem_iff]
  constructor <;> norm_num [Quaternion.star_mul_self,Quaternion.self_mul_star,Quaternion.normSq_def'] <;> rfl⟩

private def twist : SU2 := hom rawTwist
private def background (i : Fin 3) : SU2 := if i=0 then twist else 1
private def velocity : Velocity := fun e => if e.2=1 then ![0,1,0] else 0

private theorem background_commutes (i j : Fin 3) : background i*background j=background j*background i := by
  by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp [background,hi,hj]

private theorem twist_rotate : rotate twist ![0,1,0]=![0,-7/25,24/25] := by
  have hr : recover (twist : M2)=(⟨3/5,4/5,0,0⟩ : Quaternion ℝ) := recover_repr _
  change ![(recover (twist : M2)*(⟨0,0,1,0⟩ : Quaternion ℝ)*star (recover (twist : M2))).imI,
    (recover (twist : M2)*(⟨0,0,1,0⟩ : Quaternion ℝ)*star (recover (twist : M2))).imJ,
    (recover (twist : M2)*(⟨0,0,1,0⟩ : Quaternion ℝ)*star (recover (twist : M2))).imK]=_
  rw [hr]
  norm_num [Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul]

private theorem winding_trace :
    halfTrace (PeriodicSpatialHolonomy.winding (fun e => background e.2) (fun _ => 0) 0)= -527/625 := by
  change halfTrace (twist*twist*twist*twist)=_
  have he : twist*twist*twist*twist=hom (rawTwist*rawTwist*rawTwist*rawTwist) := by simp only [twist,map_mul]
  rw [he,halfTrace_map]
  change (((rawTwist : Quaternion ℝ)*(rawTwist : Quaternion ℝ)*(rawTwist : Quaternion ℝ)*(rawTwist : Quaternion ℝ)).re)=_
  norm_num [rawTwist,Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul]

theorem constant_mode_obstruction :
    ∃ (h : Fin 3 → SU2) (a : Fin 3 → Triple),
      (∀ i j,h i*h j=h j*h i) ∧
      (∀ v i j,covariantCurl (fun _ => 1) (fun e => a e.2) v i j=0) ∧
      0<deriv (deriv (fun t : ℝ => spatialAction (state h (fun e => a e.2) t))) 0 ∧
      halfTrace (PeriodicSpatialHolonomy.winding (fun e => h e.2) (fun _ => 0) 0)= -527/625 := by
  refine ⟨background,(fun i => if i=1 then ![0,1,0] else 0),background_commutes,?_,?_,winding_trace⟩
  · intro v i j
    unfold covariantCurl
    rw [rotate_one,rotate_one]
    abel
  · change 0<deriv (deriv (fun t : ℝ => spatialAction (state background velocity t))) 0
    rw [spatial_second background velocity background_commutes]
    let p : SpatialFace := ⟨((fun _ => 0),(0,1)),by decide⟩
    have hp : sizeSq (covariantCurl background velocity p.val.1 p.val.2.1 p.val.2.2)=64/25 := by
      norm_num [p,covariantCurl,background,velocity,rotate_one,twist_rotate,sizeSq]
    have hh := Finset.single_le_sum (fun p (_ : p∈Finset.univ) =>
      sizeSq_nonneg (covariantCurl background velocity p.val.1 p.val.2.1 p.val.2.2)) (Finset.mem_univ p)
    change sizeSq (covariantCurl background velocity p.val.1 p.val.2.1 p.val.2.2)≤quadratic background velocity at hh
    rw [hp] at hh
    exact (by norm_num : (0 : ℝ)<64/25).trans_le hh


private theorem generator_sub (u v : Triple) :
    SU2HemisphereJets.generator (u-v)=SU2HemisphereJets.generator u-SU2HemisphereJets.generator v := by
  have hf : frame (u-v)=frame u-frame v := by simp only [sub_eq_add_neg,frame_add,frame_neg]
  unfold SU2HemisphereJets.generator
  rw [hf]
  simp only [sub_eq_add_neg,SU2FourWordVariation.algebraElement_add,SU2FourWordVariation.algebraElement_neg]

def gaugeCurve (h : Fin 3 → SU2) (Z : SpatialVertex → Triple) (e : SpatialEdge) (t : ℝ) : M2 :=
  PeriodicSlabGauge.gaugeAction (fun v => expLink (Z v) t) (fun e => h e.2) e

theorem gauge_tangent (h : Fin 3 → SU2) (Z : SpatialVertex → Triple) (e : SpatialEdge) :
    HasDerivAt (gaugeCurve h Z e)
      (SU2HemisphereJets.generator (gaugeGradient h Z e)*(h e.2 : M2)) 0 := by
  have he : gaugeCurve h Z e=
      (fun t => NormedSpace.exp (t • SU2HemisphereJets.generator (Z e.1))*(h e.2 : M2)*
        NormedSpace.exp (t • SU2HemisphereJets.generator (-Z (shift e.1 e.2)))) := by
    funext t
    change ((expLink (Z e.1) t*h e.2*(expLink (Z (shift e.1 e.2)) t)⁻¹ : SU2) : M2)=_
    rw [expLink_inv]
    rfl
  rw [he]
  have hc : (h e.2 : M2)ᴴ*(h e.2 : M2)=1 := by
    change (( (h e.2)⁻¹*h e.2 : SU2) : M2)=1
    simp
  have heq : SU2HemisphereJets.generator (gaugeGradient h Z e)*(h e.2 : M2)=
      SU2HemisphereJets.generator (Z e.1)*(h e.2 : M2)+
        (h e.2 : M2)*SU2HemisphereJets.generator (-Z (shift e.1 e.2)) := by
    unfold gaugeGradient
    rw [generator_sub,generator_rotate,generator_neg]
    unfold CubeMixedForm.adjointVelocity
    calc
      _ = SU2HemisphereJets.generator (Z e.1)*(h e.2 : M2)-
          (h e.2 : M2)*SU2HemisphereJets.generator (Z (shift e.1 e.2))*((h e.2 : M2)ᴴ*(h e.2 : M2)) := by noncomm_ring
      _ = _ := by rw [hc]; noncomm_ring
  rw [heq]
  have hd := ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) (SU2HemisphereJets.generator (Z e.1)) 0).mul_const
    (h e.2 : M2)).mul
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (SU2HemisphereJets.generator (-Z (shift e.1 e.2))) 0)
  convert! hd using 1
  simp only [zero_smul,NormedSpace.exp_zero,mul_one,one_mul]


private theorem curl_add (h : Fin 3 → SU2) (X Y : Velocity) (v : SpatialVertex) (i j : Fin 3) :
    covariantCurl h (X+Y) v i j=covariantCurl h X v i j+covariantCurl h Y v i j := by
  unfold covariantCurl
  simp only [Pi.add_apply,rotate_add]
  abel

theorem quadratic_add_gauge (h : Fin 3 → SU2) (X : Velocity) (Z : SpatialVertex → Triple)
    (hc : ∀ i j,h i*h j=h j*h i) : quadratic h (X+gaugeGradient h Z)=quadratic h X := by
  unfold quadratic
  apply Finset.sum_congr rfl
  intro p _
  rw [curl_add,curl_gauge_zero h Z _ _ _ (hc _ _),add_zero]

end OperatorDerivativeRewrite.Foundation.PeriodicFlatBackgroundHessian
