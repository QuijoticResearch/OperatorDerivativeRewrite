import Foundation.FourCubePinnedCoercivity
import Foundation.SU2FourWordVariation

/-! Actual logarithmic-ray second variations of the full72-face cell. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubePinnedSecondVariation
open QuaternionSU2Representation SU2TraceHessianModel SU2MatrixExponentialBridge
open SU2ExponentialMembership SU2ProductCurveHessian
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex
open FourCubeHaarParity FourCubeHaarChannels FourCubeIntegratedCubic FourCubePinnedHaar
open FourCubePinnedCoercivity
attribute [local irreducible] edges upperFaces innerFaces

abbrev Velocity := Interior → Fin 3 → ℝ

def extended (W : Velocity) (e : EdgeData) : Fin 3 → ℝ :=
  fun a => extend (fun k => W k a) e

def logState (W : Velocity) (t : ℝ) : InteriorState :=
  fun e => ⟨NormedSpace.exp (t • algebraElement (W e)),scaled_algebraElement_exp_mem t (W e)⟩

theorem extended_on (W : Velocity) (e : Interior) : extended W e.val=W e := by
  funext a
  simp [extended,extend,e.property]

theorem core_log_coe (W : Velocity) (t : ℝ) (e : EdgeData) :
    (coreField (logState W t) e : M2)=NormedSpace.exp (t • algebraElement (extended W e)) := by
  by_cases he : e∈edges
  · have hv := extended_on W (⟨e,he⟩ : Interior)
    rw [hv]
    simp only [coreField,dif_pos he,logState]
  · have hv : extended W e=0 := by funext a; simp [extended,extend,he]
    simp [coreField,he,hv,algebraElement]

theorem core_log_inv_coe (W : Velocity) (t : ℝ) (e : EdgeData) :
    ((coreField (logState W t) e)⁻¹ : SU2)=(⟨NormedSpace.exp (t • (-algebraElement (extended W e))),by
      have hm := scaled_algebraElement_exp_mem (-t) (extended W e)
      simpa only [neg_smul,smul_neg] using hm⟩ : SU2) := by
  apply Subtype.ext
  change ((coreField (logState W t) e : M2)ᴴ)=_
  rw [core_log_coe,← Matrix.exp_conjTranspose]
  simp [Matrix.conjTranspose_smul,algebraElement_skewHermitian]

def faceVectors (W : Velocity) (p : FaceData) : Fin 4 → (Fin 3 → ℝ) :=
  ![extended W (p.1,p.2.1),extended W (shifted p.1 p.2.1,p.2.2),
    extended W (shifted p.1 p.2.2,p.2.1),extended W (p.1,p.2.2)]

def faceModel (W : Velocity) (p : FaceData) : ℝ → ℝ :=
  SU2FourWordVariation.action (algebraElement (faceVectors W p 0))
    (algebraElement (faceVectors W p 1)) (-algebraElement (faceVectors W p 2))
    (-algebraElement (faceVectors W p 3))

def faceSlope (W : Velocity) (p : FaceData) : ℝ → ℝ :=
  SU2FourWordVariation.actionSlope (algebraElement (faceVectors W p 0))
    (algebraElement (faceVectors W p 1)) (-algebraElement (faceVectors W p 2))
    (-algebraElement (faceVectors W p 3))

def faceSecond (W : Velocity) (p : FaceData) (t : ℝ) : ℝ :=
  -traceReal (SU2FourWordVariation.pathSecond (algebraElement (faceVectors W p 0))
    (algebraElement (faceVectors W p 1)) (-algebraElement (faceVectors W p 2))
    (-algebraElement (faceVectors W p 3)) t)/2

def ray (W : Velocity) (t : ℝ) : ℝ := vacuumAction (logState W t)
def raySlope (W : Velocity) (t : ℝ) : ℝ :=
  (∑ p∈innerFaces,faceSlope W p t)+
    ∑ p : Upper,slope 1 (algebraElement (W (ribbonInterior p))) t

def ribbonSecond (W : Velocity) (p : Upper) (t : ℝ) : ℝ :=
  -traceReal ((1 : M2)*(algebraElement (W (ribbonInterior p))*
    (algebraElement (W (ribbonInterior p))*
      NormedSpace.exp (t • algebraElement (W (ribbonInterior p))))))/2

def raySecond (W : Velocity) (t : ℝ) : ℝ :=
  (∑ p∈innerFaces,faceSecond W p t)+∑ p : Upper,ribbonSecond W p t

theorem faceModel_hasDerivAt (W : Velocity) (p : FaceData) (t : ℝ) :
    HasDerivAt (faceModel W p) (faceSlope W p t) t :=
  SU2FourWordVariation.action_hasDerivAt (algebraElement (faceVectors W p 0))
    (algebraElement (faceVectors W p 1)) (-algebraElement (faceVectors W p 2))
    (-algebraElement (faceVectors W p 3)) t

theorem faceSlope_hasDerivAt (W : Velocity) (p : FaceData) (t : ℝ) :
    HasDerivAt (faceSlope W p) (faceSecond W p t) t :=
  SU2FourWordVariation.actionSlope_hasDerivAt (algebraElement (faceVectors W p 0))
    (algebraElement (faceVectors W p 1)) (-algebraElement (faceVectors W p 2))
    (-algebraElement (faceVectors W p 3)) t

theorem face_model (W : Velocity) (p : FaceData) (t : ℝ) :
    FourCubeWilsonCubic.faceAction (coreField (logState W t)) p=faceModel W p t := by
  unfold FourCubeWilsonCubic.faceAction
  rw [core_log_inv_coe,core_log_inv_coe]
  change 1-traceReal (((coreField (logState W t) (p.1,p.2.1) : M2)*
    (coreField (logState W t) (shifted p.1 p.2.1,p.2.2) : M2))*
    NormedSpace.exp (t • (-algebraElement (extended W (shifted p.1 p.2.2,p.2.1))))*
    NormedSpace.exp (t • (-algebraElement (extended W (p.1,p.2.2)))))/2=_
  rw [core_log_coe,core_log_coe]
  rfl

theorem ribbon_model (W : Velocity) (p : Upper) (t : ℝ) :
    defect (logState W t (ribbonInterior p))=curve 1 (algebraElement (W (ribbonInterior p))) t := by
  simp only [defect,halfTrace,logState,curve,wilson,one_mul]

theorem ray_model (W : Velocity) (t : ℝ) : ray W t=
    (∑ p∈innerFaces,faceModel W p t)+
      ∑ p : Upper,curve 1 (algebraElement (W (ribbonInterior p))) t := by
  unfold ray
  rw [vacuum_decomposition]
  change (∑ p∈innerFaces,FourCubeWilsonCubic.faceAction (coreField (logState W t)) p)+
    (∑ p : Upper,defect (logState W t (ribbonInterior p)))=_
  simp_rw [face_model,ribbon_model]

theorem ray_hasDerivAt (W : Velocity) (t : ℝ) :
    HasDerivAt (ray W) (raySlope W t) t := by
  have he : ray W=(fun u => (∑ p∈innerFaces,faceModel W p u)+
      ∑ p : Upper,curve 1 (algebraElement (W (ribbonInterior p))) u) := funext (ray_model W)
  rw [he]
  unfold raySlope
  have hh := (HasDerivAt.sum (u := innerFaces) (fun p _ => faceModel_hasDerivAt W p t)).add
    (HasDerivAt.sum (u := Finset.univ) (fun p _ => curve_hasDerivAt 1 (algebraElement (W (ribbonInterior p))) t))
  convert hh using 1
  funext u
  simp only [Finset.sum_apply,Pi.add_apply]

theorem raySlope_hasDerivAt (W : Velocity) (t : ℝ) :
    HasDerivAt (raySlope W) (raySecond W t) t := by
  unfold raySlope raySecond
  have hh := (HasDerivAt.sum (u := innerFaces) (fun p _ => faceSlope_hasDerivAt W p t)).add
    (HasDerivAt.sum (u := Finset.univ) (fun p _ => slope_hasDerivAt 1 (algebraElement (W (ribbonInterior p))) t))
  convert hh using 1
  · funext u
    simp only [Finset.sum_apply,Pi.add_apply]
  · rfl

def faceSum (W : Velocity) (p : FaceData) : Fin 3 → ℝ :=
  faceVectors W p 0+faceVectors W p 1-faceVectors W p 2-faceVectors W p 3

theorem faceSum_apply (W : Velocity) (p : FaceData) (a : Fin 3) :
    faceSum W p a=realCurl (extend (fun k => W k a)) p := rfl

theorem face_second_zero (W : Velocity) (p : FaceData) :
    faceSecond W p 0=lengthSq (faceSum W p)/4 :=
  SU2FourWordVariation.signed_slope_second_zero _ _ _ _

theorem ray_second_zero (W : Velocity) :
    deriv (deriv (ray W)) 0=
      ((∑ p∈innerFaces,lengthSq (faceSum W p))+
        ∑ p : Upper,lengthSq (W (ribbonInterior p)))/4 := by
  have he : deriv (ray W)=raySlope W := funext (fun t => (ray_hasDerivAt W t).deriv)
  rw [he,(raySlope_hasDerivAt W 0).deriv]
  unfold raySecond
  simp_rw [face_second_zero]
  have hr (p : Upper) : ribbonSecond W p 0=lengthSq (W (ribbonInterior p))/4 := by
    unfold ribbonSecond
    simp only [zero_smul,NormedSpace.exp_zero,mul_one,one_mul]
    have hh := algebraElement_metric_sq (W (ribbonInterior p))
    rw [pow_two] at hh
    linarith
  simp_rw [hr]
  rw [← Finset.sum_div,← Finset.sum_div]
  ring


theorem incidence_identity (W : Velocity) :
    ((∑ p∈innerFaces,lengthSq (faceSum W p))+
      ∑ p : Upper,lengthSq (W (ribbonInterior p)))=
      ∑ a : Fin 3,realEnergy (extend (fun k => W k a)) := by
  unfold lengthSq
  simp_rw [faceSum_apply]
  conv_lhs => lhs; rw [Finset.sum_comm]
  conv_lhs => rhs; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  unfold realEnergy
  congr 1
  trans ∑ p : Upper,(extend (fun k => W k a) p.val.1)^2
  · apply Finset.sum_congr rfl
    intro p _
    have he := extend_on (fun k => W k a) (ribbonInterior p)
    change extend (fun k => W k a) p.val.1=W (ribbonInterior p) a at he
    rw [he]
  · exact Finset.sum_coe_sort upperFaces (fun p => (extend (fun k => W k a) p.1)^2)

theorem ray_second_incidence (W : Velocity) :
    deriv (deriv (ray W)) 0=(∑ a : Fin 3,realEnergy (extend (fun k => W k a)))/4 := by
  rw [ray_second_zero,incidence_identity]

theorem ray_first_zero (W : Velocity) : deriv (ray W) 0=0 := by
  rw [(ray_hasDerivAt W 0).deriv]
  unfold raySlope faceSlope
  simp_rw [SU2FourWordVariation.signed_first_zero]
  have hr (p : Upper) : slope 1 (algebraElement (W (ribbonInterior p))) 0=0 := by
    simp [SU2ProductCurveHessian.slope,traceReal,algebraElement_trace]
  simp [hr]

abbrev PinnedVelocity := OneSidedPinnedInterior.Free → Fin 3 → ℝ

def liftVelocity (V : PinnedVelocity) : Velocity :=
  fun e a => OneSidedPinnedInterior.lift (fun k => V k a) e

def pinnedChart (V : PinnedVelocity) (t : ℝ) : PinnedState :=
  fun e => ⟨NormedSpace.exp (t • algebraElement (V e)),scaled_algebraElement_exp_mem t (V e)⟩

def pinnedRay (V : PinnedVelocity) (t : ℝ) : ℝ := pinnedAction (pinnedChart V t)

theorem liftVelocity_pole (V : PinnedVelocity) : liftVelocity V OneSidedPinnedInterior.pole=0 := by
  funext a
  exact OneSidedPinnedInterior.lift_pole (fun k => V k a)

theorem liftVelocity_free (V : PinnedVelocity) (e : OneSidedPinnedInterior.Free) :
    liftVelocity V e.val=V e := by
  funext a
  exact OneSidedPinnedInterior.lift_free (fun k => V k a) e

theorem pinnedChart_fill (V : PinnedVelocity) (t : ℝ) :
    fillPole 1 (pinnedChart V t)=logState (liftVelocity V) t := by
  funext e
  by_cases h : e=OneSidedPinnedInterior.pole
  · subst e
    apply Subtype.ext
    simp [fillPole,logState,liftVelocity_pole,algebraElement]
  · have hv := liftVelocity_free V (⟨e,h⟩ : OneSidedPinnedInterior.Free)
    apply Subtype.ext
    simp only [fillPole,dif_neg h,pinnedChart,logState,hv]

theorem pinnedRay_eq (V : PinnedVelocity) : pinnedRay V=ray (liftVelocity V) := by
  funext t
  unfold pinnedRay pinnedAction ray
  rw [pinnedChart_fill]

theorem pinned_first_zero (V : PinnedVelocity) : deriv (pinnedRay V) 0=0 := by
  rw [pinnedRay_eq,ray_first_zero]

theorem pinned_second_gram (V : PinnedVelocity) :
    deriv (deriv (pinnedRay V)) 0=
      (∑ a : Fin 3, dotProduct (fun e => V e a)
        (OneSidedPinnedInterior.localGram.mulVec (fun e => V e a)))/4 := by
  rw [pinnedRay_eq,ray_second_incidence]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact (OneSidedPinnedInterior.localGram_energy (fun e => V e a)).symm

theorem pinned_second_positive (V : PinnedVelocity) (hV : V ≠ 0) :
    0 < deriv (deriv (pinnedRay V)) 0 := by
  have hex : ∃ a : Fin 3,(fun e => V e a)≠0 := by
    by_contra hn
    push_neg at hn
    apply hV
    funext e a
    exact congrFun (hn a) e
  obtain ⟨a,ha⟩ := hex
  have hpos := OneSidedPinnedInterior.localGram_positive (fun e => V e a) ha
  have hn (b : Fin 3) : 0 ≤ dotProduct (fun e => V e b)
      (OneSidedPinnedInterior.localGram.mulVec (fun e => V e b)) := by
    rw [OneSidedPinnedInterior.localGram_energy]
    exact realEnergy_nonneg _
  have hs : 0<(∑ b : Fin 3,dotProduct (fun e => V e b)
      (OneSidedPinnedInterior.localGram.mulVec (fun e => V e b))) :=
    Finset.sum_pos' (fun b _ => hn b) ⟨a,Finset.mem_univ a,hpos⟩
  rw [pinned_second_gram]
  exact div_pos hs (by norm_num)

end OperatorDerivativeRewrite.Foundation.FourCubePinnedSecondVariation
