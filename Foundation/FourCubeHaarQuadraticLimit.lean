import Foundation.FourCubeAmbientAction
import Foundation.SU2HemisphereJets
import Foundation.FourCubeHemisphereCoercivity
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Taylor

/-! Quadratic scaling of the actual pinned Wilson action in actual Haar coordinates. -/
noncomputable section
open Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeHaarQuadraticLimit
open QuaternionSU2Representation SU2TraceHessianModel SU2MatrixExponentialBridge
open SU2ProductCurveHessian SU2ExponentialMembership SU2HemisphereChart SU2GaussianConeCoordinates
open FourCubePinnedHaar FourCubePinnedCoercivity FourCubePinnedSecondVariation
open FourCubeHemisphereCoercivity FourCubeAmbientAction

private theorem curve_contDiff (y : Triple) : ContDiff ℝ 2 (SU2HemisphereJets.curve y) := by
  have hp (t : ℝ) : 0 < 1+t^2*SU2HemisphereJets.sizeSq y := by
    have hh := SU2HemisphereJets.sizeSq_nonneg y
    positivity
  have hb : ContDiff ℝ 2 (fun t : ℝ => 1+t^2*SU2HemisphereJets.sizeSq y) :=
    contDiff_const.add ((contDiff_id.pow 2).mul contDiff_const)
  have hw : ContDiff ℝ 2 (SU2HemisphereJets.weight y) :=
    (hb.sqrt (fun t => (hp t).ne')).inv (fun t => (Real.sqrt_pos.mpr (hp t)).ne')
  have ha : ContDiff ℝ 2 (SU2HemisphereJets.affine y) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  convert! hw.smul ha using 1
  funext t
  exact SU2HemisphereJets.curve_formula y t

private theorem exp_contDiff (y : Triple) :
    ContDiff ℝ 2 (fun t : ℝ => NormedSpace.exp (t • SU2HemisphereJets.generator y)) := by
  have he : ContDiff ℝ 2 (NormedSpace.exp : M2 → M2) :=
    contDiff_iff_contDiffAt.mpr (fun M => (NormedSpace.exp_analytic (𝕂 := ℝ) M).contDiffAt)
  exact he.comp (contDiff_id.smul contDiff_const)

def ratioPath (Y : Field) (t : ℝ) : MatrixField :=
  fun e => SU2HemisphereJets.curve (liftVelocity Y e) t

def expPath (Y : Field) (t : ℝ) : MatrixField :=
  fun e => NormedSpace.exp (t • SU2HemisphereJets.generator (liftVelocity Y e))

theorem ratioPath_contDiff (Y : Field) : ContDiff ℝ 2 (ratioPath Y) :=
  contDiff_pi.mpr (fun e => curve_contDiff (liftVelocity Y e))

theorem expPath_contDiff (Y : Field) : ContDiff ℝ 2 (expPath Y) :=
  contDiff_pi.mpr (fun e => exp_contDiff (liftVelocity Y e))

theorem path_value_zero (Y : Field) : ratioPath Y 0=expPath Y 0 := by
  funext e
  exact (SU2HemisphereJets.curve_two_jet (liftVelocity Y e)).1

theorem path_first_zero (Y : Field) : deriv (ratioPath Y) 0=deriv (expPath Y) 0 := by
  have hr : deriv (ratioPath Y) 0=(fun e => deriv (SU2HemisphereJets.curve (liftVelocity Y e)) 0) := by
    convert! deriv_pi (fun e => ((curve_contDiff (liftVelocity Y e)).differentiable (by norm_num)).differentiableAt) using 1
  have he : deriv (expPath Y) 0=(fun e => deriv
      (fun t : ℝ => NormedSpace.exp (t • SU2HemisphereJets.generator (liftVelocity Y e))) 0) := by
    convert! deriv_pi (fun e => ((exp_contDiff (liftVelocity Y e)).differentiable (by norm_num)).differentiableAt) using 1
  exact hr.trans ((funext (fun e => (SU2HemisphereJets.curve_two_jet (liftVelocity Y e)).2.1)).trans he.symm)

theorem path_second_zero (Y : Field) :
    deriv (deriv (ratioPath Y)) 0=deriv (deriv (expPath Y)) 0 := by
  have hr : deriv (ratioPath Y)=(fun t e => deriv (SU2HemisphereJets.curve (liftVelocity Y e)) t) := by
    funext t
    exact deriv_pi (fun e => ((curve_contDiff (liftVelocity Y e)).differentiable (by norm_num)).differentiableAt)
  have he : deriv (expPath Y)=(fun t e => deriv
      (fun u : ℝ => NormedSpace.exp (u • SU2HemisphereJets.generator (liftVelocity Y e))) t) := by
    funext t
    exact deriv_pi (fun e => ((exp_contDiff (liftVelocity Y e)).differentiable (by norm_num)).differentiableAt)
  rw [hr,he]
  have hr0 : deriv (fun t e => deriv (SU2HemisphereJets.curve (liftVelocity Y e)) t) 0=
      (fun e => deriv (deriv (SU2HemisphereJets.curve (liftVelocity Y e))) 0) := by
    convert! deriv_pi (fun e => (curve_contDiff (liftVelocity Y e)).differentiable_deriv_two.differentiableAt) using 1
  have he0 : deriv (fun t e => deriv
      (fun u : ℝ => NormedSpace.exp (u • SU2HemisphereJets.generator (liftVelocity Y e))) t) 0=
      (fun e => deriv (deriv (fun u : ℝ => NormedSpace.exp (u • SU2HemisphereJets.generator (liftVelocity Y e)))) 0) := by
    convert! deriv_pi (fun e => (exp_contDiff (liftVelocity Y e)).differentiable_deriv_two.differentiableAt) using 1
  exact hr0.trans ((funext (fun e => (SU2HemisphereJets.curve_two_jet (liftVelocity Y e)).2.2)).trans he0.symm)

theorem action_second_transfer (Y : Field) :
    deriv (deriv (action ∘ ratioPath Y)) 0=deriv (deriv (action ∘ expPath Y)) 0 := by
  have hr := iteratedDeriv_vcomp_two action_contDiff.contDiffAt (ratioPath_contDiff Y).contDiffAt (x := (0 : ℝ))
  have he := iteratedDeriv_vcomp_two action_contDiff.contDiffAt (expPath_contDiff Y).contDiffAt (x := (0 : ℝ))
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hr he
  have hp : (ratioPath Y 0,deriv (ratioPath Y) 0,deriv (deriv (ratioPath Y)) 0)=
      (expPath Y 0,deriv (expPath Y) 0,deriv (deriv (expPath Y)) 0) := by
    exact Prod.ext (path_value_zero Y) (Prod.ext (path_first_zero Y) (path_second_zero Y))
  have hj := congrArg (fun z : MatrixField × MatrixField × MatrixField =>
    iteratedFDeriv ℝ 2 action z.1 (fun _ : Fin 2 => z.2.1)+fderiv ℝ action z.1 z.2.2)
    hp
  exact hr.trans (hj.trans he.symm)

def frameField (Y : Field) : PinnedVelocity := fun e => SU2HemisphereJets.frame (Y e)

theorem frame_lift (Y : Field) (e : OneSidedBlockRank.Interior) :
    SU2HemisphereJets.frame (liftVelocity Y e)=liftVelocity (frameField Y) e := by
  by_cases hp : e=OneSidedPinnedInterior.pole
  · subst e
    rw [liftVelocity_pole,liftVelocity_pole]
    simp [SU2HemisphereJets.frame]
  · change SU2HemisphereJets.frame (liftVelocity Y (⟨e,hp⟩ : OneSidedPinnedInterior.Free).val)=
      liftVelocity (frameField Y) (⟨e,hp⟩ : OneSidedPinnedInterior.Free).val
    rw [liftVelocity_free,liftVelocity_free]
    rfl

theorem expPath_actual (Y : Field) (t : ℝ) :
    action (expPath Y t)=pinnedRay (frameField Y) t := by
  rw [pinnedRay_eq]
  unfold ray
  rw [← action_actual]
  congr 1
  funext e
  change NormedSpace.exp (t • algebraElement (SU2HemisphereJets.frame (liftVelocity Y e)))=
    NormedSpace.exp (t • algebraElement (liftVelocity (frameField Y) e))
  rw [frame_lift]

theorem ratioPath_actual (Y : Field) (t : ℝ) :
    action (ratioPath Y t)=pinnedAction (chartField (t • Y)) := by
  unfold pinnedAction
  rw [← action_actual]
  congr 1
  funext e
  change (hemisphereChart (t • liftVelocity Y e) : M2)=
    (fillPole 1 (chartField (t • Y)) e : M2)
  by_cases hp : e=OneSidedPinnedInterior.pole
  · subst e
    rw [liftVelocity_pole]
    simp only [smul_zero,fillPole,dite_true]
    convert! SU2HemisphereJets.curve_zero (0 : Triple) using 1 <;>
      simp only [SU2HemisphereJets.curve,zero_smul]
  · change (hemisphereChart (t • liftVelocity Y (⟨e,hp⟩ : OneSidedPinnedInterior.Free).val) : M2)=_
    rw [liftVelocity_free]
    simp only [fillPole,dif_neg hp,chartField,Pi.smul_apply]

def ray (Y : Field) (t : ℝ) : ℝ := pinnedAction (chartField (t • Y))

theorem ray_contDiff (Y : Field) : ContDiff ℝ 2 (ray Y) := by
  have he : ray Y=action ∘ ratioPath Y := (funext (ratioPath_actual Y)).symm
  rw [he]
  exact action_contDiff.comp (ratioPath_contDiff Y)

theorem ray_second_gram_frame (Y : Field) :
    deriv (deriv (ray Y)) 0=(∑ a : Fin 3,dotProduct (fun e => frameField Y e a)
      (OneSidedPinnedInterior.localGram.mulVec (fun e => frameField Y e a)))/4 := by
  have hr : ray Y=action ∘ ratioPath Y := (funext (ratioPath_actual Y)).symm
  have he : action ∘ expPath Y=pinnedRay (frameField Y) := funext (expPath_actual Y)
  rw [hr,action_second_transfer,he,pinned_second_gram]


theorem action_first_transfer (Y : Field) :
    deriv (action ∘ ratioPath Y) 0=deriv (action ∘ expPath Y) 0 := by
  have hr := ((action_contDiff.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt 0
    ((ratioPath_contDiff Y).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have he := ((action_contDiff.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt 0
    ((expPath_contDiff Y).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hp : (ratioPath Y 0,deriv (ratioPath Y) 0)=(expPath Y 0,deriv (expPath Y) 0) :=
    Prod.ext (path_value_zero Y) (path_first_zero Y)
  have hj := congrArg (fun z : MatrixField × MatrixField => fderiv ℝ action z.1 z.2) hp
  exact hr.deriv.trans (hj.trans he.deriv.symm)

theorem ray_first_zero (Y : Field) : deriv (ray Y) 0=0 := by
  have hr : ray Y=action ∘ ratioPath Y := (funext (ratioPath_actual Y)).symm
  have he : action ∘ expPath Y=pinnedRay (frameField Y) := funext (expPath_actual Y)
  rw [hr,action_first_transfer,he,pinned_first_zero]

theorem ray_zero (Y : Field) : ray Y 0=0 := by
  have hc : chartField ((0 : ℝ) • Y)=1 := by
    funext e
    apply Subtype.ext
    convert! SU2HemisphereJets.curve_zero (Y e) using 1
  exact (pinnedAction_zero_iff _).mpr hc

def quadraticForm (Y : Field) : ℝ :=
  ∑ a : Fin 3,dotProduct (fun e => Y e a)
    (OneSidedPinnedInterior.localGram.mulVec (fun e => Y e a))

theorem frame_quadraticForm (Y : Field) :
    (∑ a : Fin 3,dotProduct (fun e => frameField Y e a)
      (OneSidedPinnedInterior.localGram.mulVec (fun e => frameField Y e a)))=4*quadraticForm Y := by
  have h2 (a : Fin 3) :
      dotProduct (fun e => 2*Y e a) (OneSidedPinnedInterior.localGram.mulVec (fun e => 2*Y e a))=
        4*dotProduct (fun e => Y e a) (OneSidedPinnedInterior.localGram.mulVec (fun e => Y e a)) := by
    change dotProduct ((2 : ℝ) • (fun e => Y e a))
      (OneSidedPinnedInterior.localGram.mulVec ((2 : ℝ) • (fun e => Y e a)))=_
    rw [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  simp [frameField,SU2HemisphereJets.frame,Fin.sum_univ_three,quadraticForm]
  rw [h2,h2,h2]
  ring

theorem ray_second_gram (Y : Field) : deriv (deriv (ray Y)) 0=quadraticForm Y := by
  rw [ray_second_gram_frame,frame_quadraticForm]
  ring

theorem ray_second_positive (Y : Field) (hY : Y ≠ 0) : 0 < deriv (deriv (ray Y)) 0 := by
  have hn : frameField Y ≠ 0 := by
    intro he
    apply hY
    funext e a
    have h0 := congrFun (congrFun he e) 0
    have h1 := congrFun (congrFun he e) 1
    have h2 := congrFun (congrFun he e) 2
    fin_cases a <;> norm_num [frameField,SU2HemisphereJets.frame] at h0 h1 h2 ⊢ <;> linarith
  rw [ray_second_gram_frame,← pinned_second_gram]
  exact pinned_second_positive (frameField Y) hn

theorem ray_taylor_polynomial (Y : Field) (t : ℝ) :
    taylorWithinEval (ray Y) 2 Set.univ 0 t=(quadraticForm Y/2)*t^2 := by
  simp [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_univ,
    iteratedDeriv_succ,iteratedDeriv_zero,ray_zero,ray_first_zero,ray_second_gram]
  ring

theorem ray_quadratic_remainder (Y : Field) :
    (fun t : ℝ => ray Y t-(quadraticForm Y/2)*t^2) =o[𝓝 0] (fun t : ℝ => t^2) := by
  simpa only [ray_taylor_polynomial,sub_zero] using
    (taylor_isLittleO_univ (x₀ := 0) (n := 2) (ray_contDiff Y))

theorem ray_quadratic_limit (Y : Field) :
    Tendsto (fun t : ℝ => ray Y t/t^2) (𝓝[≠] 0) (𝓝 (quadraticForm Y/2)) := by
  have hh := ((ray_quadratic_remainder Y).tendsto_div_nhds_zero.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).add_const (quadraticForm Y/2)
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : t ≠ 0 := ht
  field_simp [hn]
  ring


theorem no_unpunctured_quadratic_limit (Y : Field) (hY : Y ≠ 0) :
    ¬ Tendsto (fun t : ℝ => ray Y t/t^2) (𝓝 0) (𝓝 (quadraticForm Y/2)) := by
  intro hh
  have he := eq_of_tendsto_nhds hh
  have hp : 0 < quadraticForm Y := by
    rw [← ray_second_gram]
    exact ray_second_positive Y hY
  simp only [zero_pow (by norm_num : 2 ≠ 0),div_zero] at he
  linarith

theorem boltzmann_quadratic_limit (Y : Field) :
    Tendsto (fun t : ℝ => Real.exp (-ray Y t/t^2)) (𝓝[≠] 0)
      (𝓝 (Real.exp (-quadraticForm Y/2))) := by
  exact Real.continuous_exp.continuousAt.tendsto.comp
    (by simpa only [neg_div] using (ray_quadratic_limit Y).neg)

end OperatorDerivativeRewrite.Foundation.FourCubeHaarQuadraticLimit
