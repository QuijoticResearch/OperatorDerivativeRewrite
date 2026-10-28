import Foundation.FourCubeHaarParity
import Foundation.SU2StrongCouplingCovariance
import Mathlib.Probability.Independence.Integration

/-! Actual finite-cell Haar channels needed to test the integrated cubic.
No continuum measure or mass gap is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.FourCubeHaarChannels
open QuaternionSU2Representation OneSidedBlockIncidence OneSidedBlockRank
open OneSidedCapComplex FourCubeHaarParity FourCubeWilsonCubic
attribute [local irreducible] edges upperFaces

def linkProbe (e : Interior) (A : SU2) (s : InteriorState) : ℝ := halfTrace (A*s e)

theorem linkProbe_measurable (e : Interior) (A : SU2) : Measurable (linkProbe e A) :=
  halfTrace_measurable.comp ((measurable_const_mul A).comp (measurable_pi_apply e))

theorem linkProbe_bound (e : Interior) (A : SU2) (s : InteriorState) : |linkProbe e A s| ≤ 1 :=
  halfTrace_bound _

theorem linkProbe_integrable (e : Interior) (A : SU2) : Integrable (linkProbe e A) interiorHaar :=
  Integrable.of_bound (linkProbe_measurable e A).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using linkProbe_bound e A s)

private theorem integral_eval (e : Interior) (f : SU2 → ℝ) (hf : Measurable f) :
    (∫ s : InteriorState, f (s e) ∂interiorHaar)=∫ C, f C ∂law := by
  have hm : interiorHaar.map (fun s : InteriorState => s e)=law :=
    (measurePreserving_eval (fun _ : Interior => law) e).map_eq
  have h := integral_map (μ := interiorHaar) (measurable_pi_apply e).aemeasurable hf.aestronglyMeasurable
  rw [hm] at h
  exact h.symm

theorem linkProbe_mean (e : Interior) (A : SU2) : (∫ s, linkProbe e A s ∂interiorHaar)=0 := by
  unfold linkProbe
  rw [integral_eval e (fun C => halfTrace (A*C)) (halfTrace_measurable.comp (measurable_const_mul A)),
    integral_mul_left_eq_self (μ := law) halfTrace A]
  exact (SU2TiltEnergyResponse.moment_values law).1

theorem linkProbe_pair (e f : Interior) (A B : SU2) :
    (∫ s, linkProbe e A s*linkProbe f B s ∂interiorHaar)=
      if e=f then halfTrace (A*B⁻¹)/4 else 0 := by
  by_cases he : e=f
  · subst f
    rw [if_pos rfl]
    unfold linkProbe
    rw [integral_eval e (fun C => halfTrace (A*C)*halfTrace (B*C)) ((halfTrace_measurable.comp (measurable_const_mul A)).mul
      (halfTrace_measurable.comp (measurable_const_mul B)))]
    exact SU2SharedPlaquetteProjection.translated_pair_covariance A B
  · rw [if_neg he]
    have hi : iIndepFun (fun e : Interior => fun s : InteriorState => s e) interiorHaar :=
      iIndepFun_pi (μ := fun _ : Interior => law) (X := fun _ : Interior => id) (fun _ => aemeasurable_id)
    have hp := (hi.indepFun he).comp (halfTrace_measurable.comp (measurable_const_mul A))
      (halfTrace_measurable.comp (measurable_const_mul B))
    have hm := hp.integral_mul_eq_mul_integral (linkProbe_measurable e A).aestronglyMeasurable
      (linkProbe_measurable f B).aestronglyMeasurable
    change (∫ s, linkProbe e A s*linkProbe f B s ∂interiorHaar)=
      (∫ s, linkProbe e A s ∂interiorHaar)*(∫ s, linkProbe f B s ∂interiorHaar) at hm
    rw [hm,linkProbe_mean,zero_mul]

def interiorGauge (g : Vertex → SU2) (s : InteriorState) : InteriorState :=
  fun e => g e.val.1*s e*(g (shifted e.val.1 e.val.2))⁻¹

private theorem haar_endpoints (g h : SU2) : law.map (fun C => g*C*h⁻¹)=law := by
  have hr : law.map (fun C : SU2 => C*h⁻¹)=law := by
    haveI : IsProbabilityMeasure (law.map (fun C : SU2 => C*h⁻¹)) := by infer_instance
    exact (law_eq_probability_haar (law.map (fun C : SU2 => C*h⁻¹))).symm
  have he : (fun C : SU2 => g*C*h⁻¹)=(fun D => g*D) ∘ (fun C => C*h⁻¹) := by
    funext C
    simp [Function.comp_def,mul_assoc]
  rw [he,← Measure.map_map (measurable_const_mul g) (measurable_mul_const h⁻¹),hr,map_mul_left_eq_self]

theorem interiorGauge_preserving (g : Vertex → SU2) :
    MeasurePreserving (interiorGauge g) interiorHaar interiorHaar := by
  unfold interiorGauge interiorHaar
  apply measurePreserving_pi (fun _ : Interior => law) (fun _ : Interior => law)
    (f := fun (e : Interior) (C : SU2) => g e.val.1*C*(g (shifted e.val.1 e.val.2))⁻¹)
  intro e
  exact ⟨(measurable_mul_const _).comp (measurable_const_mul _),haar_endpoints _ _⟩

def coreField (s : InteriorState) (e : EdgeData) : SU2 :=
  if he : e∈edges then s ⟨e,he⟩ else 1

def internalAction (s : InteriorState) : ℝ := innerAction (coreField s)

private theorem coreField_measurable : Measurable coreField := by
  apply measurable_pi_iff.mpr
  intro e
  by_cases he : e∈edges
  · simpa only [coreField,dif_pos he] using (measurable_pi_apply (⟨e,he⟩ : Interior))
  · simp only [coreField,dif_neg he]
    exact measurable_const

private theorem traceWord_measurable {ι : Type} (a b c d : ι) :
    Measurable (fun U : ι → SU2 => halfTrace (U a*U b*(U c)⁻¹*(U d)⁻¹)) :=
  halfTrace_measurable.comp ((((measurable_pi_apply a).mul (measurable_pi_apply b)).mul
    (measurable_pi_apply c).inv).mul (measurable_pi_apply d).inv)

theorem internalAction_measurable : Measurable internalAction := by
  unfold internalAction innerAction
  apply Finset.measurable_sum
  intro p _
  exact (measurable_const.sub (traceWord_measurable (ι := EdgeData)
    (FourCubeChordIncidence.faceEdge p 0) (FourCubeChordIncidence.faceEdge p 1)
    (FourCubeChordIncidence.faceEdge p 2) (FourCubeChordIncidence.faceEdge p 3))).comp coreField_measurable

private theorem coreGauge_on (g : Vertex → SU2) (s : InteriorState) (e : EdgeData) (he : e∈edges) :
    coreField (interiorGauge g s) e=gaugeField g (coreField s) e := by
  simp [coreField,interiorGauge,gaugeField,he]

private theorem internalFace_gauge (g : Vertex → SU2) (s : InteriorState)
    (p : FaceData) (hp : p∈innerFaces) :
    faceAction (coreField (interiorGauge g s)) p=faceAction (coreField s) p := by
  have he (i : Fin 4) : FourCubeChordIncidence.faceEdge p i ∈ edges :=
    FourCubeChordIncidence.boundary_subset p hp
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  calc
    _ = faceAction (gaugeField g (coreField s)) p := by
      unfold faceAction
      rw [coreGauge_on g s _ (he 0),coreGauge_on g s _ (he 1),
        coreGauge_on g s _ (he 2),coreGauge_on g s _ (he 3)]
    _ = _ := faceAction_gauge g (coreField s) p

theorem internalAction_gauge (g : Vertex → SU2) (s : InteriorState) :
    internalAction (interiorGauge g s)=internalAction s := by
  unfold internalAction innerAction
  exact Finset.sum_congr rfl (fun p hp => internalFace_gauge g s p hp)

private theorem integral_gauge (g : Vertex → SU2) (f : InteriorState → ℝ) (hf : Measurable f) :
    (∫ s, f (interiorGauge g s) ∂interiorHaar)=∫ s, f s ∂interiorHaar := by
  have h := integral_map (μ := interiorHaar) (interiorGauge_preserving g).measurable.aemeasurable hf.aestronglyMeasurable
  rw [(interiorGauge_preserving g).map_eq] at h
  exact h.symm

def vertexCenter (v : Vertex) : Vertex → SU2 :=
  fun w => if w=v then SU2StapleExtremes.minusOne else 1

private theorem target_ne_source (e : Interior) : shifted e.val.1 e.val.2 ≠ e.val.1 := by
  have he : e.val∈edges := e.property
  simp only [edges,Finset.mem_filter,Finset.mem_univ,true_and] at he
  intro h
  have hc := congrArg (fun v : Vertex => v e.val.2) h
  simp [shifted,he] at hc

theorem linkProbe_center (e : Interior) (A : SU2) (s : InteriorState) :
    linkProbe e A (interiorGauge (vertexCenter e.val.1) s)= -linkProbe e A s := by
  have he : interiorGauge (vertexCenter e.val.1) s e=SU2StapleExtremes.minusOne*s e := by
    simp [interiorGauge,vertexCenter,target_ne_source e]
  unfold linkProbe
  rw [he,SU2WilsonConvolution.halfTrace_mul_comm A _,mul_assoc,
    SU2StrongCouplingCovariance.halfTrace_center_neg,SU2WilsonConvolution.halfTrace_mul_comm (s e) A]

/-- Local gauge symmetry makes every internal closed-action channel orthogonal
to an open fundamental ribbon channel in the ACTUAL32-link product Haar law. -/
theorem internal_link_orthogonal (e : Interior) (A : SU2) :
    (∫ s, internalAction s*linkProbe e A s ∂interiorHaar)=0 := by
  have h := integral_gauge (vertexCenter e.val.1) (fun s => internalAction s*linkProbe e A s)
    (internalAction_measurable.mul (linkProbe_measurable e A))
  simp_rw [internalAction_gauge,linkProbe_center,mul_neg,integral_neg] at h
  linarith

theorem linkProbe_memLp (e : Interior) (A : SU2) : MemLp (linkProbe e A) 2 interiorHaar :=
  MemLp.of_bound (linkProbe_measurable e A).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using linkProbe_bound e A s)

theorem linkProbe_covariance (e f : Interior) (A B : SU2) :
    covariance (linkProbe e A) (linkProbe f B) interiorHaar=
      if e=f then halfTrace (A*B⁻¹)/4 else 0 := by
  rw [covariance_eq_sub (linkProbe_memLp e A) (linkProbe_memLp f B)]
  change (∫ s, linkProbe e A s*linkProbe f B s ∂interiorHaar)-
    (∫ s, linkProbe e A s ∂interiorHaar)*(∫ s, linkProbe f B s ∂interiorHaar)=_
  rw [linkProbe_mean,zero_mul,sub_zero,linkProbe_pair]

theorem linkProbe_variance (e : Interior) (A : SU2) : variance (linkProbe e A) interiorHaar=1/4 := by
  rw [← covariance_self (linkProbe_measurable e A).aemeasurable,linkProbe_covariance]
  simp [FourCubeWilsonCubic.trace_one]

theorem internalAction_bound (s : InteriorState) : |internalAction s| ≤ 48 := by
  have hb (p : FaceData) : |faceAction (coreField s) p| ≤ 2 := by
    let W := coreField s (FourCubeChordIncidence.faceEdge p 0)*
      coreField s (FourCubeChordIncidence.faceEdge p 1)*
      (coreField s (FourCubeChordIncidence.faceEdge p 2))⁻¹*
      (coreField s (FourCubeChordIncidence.faceEdge p 3))⁻¹
    change |1-halfTrace W| ≤ 2
    have h := halfTrace_bound W
    have ha := norm_sub_le (1:ℝ) (halfTrace W)
    simp only [Real.norm_eq_abs,abs_one] at ha
    linarith
  change |∑ p∈innerFaces,faceAction (coreField s) p| ≤ 48
  calc
    _ ≤ ∑ p∈innerFaces,|faceAction (coreField s) p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p∈innerFaces,(2:ℝ) := Finset.sum_le_sum (fun p _ => hb p)
    _ = 48 := by norm_num [innerFaces_card]

theorem internalAction_memLp : MemLp internalAction 2 interiorHaar :=
  MemLp.of_bound internalAction_measurable.aestronglyMeasurable 48
    (Filter.Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using internalAction_bound s)

theorem internal_link_covariance (e : Interior) (A : SU2) :
    covariance internalAction (linkProbe e A) interiorHaar=0 := by
  rw [covariance_eq_sub internalAction_memLp (linkProbe_memLp e A)]
  change (∫ s, internalAction s*linkProbe e A s ∂interiorHaar)-
    (∫ s, internalAction s ∂interiorHaar)*(∫ s, linkProbe e A s ∂interiorHaar)=0
  rw [internal_link_orthogonal,linkProbe_mean,mul_zero,sub_self]

end OperatorDerivativeRewrite.Foundation.FourCubeHaarChannels
