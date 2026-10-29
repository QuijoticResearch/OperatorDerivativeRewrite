import Foundation.FourCubeIntegratedResponse
import Foundation.OneSidedPinnedInterior
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact removal of the residual root gauge coordinate from the ACTUAL72-face
Haar partition. This is a31-link normalized Haar integral, not a Gaussian approximation. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.FourCubePinnedHaar
open QuaternionSU2Representation OneSidedBlockIncidence OneSidedBlockRank
open OneSidedCapComplex FourCubeHaarParity FourCubeHaarChannels FourCubeIntegratedCubic
open OneSidedPinnedInterior (pole Free)
attribute [local irreducible] edges upperFaces

abbrev PinnedState := Free → SU2
def pinnedHaar : Measure PinnedState := Measure.pi (fun _ => law)
instance pinnedHaar_probability : IsProbabilityMeasure pinnedHaar := by
  unfold pinnedHaar
  infer_instance

def fillPole (V : SU2) (y : PinnedState) : InteriorState :=
  fun e => if h : e=pole then V else y ⟨e,h⟩

def rootGauge (V : SU2) : Vertex → SU2 := fun v => if v=origin then V else 1

def rootLeft (V : SU2) (y : PinnedState) : PinnedState :=
  fun e => if e.val.val.1=origin then V*y e else y e

theorem rootLeft_preserving (V : SU2) :
    MeasurePreserving (rootLeft V) pinnedHaar pinnedHaar := by
  unfold pinnedHaar rootLeft
  apply measurePreserving_pi (fun _ : Free => law) (fun _ : Free => law)
    (f := fun (e : Free) (C : SU2) => if e.val.val.1=origin then V*C else C)
  intro e
  by_cases h : e.val.val.1=origin
  · simp only [h,ite_true]
    exact ⟨measurable_const_mul V,map_mul_left_eq_self law V⟩
  · simp only [h,ite_false]
    exact MeasurePreserving.id law

theorem fillPole_rootLeft (V : SU2) (y : PinnedState) :
    fillPole V (rootLeft V y)=interiorGauge (rootGauge V) (fillPole 1 y) := by
  funext e
  have ht := shifted_target_nonorigin e.val e.property
  by_cases h : e=pole
  · subst e
    simp only [interiorGauge,rootGauge,if_neg ht]
    simp [fillPole,pole]
  · simp [fillPole,rootLeft,interiorGauge,rootGauge,h,ht]

private theorem ribbon_root (V : SU2) (s : InteriorState) (p : Upper) :
    interiorGauge (rootGauge V) s (ribbonInterior p)=s (ribbonInterior p) := by
  have ht := shifted_target_nonorigin (ribbonInterior p).val (ribbonInterior p).property
  change shifted p.val.1.1 p.val.1.2≠origin at ht
  have hs : p.val.1.1≠origin := by
    have hz := originStar_upper_zero p.val p.property
    intro he
    simp [originStar,he] at hz
  simp [interiorGauge,rootGauge,ribbonInterior,ht,hs]

theorem fullAction_root (V : SU2) (b : Boundary → SU2) (s : InteriorState) :
    FourCubeBoundaryCubic.fullAction (fill b (interiorGauge (rootGauge V) s))=
      FourCubeBoundaryCubic.fullAction (fill b s) := by
  simp only [action_decomposition,internalAction_gauge]
  congr 1
  unfold ribbonSum ribbonChannel linkProbe
  apply Finset.sum_congr rfl
  intro p _
  rw [ribbon_root]

theorem fullAction_fillPole (V : SU2) (b : Boundary → SU2) (y : PinnedState) :
    FourCubeBoundaryCubic.fullAction (fill b (fillPole V (rootLeft V y)))=
      FourCubeBoundaryCubic.fullAction (fill b (fillPole 1 y)) := by
  rw [fillPole_rootLeft,fullAction_root]

theorem fillPole_measurable : Measurable (fun p : SU2 × PinnedState => fillPole p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro e
  by_cases h : e=pole
  · simpa only [fillPole,dif_pos h] using (measurable_fst : Measurable (fun p : SU2 × PinnedState => p.1))
  · simpa only [fillPole,dif_neg h,Function.comp_def] using
      (measurable_pi_apply (⟨e,h⟩ : Free)).comp measurable_snd

def weight (β : ℝ) (b : Boundary → SU2) (s : InteriorState) : ℝ :=
  Real.exp (-β*FourCubeBoundaryCubic.fullAction (fill b s))

theorem weight_measurable (β : ℝ) (b : Boundary → SU2) : Measurable (weight β b) :=
  (measurable_const.mul (FourCubeHaarParity.fullAction_measurable.comp (fill_measurable b))).exp

theorem weight_bound (β : ℝ) (b : Boundary → SU2) (s : InteriorState) :
    |weight β b s|≤Real.exp (144*|β|) := by
  rw [weight,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hs := FourCubeHaarParity.fullAction_bounds (fill b s)
  have hb := neg_le_abs β
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) hs.1,
    mul_nonneg (abs_nonneg β) (sub_nonneg.mpr hs.2)]

def partition (β : ℝ) (b : Boundary → SU2) : ℝ := ∫ s,weight β b s ∂interiorHaar
def pinnedPartition (β : ℝ) (b : Boundary → SU2) : ℝ :=
  ∫ y,weight β b (fillPole 1 y) ∂pinnedHaar

theorem conditional_pole_integral (β : ℝ) (b : Boundary → SU2) (V : SU2) :
    (∫ y,weight β b (fillPole V y) ∂pinnedHaar)=pinnedPartition β b := by
  have hm : Measurable (fun y => weight β b (fillPole V y)) :=
    (weight_measurable β b).comp (fillPole_measurable.comp (measurable_const.prodMk measurable_id))
  have hh := integral_map (μ := pinnedHaar) (rootLeft_preserving V).measurable.aemeasurable
    hm.aestronglyMeasurable
  rw [(rootLeft_preserving V).map_eq] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards with y
  unfold weight
  rw [fullAction_fillPole]


abbrev PoleIndex := {e : Interior // e=pole}
def poleHaar : Measure (PoleIndex → SU2) :=
  @Measure.pi PoleIndex (fun _ => SU2) (Subtype.fintype (fun e : Interior => e=pole))
    (fun _ => inferInstance) (fun _ => law)
instance poleHaar_probability : IsProbabilityMeasure poleHaar := by
  unfold poleHaar
  infer_instance

def split : InteriorState ≃ᵐ ((PoleIndex → SU2) × PinnedState) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Interior => SU2) (fun e => e=pole)

theorem split_preserving : MeasurePreserving split interiorHaar (poleHaar.prod pinnedHaar) := by
  simpa only [split,interiorHaar,poleHaar,pinnedHaar] using
    measurePreserving_piEquivPiSubtypeProd (fun _ : Interior => law) (fun e => e=pole)

theorem split_reconstruct (s : InteriorState) :
    fillPole ((split s).1 ⟨pole,rfl⟩) (split s).2=s := by
  funext e
  by_cases h : e=pole
  · subst e
    rfl
  · simp [fillPole,h,split,MeasurableEquiv.piEquivPiSubtypeProd]

/-- Exact normalized gauge-volume factor1, for arbitrary boundary data and every real beta. -/
theorem partition_eq_pinned (β : ℝ) (b : Boundary → SU2) :
    partition β b=pinnedPartition β b := by
  let G := fun p : (PoleIndex → SU2) × PinnedState =>
    weight β b (fillPole (p.1 ⟨pole,rfl⟩) p.2)
  have hpair : Measurable (fun p : (PoleIndex → SU2) × PinnedState =>
      (p.1 ⟨pole,rfl⟩,p.2)) :=
    ((measurable_pi_apply (⟨pole,rfl⟩ : PoleIndex)).comp measurable_fst).prodMk measurable_snd
  have hm : Measurable G := by
    simpa only [G,Function.comp_def] using
      (weight_measurable β b).comp (fillPole_measurable.comp hpair)
  have hi : Integrable G (poleHaar.prod pinnedHaar) := by
    apply (integrable_const (Real.exp (144*|β|))).mono' hm.aestronglyMeasurable
    filter_upwards with p
    simpa only [Real.norm_eq_abs] using weight_bound β b (fillPole (p.1 ⟨pole,rfl⟩) p.2)
  calc
    partition β b=∫ p,G p ∂(poleHaar.prod pinnedHaar) := by
      have he := split_preserving.integral_comp' G
      simpa only [partition,G,split_reconstruct] using he
    _ = ∫ a,∫ y,G (a,y) ∂pinnedHaar ∂poleHaar := integral_prod G hi
    _ = pinnedPartition β b := by
      simp only [G,conditional_pole_integral]
      simp

/-- The already verified three-axis FULL32-link partition has the same31-link pin. -/
theorem partition3_eq_pinned (β x y z : ℝ) :
    FourCubeIntegratedResponse.partition3 x y z β=
      pinnedPartition β (boundaryData x y z) := by
  rw [← partition_eq_pinned]
  simp only [FourCubeIntegratedResponse.partition3,FourCubeIntegratedResponse.source,
    ProbabilityTheory.mgf,cellAction,partition,weight,mul_neg,neg_mul]

theorem partition_positive (β : ℝ) (b : Boundary → SU2) : 0<partition β b := by
  have hi : Integrable (weight β b) interiorHaar := by
    apply (integrable_const (Real.exp (144*|β|))).mono' (weight_measurable β b).aestronglyMeasurable
    filter_upwards with s
    simpa only [Real.norm_eq_abs] using weight_bound β b s
  unfold partition
  apply (integral_pos_iff_support_of_nonneg (fun s => (Real.exp_pos _).le) hi).mpr
  have hs : Function.support (weight β b)=Set.univ := by
    ext s
    simp [Function.mem_support,weight,Real.exp_ne_zero]
  change 0 < interiorHaar (Function.support (weight β b))
  rw [hs]
  simp

theorem pinnedPartition_positive (β : ℝ) (b : Boundary → SU2) :
    0<pinnedPartition β b := by
  rw [← partition_eq_pinned]
  exact partition_positive β b

end OperatorDerivativeRewrite.Foundation.FourCubePinnedHaar
