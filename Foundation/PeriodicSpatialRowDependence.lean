import Foundation.PeriodicLinkDisintegration
import Foundation.PeriodicLowActionBlock
import Foundation.PeriodicCenterSeam
import Foundation.PeriodicConditionalEndpointScore
import Mathlib.Probability.Kernel.CompProdEqIff

/-! Spatial dependence in the actual periodic augmented Wilson law.
Every spatial plaquette and both temporal fields remain in the original density. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.PeriodicSpatialRowDependence
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicLinkStaples
private abbrev vertexDecidableEq : DecidableEq SpatialVertex :=
  fun a b => Fintype.decidablePiFintype a b
attribute [local instance] vertexDecidableEq
attribute [local irreducible] boundaryHaar gaugeHaar spatialAction temporalAction
  incidentFaces spatialStaple

def edge : SpatialEdge := (0,0)
def neighbor : SpatialEdge := (shift 0 0,1)
def face01 : SpatialFace := ⟨(0,(0,1)),by decide⟩
def face02 : SpatialFace := ⟨(0,(0,2)),by decide⟩
def back01 : SpatialFace := ⟨(backshift 0 1,(0,1)),by decide⟩
def back02 : SpatialFace := ⟨(backshift 0 2,(0,2)),by decide⟩

theorem edge_ne_neighbor : edge≠neighbor := by decide

theorem incident_exact : incidentFaces edge={face01,face02,back01,back02} := by
  have h0 : face01∈incidentFaces edge := (mem_incidentFaces _ _).mpr ⟨0,rfl⟩
  have h1 : face02∈incidentFaces edge := (mem_incidentFaces _ _).mpr ⟨0,rfl⟩
  have h2 : back01∈incidentFaces edge := by
    apply (mem_incidentFaces _ _).mpr
    refine ⟨2,?_⟩
    simp [faceEdge,back01,edge]
    funext k
    simp [PeriodicTemporalSlab.shift,backshift]
  have h3 : back02∈incidentFaces edge := by
    apply (mem_incidentFaces _ _).mpr
    refine ⟨2,?_⟩
    simp [faceEdge,back02,edge]
    funext k
    simp [PeriodicTemporalSlab.shift,backshift]
  have hs : {face01,face02,back01,back02}⊆incidentFaces edge := by
    intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  have hc : ({face01,face02,back01,back02}:Finset SpatialFace).card=4 := by decide
  exact (Finset.eq_of_subset_of_card_le hs ((incidentFaces_card_le edge).trans_eq hc.symm)).symm

def field (B : SU2) : State := Function.update 1 neighbor B

theorem field_edge (B : SU2) : field B edge=1 := by
  rw [field,Function.update_of_ne edge_ne_neighbor]
  rfl

theorem field_update_one (B : SU2) : Function.update (field B) edge 1=field B := by
  rw [← field_edge B,Function.update_eq_self]

theorem incident_trace_sum (B : SU2) :
    (∑ p ∈ incidentFaces edge,halfTrace (spatialWord (field B) p))=3+halfTrace B := by
  rw [incident_exact]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),Finset.sum_singleton]
  have h01 : (0:ZMod 4)≠1 := by decide
  have h10 : (1:ZMod 4)≠0 := by decide
  norm_num [spatialWord,field,face01,face02,back01,back02,neighbor,edge,
    PeriodicTemporalSlab.shift,backshift,Function.update_apply,funext_iff,Fin.forall_fin_succ,h01,h10,
    SU2WilsonConvolution.halfTrace_inv,
    SU2OpenLinkGaugeObstruction.halfTrace_one]
  <;> ring

theorem row_action_difference (B : SU2) :
    PeriodicAugmentedBridge.centralAction 1 1
      (Function.update (field B) edge SU2StapleExtremes.minusOne,(1,1))-
      PeriodicAugmentedBridge.centralAction 1 1 (field B,(1,1))=10+2*halfTrace B := by
  have hs := spatial_action_change (field B) edge SU2StapleExtremes.minusOne
  simp_rw [SU2StrongCouplingCovariance.halfTrace_center_neg] at hs
  have he (p : SpatialFace) (hp : p∈incidentFaces edge) :
      halfTrace (spatialStaple (field B) edge p)=halfTrace (spatialWord (field B) p) := by
    have hh := spatial_trace_incident (field B) edge p hp 1
    rw [field_update_one,one_mul] at hh
    exact hh.symm
  rw [Finset.sum_congr rfl (fun p hp => by rw [he p hp])] at hs
  have hsum : (∑ p ∈ incidentFaces edge,
      (halfTrace (spatialWord (field B) p)- -halfTrace (spatialWord (field B) p)))=
      2*(3+halfTrace B) := by
    simp_rw [sub_neg_eq_add,← two_mul]
    rw [← Finset.mul_sum,incident_trace_sum]
  rw [field_update_one,hsum] at hs
  have hl := temporal_action_change_left (1:State) (field B) (1:Gauge) edge SU2StapleExtremes.minusOne
  have hr := temporal_action_change_right (field B) (1:State) (1:Gauge) edge SU2StapleExtremes.minusOne
  have hminus : halfTrace SU2StapleExtremes.minusOne= -1 := by
    simpa only [mul_one,SU2OpenLinkGaugeObstruction.halfTrace_one] using
      SU2StrongCouplingCovariance.halfTrace_center_neg (1:SU2)
  simp only [leftTemporal,rightTemporal,Pi.one_apply,inv_one,one_mul,mul_one,
    hminus,SU2OpenLinkGaugeObstruction.halfTrace_one,
    field_update_one] at hl hr
  unfold PeriodicAugmentedBridge.centralAction
  dsimp only
  linarith

abbrev Space := PeriodicAugmentedBridge.Space

def frozen (B : SU2) : Space := (field B,(1,1))
def raw (β : ℝ) (q : Space) (A : SU2) : ℝ :=
  localDensity β 1 q.1 1 q.2.1 q.2.2 edge A
def odds (β : ℝ) (q : Space) : ℝ := raw β q 1/raw β q SU2StapleExtremes.minusOne
def row (β : ℝ) (q : Space) : Measure SU2 := linkLaw β 1 q.1 1 q.2.1 q.2.2 edge

theorem raw_pos (β : ℝ) (q : Space) (A : SU2) : 0<raw β q A :=
  PeriodicAugmentedBridge.density_pos β 1 1 _

theorem raw_joint_continuous (β : ℝ) : Continuous (fun p : Space × SU2 => raw β p.1 p.2) := by
  have hu : Continuous (fun p : Space × SU2 => Function.update p.1.1 edge p.2) :=
    (continuous_fst.comp continuous_fst).update edge continuous_snd
  have hw : Continuous (fun p : (State × State) × Gauge => weight β p.1.1 p.1.2 p.2) := by
    unfold weight
    exact Real.continuous_exp.comp (PeriodicLowActionBlock.action_continuous.const_mul (-β))
  have h1 : Continuous (fun p : Space × SU2 =>
      (((1:State),Function.update p.1.1 edge p.2),p.1.2.1)) :=
    (continuous_const.prodMk hu).prodMk (continuous_fst.comp (continuous_snd.comp continuous_fst))
  have h2 : Continuous (fun p : Space × SU2 =>
      ((Function.update p.1.1 edge p.2,(1:State)),p.1.2.2)) :=
    (hu.prodMk continuous_const).prodMk (continuous_snd.comp (continuous_snd.comp continuous_fst))
  exact (hw.comp h1).mul (hw.comp h2)

theorem raw_continuous (β : ℝ) (q : Space) : Continuous (raw β q) :=
  (raw_joint_continuous β).comp (continuous_const.prodMk continuous_id)

theorem odds_continuous (β : ℝ) : Continuous (odds β) :=
  ((raw_joint_continuous β).comp (continuous_id.prodMk continuous_const)).div
    ((raw_joint_continuous β).comp (continuous_id.prodMk continuous_const))
    (fun q => (raw_pos β q _).ne')

theorem odds_frozen (β : ℝ) (B : SU2) :
    odds β (frozen B)=Real.exp (β*(10+2*halfTrace B)) := by
  unfold odds raw localDensity frozen
  dsimp only
  rw [field_update_one,PeriodicAugmentedBridge.density_phase,PeriodicAugmentedBridge.density_phase,
    ← Real.exp_add,← Real.exp_add,← Real.exp_sub]
  congr 1
  linear_combination β*row_action_difference B

theorem odds_separation (β : ℝ) (hβ : β≠0) :
    odds β (frozen 1)≠odds β (frozen SU2StapleExtremes.minusOne) := by
  have hm : halfTrace SU2StapleExtremes.minusOne= -1 := by
    simpa only [mul_one,SU2OpenLinkGaugeObstruction.halfTrace_one] using
      SU2StrongCouplingCovariance.halfTrace_center_neg (1:SU2)
  rw [odds_frozen,odds_frozen,SU2OpenLinkGaugeObstruction.halfTrace_one,hm]
  intro hh
  have he := Real.exp_injective hh
  exact hβ (by linarith)

theorem augmented_ae_iff (β : ℝ) (P : Space → Prop) :
    (∀ᵐ q ∂PeriodicAugmentedBridge.law β 1 1,P q) ↔ ∀ᵐ q ∂PeriodicAugmentedBridge.reference,P q := by
  rw [PeriodicLinkDisintegration.augmented_withDensity,ae_withDensity_iff
    ((PeriodicAugmentedBridge.density_measurable β 1 1).div_const _).ennreal_ofReal]
  constructor
  · intro hh
    filter_upwards [hh] with q hq
    exact hq (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos
      (PeriodicAugmentedBridge.density_pos β 1 1 q) (PeriodicGroundBridge.normalizer_pos β 1 1))))
  · intro hh
    filter_upwards [hh] with q hq
    exact fun _ => hq

private instance reference_open : PeriodicAugmentedBridge.reference.IsOpenPosMeasure := by
  unfold PeriodicAugmentedBridge.reference boundaryHaar gaugeHaar
  infer_instance

/-- Actual-law nonconstancy, not a claim from two frozen zero-measure configurations. -/
theorem odds_not_ae_constant (β : ℝ) (hβ : β≠0) (c : ℝ) :
    ¬ ∀ᵐ q ∂PeriodicAugmentedBridge.law β 1 1,odds β q=c := by
  intro hh
  have he := Measure.eq_of_ae_eq ((augmented_ae_iff β _).mp hh) (odds_continuous β) continuous_const
  exact odds_separation β hβ ((congrFun he (frozen 1)).trans
    (congrFun he (frozen SU2StapleExtremes.minusOne)).symm)

def rowPartition (β : ℝ) (q : Space) : ℝ := ∫ A,raw β q A ∂law
def rowDensity (β : ℝ) (q : Space) (A : SU2) : ℝ := raw β q A/rowPartition β q

theorem rowPartition_pos (β : ℝ) (q : Space) : 0<rowPartition β q :=
  localDensity_integral_pos β 1 q.1 1 q.2.1 q.2.2 edge

theorem rowDensity_continuous (β : ℝ) (q : Space) : Continuous (rowDensity β q) :=
  (raw_continuous β q).div_const _

theorem rowDensity_pos (β : ℝ) (q : Space) (A : SU2) : 0<rowDensity β q A :=
  div_pos (raw_pos β q A) (rowPartition_pos β q)

theorem row_density (β : ℝ) (q : Space) :
    row β q=law.withDensity (fun A => ENNReal.ofReal (rowDensity β q A)) := rfl

/-- Normalizing the actual row does not change these odds. -/
theorem rowDensity_odds (β : ℝ) (q : Space) :
    rowDensity β q 1/rowDensity β q SU2StapleExtremes.minusOne=odds β q :=
  div_div_div_cancel_right₀ (rowPartition_pos β q).ne' _ _

theorem row_eq_implies_odds (β : ℝ) (q r : Space) (h : row β q=row β r) : odds β q=odds β r := by
  rw [row_density,row_density] at h
  have he := (withDensity_eq_iff_of_sigmaFinite
    (rowDensity_continuous β q).measurable.ennreal_ofReal.aemeasurable
    (rowDensity_continuous β r).measurable.ennreal_ofReal.aemeasurable).mp h
  have hre : rowDensity β q =ᵐ[law] rowDensity β r := by
    filter_upwards [he] with A hA
    have hh := congrArg ENNReal.toReal hA
    simpa only [ENNReal.toReal_ofReal (rowDensity_pos β q A).le,
      ENNReal.toReal_ofReal (rowDensity_pos β r A).le] using hh
  have hp := Measure.eq_of_ae_eq hre (rowDensity_continuous β q) (rowDensity_continuous β r)
  rw [← rowDensity_odds,← rowDensity_odds,hp]

theorem row_not_ae_constant (β : ℝ) (hβ : β≠0) (ν : Measure SU2) :
    ¬ ∀ᵐ q ∂PeriodicAugmentedBridge.law β 1 1,row β q=ν := by
  intro hh
  obtain ⟨r,hr⟩ := hh.exists
  apply odds_not_ae_constant β hβ (odds β r)
  filter_upwards [hh] with q hq
  exact row_eq_implies_odds β q r (hq.trans hr.symm)

theorem row_is_conditional (β : ℝ) (q : Space) :
    row β q=PeriodicLinkDisintegration.conditionalKernel edge β 1 1
      ((PeriodicLinkDisintegration.split edge q).1) := by
  have hh := PeriodicLinkDisintegration.assemble edge
    ((PeriodicLinkDisintegration.split edge q).1) ((PeriodicLinkDisintegration.split edge q).2)
  rw [Prod.eta,(PeriodicLinkDisintegration.split edge).symm_apply_apply] at hh
  have hb : Function.update
      (PeriodicLinkDisintegration.baseField edge ((PeriodicLinkDisintegration.split edge q).1))
      edge (q.1 edge)=q.1 := by
    simpa only [PeriodicLinkDisintegration.split_apply] using (congrArg Prod.fst hh).symm
  have hu (A : SU2) : Function.update
      (PeriodicLinkDisintegration.baseField edge ((PeriodicLinkDisintegration.split edge q).1))
      edge A=Function.update q.1 edge A := by
    rw [← hb,Function.update_idem]
  rw [PeriodicLinkDisintegration.kernel_eq_linkLaw]
  unfold row linkLaw localDensity
  simp_rw [hu]
  have ht : ((PeriodicLinkDisintegration.split edge q).1.2)=q.2 := rfl
  simp_rw [ht]

/-- Nonconstancy belongs to the correctly partition-weighted actual rest marginal. -/
theorem conditional_not_ae_constant (β : ℝ) (hβ : β≠0) (ν : Measure SU2) :
    ¬ ∀ᵐ r ∂PeriodicLinkDisintegration.marginal edge β 1 1,
      PeriodicLinkDisintegration.conditionalKernel edge β 1 1 r=ν := by
  intro hh
  apply row_not_ae_constant β hβ ν
  have hp := (PeriodicConditionalEndpointScore.rest_preserving edge β 1 1).quasiMeasurePreserving.ae hh
  filter_upwards [hp] with q hq
  rw [row_is_conditional]
  exact hq

/-- The actual selected-link/rest disintegration is not an independent product.
The conclusion concerns the full slab law, not a frozen-rest surrogate. -/
theorem no_product_joint (β : ℝ) (hβ : β≠0) (ν : Measure SU2) [IsProbabilityMeasure ν] :
    (PeriodicAugmentedBridge.law β 1 1).map (PeriodicLinkDisintegration.split edge)≠
      (PeriodicLinkDisintegration.marginal edge β 1 1).prod ν := by
  letI := PeriodicLinkDisintegration.kernel_markov edge β 1 1
  letI := PeriodicLinkDisintegration.marginal_probability edge β 1 1
  intro hh
  apply conditional_not_ae_constant β hβ ν
  have he : (PeriodicLinkDisintegration.marginal edge β 1 1) ⊗ₘ
      (PeriodicLinkDisintegration.conditionalKernel edge β 1 1)=
      (PeriodicLinkDisintegration.marginal edge β 1 1) ⊗ₘ
        (Kernel.const (PeriodicLinkDisintegration.Rest edge) ν) := by
    rw [← PeriodicLinkDisintegration.actual_factorization,hh,Measure.compProd_const]
  exact Kernel.ae_eq_of_compProd_eq he

theorem raw_zero (q : Space) (A : SU2) : raw 0 q A=1 := by
  simp [raw,localDensity,PeriodicAugmentedBridge.density,weight]

theorem row_zero (q : Space) : row 0 q=law := by
  rw [row_density]
  simp only [rowDensity,rowPartition,raw_zero,integral_const,probReal_univ,
    one_smul,div_one,ENNReal.ofReal_one]
  change law.withDensity 1=law
  exact withDensity_one

theorem conditional_zero (r : PeriodicLinkDisintegration.Rest edge) :
    PeriodicLinkDisintegration.conditionalKernel edge 0 1 1 r=law := by
  have hh := row_is_conditional 0 ((PeriodicLinkDisintegration.split edge).symm (r,1))
  rw [(PeriodicLinkDisintegration.split edge).apply_symm_apply,row_zero] at hh
  exact hh.symm

theorem zero_product_joint :
    (PeriodicAugmentedBridge.law 0 1 1).map (PeriodicLinkDisintegration.split edge)=
      (PeriodicLinkDisintegration.marginal edge 0 1 1).prod law := by
  letI := PeriodicLinkDisintegration.marginal_probability edge 0 1 1
  rw [PeriodicLinkDisintegration.actual_factorization]
  have he : PeriodicLinkDisintegration.conditionalKernel edge 0 1 1=
      Kernel.const (PeriodicLinkDisintegration.Rest edge) law := by
    ext r s hs
    rw [conditional_zero]
    rfl
  rw [he,Measure.compProd_const]

def neighborFlip (q : Space) : Space := (field SU2StapleExtremes.minusOne*q.1,q.2)
def eraseNeighbor (q : Space) : Space := (Function.update q.1 neighbor 1,q.2)

theorem neighborFlip_continuous : Continuous neighborFlip :=
  (continuous_const.mul continuous_fst).prodMk continuous_snd

theorem neighborFlip_frozen : neighborFlip (frozen 1)=frozen SU2StapleExtremes.minusOne := by
  have h1 : field (1:SU2)=1 := Function.update_eq_self _ _
  change (field SU2StapleExtremes.minusOne*field 1,(1,1))=(field SU2StapleExtremes.minusOne,(1,1))
  rw [h1,mul_one]

theorem neighborFlip_reference_preserving : MeasurePreserving neighborFlip
    PeriodicAugmentedBridge.reference PeriodicAugmentedBridge.reference := by
  have hp : MeasurePreserving (fun V : State => field SU2StapleExtremes.minusOne*V)
      boundaryHaar boundaryHaar := by
    unfold boundaryHaar
    exact measurePreserving_pi (fun _ => law) (fun _ => law)
      (fun e => measurePreserving_mul_left law (field SU2StapleExtremes.minusOne e))
  exact hp.prod (MeasurePreserving.id (gaugeHaar.prod gaugeHaar))

/-- Nonsingularity of this coordinate change, NOT Gibbs-law invariance. -/
theorem neighborFlip_ae (β : ℝ) (P : Space → Prop)
    (hh : ∀ᵐ q ∂PeriodicAugmentedBridge.law β 1 1,P q) :
    ∀ᵐ q ∂PeriodicAugmentedBridge.law β 1 1,P (neighborFlip q) := by
  exact (augmented_ae_iff β _).mpr
    (neighborFlip_reference_preserving.quasiMeasurePreserving.ae ((augmented_ae_iff β P).mp hh))

theorem eraseNeighbor_flip (q : Space) : eraseNeighbor (neighborFlip q)=eraseNeighbor q := by
  apply Prod.ext
  · change Function.update (field SU2StapleExtremes.minusOne*q.1) neighbor 1=
      Function.update q.1 neighbor 1
    funext j
    by_cases hj : j=neighbor
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hj,Pi.mul_apply,field,one_mul]
      simp
  · rfl

/-- Actual neighbor influence holds beyond isolated frozen configurations. -/
theorem row_not_ae_neighbor_invariant (β : ℝ) (hβ : β≠0) :
    ¬ ∀ᵐ q ∂PeriodicAugmentedBridge.law β 1 1,row β (neighborFlip q)=row β q := by
  intro hh
  have ho : ∀ᵐ q ∂PeriodicAugmentedBridge.reference,odds β (neighborFlip q)=odds β q := by
    apply (augmented_ae_iff β _).mp
    filter_upwards [hh] with q hq
    exact row_eq_implies_odds β _ _ hq
  have he := Measure.eq_of_ae_eq ho ((odds_continuous β).comp neighborFlip_continuous)
    (odds_continuous β)
  have ht := congrFun he (frozen 1)
  rw [neighborFlip_frozen] at ht
  exact odds_separation β hβ ht.symm

/-- No almost-everywhere version of the original conditional row can drop this
neighbor while retaining all other spatial and temporal coordinates. -/
theorem no_neighbor_erased_version (β : ℝ) (hβ : β≠0) :
    ¬ ∃ J : Space → Measure SU2, ∀ᵐ q ∂PeriodicAugmentedBridge.law β 1 1,
      row β q=J (eraseNeighbor q) := by
  rintro ⟨J,hJ⟩
  have hF := neighborFlip_ae β _ hJ
  apply row_not_ae_neighbor_invariant β hβ
  filter_upwards [hJ,hF] with q hq hf
  exact hf.trans ((congrArg J (eraseNeighbor_flip q)).trans hq.symm)

end OperatorDerivativeRewrite.Foundation.PeriodicSpatialRowDependence
