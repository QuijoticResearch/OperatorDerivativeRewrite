import Foundation.QuaternionTiltCovariance
import Foundation.PeriodicPlaquetteVarianceLower
import Foundation.PeriodicCurvatureWeighted

/-! A genuine lower-rate obstruction for the actual stationary mixed moment.
Unit-quaternion geometry bounds a product of two trace deficits below by a
centered unit-coordinate square. The proved covariance floor therefore survives
the actual one-link conditional law and true augmented disintegration. A direct
ground-weighted left-moment identity transports it to the actual stationary
triple law, retaining both temporal integrations and all eigenvalue factors.
The scaled mixed moment cannot tend to zero. This blocks one sufficient route
using a coarse variance lower bound; it does not rule out normalized local
slowing or establish a continuum or infinite-volume physical mass gap. -/

noncomputable section
open scoped Quaternion
open OperatorDerivativeRewrite.Foundation
open QuaternionAngularHaar QuaternionTiltCovariance
namespace OperatorDerivativeRewrite.Foundation.PeriodicMixedMomentObstruction

private theorem unit_normSq (q : Group) : Quaternion.normSq (q:ℍ)=1 := by
  rw [Quaternion.normSq_eq_norm_mul_self,CStarRing.norm_coe_unitary,one_mul]

theorem real_product_gram (h q : Group) :
    0 ≤ 1-realCoordinate h^2-realCoordinate q^2-realCoordinate (h*q)^2+
      2*realCoordinate h*realCoordinate q*realCoordinate (h*q) := by
  let x : ℍ := ⟨0,(h:ℍ).imI,(h:ℍ).imJ,(h:ℍ).imK⟩
  let y : ℍ := ⟨0,(q:ℍ).imI,(q:ℍ).imJ,(q:ℍ).imK⟩
  have hx : Quaternion.normSq x = 1-realCoordinate h^2 := by
    have hh := unit_normSq h
    norm_num [x,realCoordinate,Quaternion.normSq_def'] at hh ⊢
    nlinarith
  have hy : Quaternion.normSq y = 1-realCoordinate q^2 := by
    have hh := unit_normSq q
    norm_num [y,realCoordinate,Quaternion.normSq_def'] at hh ⊢
    nlinarith
  have he : inner ℝ x y = realCoordinate h*realCoordinate q-realCoordinate (h*q) := by
    simp [x,y,realCoordinate,Quaternion.inner_def]
    ring
  have hc := real_inner_mul_inner_self_le x y
  rw [he,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hc
  simp only [pow_two,← Quaternion.normSq_eq_norm_mul_self,hx,hy] at hc
  nlinarith


theorem exists_deficit_square (h : Group) : ∃ u : Group, ∃ a : ℝ, ∀ q : Group,
    (realCoordinate (u*q)-a)^2 ≤ (1-realCoordinate q)*(1-realCoordinate (h*q)) := by
  by_cases hz : 1+(h:ℍ)=0
  · refine ⟨axis 0,0,?_⟩
    intro q
    have hh : (h:ℍ) = -1 := eq_neg_of_add_eq_zero_left
      (show (h:ℍ)+1=0 by simpa only [add_comm] using hz)
    have ht : realCoordinate (h*q) = -realCoordinate q := by
      change (((h:ℍ)*(q:ℍ)).re) = -(q:ℍ).re
      rw [hh]
      simp
    have hu : realCoordinate (axis 0*q) = -(q:ℍ).imI := by
      change ((QuaternionTiltWard.rawRotation 0 (Real.pi/2))*(q:ℍ)).re = _
      norm_num [QuaternionTiltWard.rawRotation,Quaternion.re_mul]
    have hq := unit_normSq q
    rw [ht,hu]
    norm_num [realCoordinate,Quaternion.normSq_def'] at hq ⊢
    nlinarith [sq_nonneg (q:ℍ).imJ,sq_nonneg (q:ℍ).imK]
  · let z : ℍ := 1+(h:ℍ)
    let n : ℝ := ‖z‖
    let u : Group := SU2StaplePolar.direction z
    have hnp : 0<n := norm_pos_iff.mpr hz
    have hd : (u:ℍ) = NormedSpace.normalize z := by
      simp only [u,SU2StaplePolar.direction,dite_eq_right (show z ≠ 0 from hz)]
    have hp : n • (u:ℍ) = z := by
      rw [hd]
      exact NormedSpace.norm_smul_normalize z
    have hn : n^2=2*(1+realCoordinate h) := by
      have hh := unit_normSq h
      change ‖1+(h:ℍ)‖^2 = _
      rw [pow_two,← Quaternion.normSq_eq_norm_mul_self]
      norm_num [realCoordinate,Quaternion.normSq_def'] at hh ⊢
      nlinarith
    refine ⟨u,n/2,?_⟩
    intro q
    have hr : n*realCoordinate (u*q) = realCoordinate q+realCoordinate (h*q) := by
      have he := congrArg (fun w : ℍ => (w*(q:ℍ)).re) hp
      simp [realCoordinate,z] at he ⊢
      nlinarith [he]
    have hg := real_product_gram h q
    have hs : (n*realCoordinate (u*q)-n^2/2)^2 ≤
        n^2*((1-realCoordinate q)*(1-realCoordinate (h*q))) := by
      rw [hr,hn]
      nlinarith
    have he : (n*realCoordinate (u*q)-n^2/2)^2 = n^2*(realCoordinate (u*q)-n/2)^2 := by ring
    rw [he] at hs
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hnp)).mp hs


open QuaternionSU2Representation
theorem su2_exists_deficit_square (C D : SU2) : ∃ E : SU2, ∃ a : ℝ, ∀ A : SU2,
    (halfTrace (E*A)-a)^2 ≤ (1-halfTrace (C*A))*(1-halfTrace (D*A)) := by
  obtain ⟨c,rfl⟩ := hom_surjective C
  obtain ⟨d,rfl⟩ := hom_surjective D
  obtain ⟨u,a,hu⟩ := exists_deficit_square (d*c⁻¹)
  refine ⟨hom (u*c),a,?_⟩
  intro A
  obtain ⟨q,rfl⟩ := hom_surjective A
  have h := hu (c*q)
  have he : (d*c⁻¹)*(c*q)=d*q := by group
  rw [he] at h
  simpa only [← hom.map_mul,halfTrace_map,mul_assoc] using h


open MeasureTheory ProbabilityTheory PeriodicTemporalSlab PeriodicLinkDisintegration
theorem conditional_deficit_product_lower (e : SpatialEdge) (β : ℝ) (hβ : 0 ≤ β)
    (U W : State) (r : Rest e) (C D : SU2) :
    6/(49*(1+6*β)^2) ≤ ∫ A, (1-halfTrace (C*A))*(1-halfTrace (D*A))
      ∂conditionalKernel e β U W r := by
  let := kernel_markov e β U W
  have hm (E : SU2) : Measurable (fun A : SU2 => halfTrace (E*A)) :=
    halfTrace_measurable.comp (measurable_const.mul measurable_id)
  have hl (E : SU2) : MemLp (fun A : SU2 => halfTrace (E*A)) 2
      (conditionalKernel e β U W r) :=
    MemLp.of_bound (hm E).aestronglyMeasurable 1
      (ae_of_all _ (fun A => by simpa only [Real.norm_eq_abs] using halfTrace_bound (E*A)))
  have hd (E : SU2) : MemLp (fun A : SU2 => 1-halfTrace (E*A)) 2
      (conditionalKernel e β U W r) := (memLp_const 1).sub (hl E)
  have hi : Integrable (fun A => (1-halfTrace (C*A))*(1-halfTrace (D*A)))
      (conditionalKernel e β U W r) := (hd C).integrable_mul (hd D)
  obtain ⟨E,a,he⟩ := su2_exists_deficit_square C D
  have hs := ((hl E).sub (memLp_const a)).integrable_sq
  exact (PeriodicPlaquetteVarianceLower.centered_fiber e β hβ U W r E a).trans
    (integral_mono hs hi he)


open PeriodicWilsonSlab PeriodicLinkStaples SU2WilsonConvolution
def leftProduct (U : State) (p : SpatialFace) (q : PeriodicAugmentedBridge.Space) : ℝ :=
  (1-halfTrace (temporalWord U q.1 q.2.1 (faceEdge p 0)))*
    (1-PeriodicCurvatureVariance.plaquette p q.1)

theorem leftProduct_measurable (U : State) (p : SpatialFace) : Measurable (leftProduct U p) := by
  unfold leftProduct
  apply Measurable.mul
  · apply Measurable.sub measurable_const
    apply halfTrace_measurable.comp
    unfold temporalWord
    fun_prop
  · exact measurable_const.sub ((PeriodicCurvatureVariance.plaquette_measurable p).comp measurable_fst)

private theorem deficit_bound (A : SU2) : |1-halfTrace A| ≤ 2 := by
  have h := abs_le.mp (halfTrace_bound A)
  rw [abs_le]
  constructor <;> linarith

theorem leftProduct_bound (U : State) (p : SpatialFace) (q : PeriodicAugmentedBridge.Space) :
    |leftProduct U p q| ≤ 4 := by
  unfold leftProduct PeriodicCurvatureVariance.plaquette
  rw [abs_mul]
  have h := mul_le_mul (deficit_bound (temporalWord U q.1 q.2.1 (faceEdge p 0)))
    (deficit_bound (spatialWord q.1 p)) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  norm_num at h ⊢
  exact h

attribute [local irreducible] split coordinateSplit baseField conditionalKernel marginal
theorem augmented_left_product_lower (p : SpatialFace) (β : ℝ) (hβ : 0 ≤ β) (U W : State) :
    6/(49*(1+6*β)^2) ≤ ∫ q, leftProduct U p q ∂PeriodicAugmentedBridge.law β U W := by
  let e := faceEdge p 0
  let f : Rest e × SU2 → ℝ := fun z => leftProduct U p ((split e).symm z)
  let := marginal_probability e β U W
  let := kernel_markov e β U W
  have hm : Measurable f := (leftProduct_measurable U p).comp (split e).symm.measurable
  have hi : Integrable f ((marginal e β U W) ⊗ₘ conditionalKernel e β U W) :=
    Integrable.of_bound hm.aestronglyMeasurable 4
      (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using leftProduct_bound U p ((split e).symm z)))
  have he (r : Rest e) : 6/(49*(1+6*β)^2) ≤ ∫ A, f (r,A) ∂conditionalKernel e β U W r := by
    have hf (A : SU2) : f (r,A) =
        (1-halfTrace (leftTemporal U r.2.1 e*A))*
          (1-halfTrace (faceRemainder (baseField e r) p 0*A)) := by
      dsimp [f,leftProduct,PeriodicCurvatureVariance.plaquette]
      rw [assemble]
      simp only
      rw [left_temporal_trace,spatial_trace_at_slot]
      simp only [halfTrace_mul_comm A]
    simp_rw [hf]
    exact conditional_deficit_product_lower e β hβ U W r _ _
  have h := integral_mono (integrable_const (6/(49*(1+6*β)^2))) hi.integral_compProd he
  simp only [integral_const,probReal_univ,one_smul,Kernel.prodMkLeft_apply,Kernel.const_apply] at h
  rw [← Measure.integral_compProd hi,← actual_factorization] at h
  rw [integral_map (split e).measurable.aemeasurable hm.aestronglyMeasurable] at h
  simpa only [f,MeasurableEquiv.symm_apply_apply] using h


open PeriodicSlabGround
attribute [local irreducible] PeriodicWilsonSlab.weight PeriodicWilsonSlab.kernel
  PeriodicWilsonSlab.boundaryHaar PeriodicWilsonSlab.gaugeHaar

theorem gauge_weight_eigen (β : ℝ) (g : GroundData β) (V : State) :
    (∫ b,∫ W,weight β V W b*g.function W ∂boundaryHaar ∂gaugeHaar)=g.value*g.function V := by
  have hm : Measurable (fun z : State × Gauge => weight β V z.1 z.2*g.function z.1) :=
    ((weight_joint_measurable β).comp (show Measurable
      (fun z : State × Gauge => ((V,z.1),z.2)) by fun_prop)).mul (g.measurable.comp measurable_fst)
  have hi : Integrable (fun z : State × Gauge => weight β V z.1 z.2*g.function z.1)
      (boundaryHaar.prod gaugeHaar) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (768*|β|)*|g.upper|)
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by unfold weight; exact Real.exp_pos _ : 0 < weight β V z.1 z.2)]
    exact mul_le_mul (weight_bounds β V z.1 z.2).2 ((g.bounds z.1).2.trans (le_abs_self _))
      (abs_nonneg _) (Real.exp_pos _).le
  rw [← integral_integral_swap hi]
  simp_rw [integral_mul_const]
  have he := g.eigen V
  unfold kernel at he
  exact he

theorem weighted_augmented_integrable (β : ℝ) (g : GroundData β) (U : State) (p : SpatialFace) :
    Integrable (fun z : State × PeriodicAugmentedBridge.Space =>
      PeriodicAugmentedBridge.density β U z.1 z.2*leftProduct U p z.2*g.function z.1)
      (boundaryHaar.prod PeriodicAugmentedBridge.reference) := by
  have h1 := (weight_joint_measurable β).comp (show Measurable
    (fun z : State × PeriodicAugmentedBridge.Space => ((U,z.2.1),z.2.2.1)) by fun_prop)
  have h2 := (weight_joint_measurable β).comp (show Measurable
    (fun z : State × PeriodicAugmentedBridge.Space => ((z.2.1,z.1),z.2.2.2)) by fun_prop)
  have hm : Measurable (fun z : State × PeriodicAugmentedBridge.Space =>
      PeriodicAugmentedBridge.density β U z.1 z.2*leftProduct U p z.2*g.function z.1) :=
    ((h1.mul h2).mul ((leftProduct_measurable U p).comp measurable_snd)).mul
      (g.measurable.comp measurable_fst)
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (768*|β|)^2*4*|g.upper|)
  filter_upwards with z
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (PeriodicAugmentedBridge.density_pos β U z.1 z.2)]
  exact mul_le_mul (mul_le_mul (PeriodicAugmentedBridge.density_upper β U z.1 z.2)
    (leftProduct_bound U p z.2) (abs_nonneg _) (sq_nonneg _))
    ((g.bounds z.1).2.trans (le_abs_self _)) (abs_nonneg _) (by positivity)


def rawLeft (β : ℝ) (U : State) (p : SpatialFace) (W : State) : ℝ :=
  ∫ q,PeriodicAugmentedBridge.density β U W q*leftProduct U p q ∂PeriodicAugmentedBridge.reference

def leftRow (β : ℝ) (g : GroundData β) (U : State) (p : SpatialFace) : ℝ :=
  ∫ V,(∫ a,weight β U V a*leftProduct U p (V,(a,1)) ∂gaugeHaar)*g.function V ∂boundaryHaar

theorem weighted_left_identity (β : ℝ) (g : GroundData β) (U : State) (p : SpatialFace) :
    (∫ W,rawLeft β U p W*g.function W ∂boundaryHaar)=g.value*leftRow β g U p := by
  have hi := weighted_augmented_integrable β g U p
  have he : (∫ W,rawLeft β U p W*g.function W ∂boundaryHaar)=
      ∫ q,∫ W,PeriodicAugmentedBridge.density β U W q*leftProduct U p q*g.function W
        ∂boundaryHaar ∂PeriodicAugmentedBridge.reference := by
    unfold rawLeft
    simp_rw [← integral_mul_const]
    exact integral_integral_swap hi
  have hV (V : State) :
      (∫ ab : Gauge × Gauge,∫ W,PeriodicAugmentedBridge.density β U W (V,ab)*
        leftProduct U p (V,ab)*g.function W ∂boundaryHaar ∂gaugeHaar.prod gaugeHaar)=
      (∫ a,weight β U V a*leftProduct U p (V,(a,1)) ∂gaugeHaar)*(g.value*g.function V) := by
    let L : Gauge → ℝ := fun a => weight β U V a*leftProduct U p (V,(a,1))
    let R : Gauge → ℝ := fun b => ∫ W,weight β V W b*g.function W ∂boundaryHaar
    have hp (a b : Gauge) :
        (∫ W,PeriodicAugmentedBridge.density β U W (V,(a,b))*
          leftProduct U p (V,(a,b))*g.function W ∂boundaryHaar)=L a*R b := by
      have hw (W : State) : PeriodicAugmentedBridge.density β U W (V,(a,b))*
          leftProduct U p (V,(a,b))*g.function W=L a*(weight β V W b*g.function W) := by
        dsimp [PeriodicAugmentedBridge.density,L,leftProduct]
        ring
      simp_rw [hw,integral_const_mul]
      rfl
    simp_rw [hp]
    rw [integral_prod_mul]
    have hr : (∫ b,R b ∂gaugeHaar)=g.value*g.function V := gauge_weight_eigen β g V
    rw [hr]
  rw [he,PeriodicAugmentedBridge.reference,integral_prod _ hi.integral_prod_right]
  simp_rw [hV]
  unfold leftRow
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with V
  ring


theorem weighted_normalizer (β : ℝ) (g : GroundData β) (U : State) :
    (∫ W,PeriodicGroundBridge.normalizer β U W*g.function W ∂boundaryHaar)=
      g.value^2*g.function U := by
  have hp (W : State) : PeriodicGroundBridge.normalizer β U W*g.function W=
      PeriodicGroundBridge.twoStepDensity g U W*(g.value^2*g.function U) := by
    rw [PeriodicGroundBridge.twoStep_factor]
    field_simp [g.value_pos.ne',(g.function_pos U).ne']
  simp_rw [hp,integral_mul_const,PeriodicGroundBridge.twoStep_integral,one_mul]

theorem left_row_lower (β : ℝ) (hβ : 0 ≤ β) (g : GroundData β) (U : State) (p : SpatialFace) :
    (6/(49*(1+6*β)^2))*g.value*g.function U ≤ leftRow β g U p := by
  let c : ℝ := 6/(49*(1+6*β)^2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hi : Integrable (fun W => rawLeft β U p W*g.function W) boundaryHaar := by
    simpa only [rawLeft,integral_mul_const] using
      (weighted_augmented_integrable β g U p).integral_prod_left
  have hp (W : State) : c*PeriodicGroundBridge.normalizer β U W ≤ rawLeft β U p W := by
    have h := augmented_left_product_lower p β hβ U W
    rw [PeriodicAugmentedBridge.integral_formula] at h
    exact (le_div_iff₀ (PeriodicGroundBridge.normalizer_pos β U W)).mp h
  have h := integral_mono_of_nonneg
    (ae_of_all boundaryHaar (fun W => mul_nonneg (mul_nonneg hc
      (PeriodicGroundBridge.normalizer_pos β U W).le) (g.function_pos W).le)) hi
    (ae_of_all _ (fun W => mul_le_mul_of_nonneg_right (hp W) (g.function_pos W).le))
  have he : (∫ W,c*PeriodicGroundBridge.normalizer β U W*g.function W ∂boundaryHaar)=
      c*(g.value^2*g.function U) := by
    calc
      _ = c*(∫ W,PeriodicGroundBridge.normalizer β U W*g.function W ∂boundaryHaar) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with W
        ring
      _ = _ := by rw [weighted_normalizer]
  rw [he,weighted_left_identity] at h
  have hh : g.value*(c*g.value*g.function U) ≤ g.value*leftRow β g U p := by nlinarith [h]
  exact (mul_le_mul_iff_right₀ g.value_pos).mp hh

open PeriodicSlabJoint
/-- The final temporal field is unused by leftProduct; its dummy value here
changes only an unused observable argument, never an integrated density. -/
def tripleProduct (p : SpatialFace) (q : Triple) : ℝ := leftProduct q.1.1 p (q.1.2,(q.2,1))

theorem tripleProduct_measurable (p : SpatialFace) : Measurable (tripleProduct p) := by
  unfold tripleProduct leftProduct
  apply Measurable.mul
  · apply Measurable.sub measurable_const
    apply halfTrace_measurable.comp
    unfold temporalWord
    fun_prop
  · exact measurable_const.sub ((PeriodicCurvatureVariance.plaquette_measurable p).comp
      (measurable_snd.comp measurable_fst))

theorem tripleProduct_bound (p : SpatialFace) (q : Triple) : |tripleProduct p q| ≤ 4 :=
  leftProduct_bound q.1.1 p (q.1.2,(q.2,1))

theorem raw_row_identity (β : ℝ) (g : GroundData β) (p : SpatialFace) (U : State) :
    (∫ V,∫ a,jointWeight g ((U,V),a)*tripleProduct p ((U,V),a)
      ∂gaugeHaar ∂boundaryHaar)=g.function U*leftRow β g U p := by
  unfold leftRow
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with V
  rw [← integral_mul_const,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with a
  dsimp [jointWeight,tripleProduct]
  ring

theorem stationary_triple_product_lower (β : ℝ) (hβ : 0 ≤ β) (g : GroundData β) (p : SpatialFace) :
    6/(49*(1+6*β)^2) ≤ ∫ q,tripleProduct p q ∂tripleLaw g := by
  let c : ℝ := 6/(49*(1+6*β)^2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hi := PeriodicSlabJoint.probe_integrable g (tripleProduct p) (tripleProduct_measurable p)
    4 (tripleProduct_bound p)
  have hi' : Integrable (fun UV : State × State =>
      ∫ a,jointWeight g (UV,a)*tripleProduct p (UV,a) ∂gaugeHaar)
      (boundaryHaar.prod boundaryHaar) := hi.integral_prod_left
  have h := integral_mono_of_nonneg
    (ae_of_all boundaryHaar (fun U => mul_nonneg (mul_nonneg hc g.value_pos.le) (sq_nonneg (g.function U))))
    hi'.integral_prod_left
    (ae_of_all _ (fun U => by
      dsimp only
      rw [raw_row_identity]
      have hh := mul_le_mul_of_nonneg_left (left_row_lower β hβ g U p) (g.function_pos U).le
      nlinarith [hh]))
  have he : (∫ U,c*g.value*g.function U^2 ∂boundaryHaar)=c*(g.value*g.normalizer) := by
    rw [integral_const_mul]
    unfold GroundData.normalizer
    ring
  rw [he] at h
  have hf : (∫ q,jointWeight g q*tripleProduct p q ∂PeriodicSlabJoint.reference)=
      ∫ U,∫ V,∫ a,jointWeight g ((U,V),a)*tripleProduct p ((U,V),a)
        ∂gaugeHaar ∂boundaryHaar ∂boundaryHaar := by
    rw [PeriodicSlabJoint.reference,integral_prod _ hi,integral_prod _ hi']
  rw [← hf] at h
  rw [PeriodicSlabJoint.integral_formula]
  exact (le_div_iff₀ (mul_pos g.value_pos g.normalizer_pos)).mpr h


open PeriodicTemporalConcentration PeriodicCurvatureWeighted PeriodicCurvatureVariance
theorem triple_product_le_mixed (p : SpatialFace) (q : Triple) :
    tripleProduct p q ≤ mixedEnergy p q := by
  have ht := Finset.single_le_sum (fun e (_ : e ∈ Finset.univ) =>
    FourCubePinnedCoercivity.defect_nonneg (temporalWord q.1.1 q.1.2 q.2 e))
      (Finset.mem_univ (faceEdge p 0))
  change 1-halfTrace (temporalWord q.1.1 q.1.2 q.2 (faceEdge p 0)) ≤ temporalEnergy q at ht
  have hu : 0 ≤ 1-plaquette p q.1.1 := by
    have h := (abs_le.mp (halfTrace_bound (spatialWord q.1.1 p))).2
    exact sub_nonneg.mpr h
  have hv : 0 ≤ 1-plaquette p q.1.2 := by
    have h := (abs_le.mp (halfTrace_bound (spatialWord q.1.2 p))).2
    exact sub_nonneg.mpr h
  have hd : 1-plaquette p q.1.2 ≤ pairedDefect p q := by
    unfold pairedDefect
    linarith
  exact mul_le_mul ht hd hv (temporal_bounds q).1

theorem stationary_mixed_lower (β : ℝ) (hβ : 0 ≤ β) (g : GroundData β) (p : SpatialFace) :
    6/(49*(1+6*β)^2) ≤ ∫ q,mixedEnergy p q ∂tripleLaw g := by
  have hp : Integrable (tripleProduct p) (tripleLaw g) :=
    Integrable.of_bound (tripleProduct_measurable p).aestronglyMeasurable 4
      (ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs] using tripleProduct_bound p q))
  exact (stationary_triple_product_lower β hβ g p).trans
    (integral_mono hp (mixed_integrable g p) (triple_product_le_mixed p))

theorem scaled_mixed_lower (β : ℝ) (hβ : 0 ≤ β) (g : GroundData β) (p : SpatialFace) :
    (6:ℝ)/49 ≤ (1+6*β)^2*(∫ q,mixedEnergy p q ∂tripleLaw g) := by
  have ht : 0 < 49*(1+6*β)^2 := by positivity
  have h := (div_le_iff₀ ht).mp (stationary_mixed_lower β hβ g p)
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 49)).mpr
  nlinarith [h]

open Filter
open scoped Topology
theorem actual_scaled_mixed_not_zero (p : SpatialFace) :
    ¬Tendsto (fun β : ℝ => (1+6*β)^2*(∫ q,mixedEnergy p q ∂tripleLaw (ground β)))
      atTop (𝓝 0) := by
  intro h
  have hs := (tendsto_order.mp h).2 ((6:ℝ)/49) (by norm_num)
  obtain ⟨β,hβ,hsmall⟩ := ((eventually_ge_atTop (0:ℝ)).and hs).exists
  have hl := scaled_mixed_lower β hβ (ground β) p
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicMixedMomentObstruction
