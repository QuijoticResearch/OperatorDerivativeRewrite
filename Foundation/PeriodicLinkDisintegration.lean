import Foundation.PeriodicLinkStaples
import Foundation.ExponentialJointDisintegration

/-! Genuine one-link disintegration of the actual periodic augmented Wilson law.
The Haar chart and density pushforward are explicit; the rest-field marginal is
reweighted by its partition function. No stationary variance or mass gap is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicLinkDisintegration
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicLinkStaples
set_option backward.isDefEq.respectTransparency false

private theorem split_constant_pi {I E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (i : I) :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => E) (fun j => j = i))
      (Measure.pi (fun _ : I => μ))
      ((Measure.pi (fun _ : {j : I // j = i} => μ)).prod
        (Measure.pi (fun _ : {j : I // j ≠ i} => μ))) := by
  have hF : (Subtype.fintype (fun j : I => j = i) : Fintype {j : I // j = i}) =
      (inferInstance : Fintype {j : I // j = i}) := Subsingleton.elim _ _
  have hμ := congrArg
    (fun F : Fintype {j : I // j = i} => @Measure.pi {j : I // j = i} (fun _ => E) F
      (fun _ => inferInstanceAs (MeasurableSpace E)) (fun _ => μ)) hF
  have h := measurePreserving_piEquivPiSubtypeProd (fun _ : I => μ) (fun j => j = i)
  rw [hμ] at h
  exact h

variable (e : SpatialEdge)



private instance targetUnique : Unique {j : SpatialEdge // j = e} where
  default := ⟨e,rfl⟩
  uniq j := Subtype.ext j.property

abbrev RestField := {j : SpatialEdge // j ≠ e} → SU2
abbrev Rest := RestField e × (Gauge × Gauge)

def restHaar : Measure (RestField e) := Measure.pi (fun _ => law)
instance restHaar_probability : IsProbabilityMeasure (restHaar e) := by unfold restHaar; infer_instance

def restReference : Measure (Rest e) := (restHaar e).prod (gaugeHaar.prod gaugeHaar)
instance restReference_probability : IsProbabilityMeasure (restReference e) := by
  unfold restReference; infer_instance

attribute [local irreducible] boundaryHaar gaugeHaar restHaar restReference

def coordinateSplit : State ≃ᵐ SU2 × RestField e :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : SpatialEdge => SU2) (fun j => j = e)).trans
    ((MeasurableEquiv.piUnique (fun _ : {j : SpatialEdge // j = e} => SU2)).prodCongr
      (MeasurableEquiv.refl _))

theorem coordinateSplit_preserving :
    MeasurePreserving (coordinateSplit e) boundaryHaar (law.prod (restHaar e)) := by
  have hs : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : SpatialEdge => SU2) (fun j => j = e))
      boundaryHaar ((Measure.pi (fun _ : {j : SpatialEdge // j = e} => law)).prod (restHaar e)) := by
    unfold boundaryHaar restHaar
    exact split_constant_pi law e
  have hu := measurePreserving_piUnique (fun _ : {j : SpatialEdge // j = e} => law)
  have hr : MeasurePreserving
      ((MeasurableEquiv.piUnique (fun _ : {j : SpatialEdge // j = e} => SU2)).prodCongr
        (MeasurableEquiv.refl (RestField e)))
      ((Measure.pi (fun _ : {j : SpatialEdge // j = e} => law)).prod (restHaar e))
      (law.prod (restHaar e)) := hu.prod (MeasurePreserving.id (restHaar e))
  unfold coordinateSplit
  exact hr.comp hs

def split : PeriodicAugmentedBridge.Space ≃ᵐ Rest e × SU2 :=
  (((coordinateSplit e).prodCongr (MeasurableEquiv.refl (Gauge × Gauge))).trans
    MeasurableEquiv.prodAssoc).trans MeasurableEquiv.prodComm

theorem split_preserving : MeasurePreserving (split e) PeriodicAugmentedBridge.reference
    ((restReference e).prod law) := by
  have h1 := (coordinateSplit_preserving e).prod (MeasurePreserving.id (gaugeHaar.prod gaugeHaar))
  have h2 := measurePreserving_prodAssoc law (restHaar e) (gaugeHaar.prod gaugeHaar)
  have h3 := Measure.measurePreserving_swap (μ := law) (ν := (restHaar e).prod (gaugeHaar.prod gaugeHaar))
  unfold split PeriodicAugmentedBridge.reference restReference
  exact h3.comp (h2.comp h1)

theorem coordinateSplit_apply (V : State) : coordinateSplit e V =
    (V e,fun j : {j : SpatialEdge // j ≠ e} => V j) := rfl

theorem split_apply (q : PeriodicAugmentedBridge.Space) :
    split e q = ((fun j : {j : SpatialEdge // j ≠ e} => q.1 j,q.2),q.1 e) := rfl

def baseField (r : Rest e) : State := (coordinateSplit e).symm (1,r.1)

theorem assemble (r : Rest e) (A : SU2) :
    (split e).symm (r,A) = (Function.update (baseField e r) e A,r.2) := by
  apply (split e).injective
  rw [(split e).apply_symm_apply, split_apply]
  dsimp only
  have hb := (coordinateSplit e).apply_symm_apply (1,r.1)
  rw [coordinateSplit_apply] at hb
  have hbr := congrArg Prod.snd hb
  apply Prod.ext
  · apply Prod.ext
    · funext j
      change r.1 j = Function.update (baseField e r) e A j
      rw [Function.update_of_ne j.property]
      exact (congrFun hbr j).symm
    · rfl
  · change A = Function.update (baseField e r) e A e
    exact (Function.update_self e A (baseField e r)).symm

attribute [local irreducible] coordinateSplit split baseField PeriodicAugmentedBridge.density

def exponent (β : ℝ) (U W : State) (r : Rest e) (A : SU2) : ℝ :=
  Real.log (PeriodicAugmentedBridge.density β U W ((split e).symm (r,A)))

theorem exponent_measurable (β : ℝ) (U W : State) :
    Measurable (Function.uncurry (exponent e β U W)) :=
  ((PeriodicAugmentedBridge.density_measurable β U W).comp (split e).symm.measurable).log

theorem exp_exponent (β : ℝ) (U W : State) (r : Rest e) (A : SU2) :
    Real.exp (exponent e β U W r A) =
      PeriodicAugmentedBridge.density β U W ((split e).symm (r,A)) :=
  Real.exp_log (PeriodicAugmentedBridge.density_pos β U W _)

theorem exp_fiber_integrable (β : ℝ) (U W : State) (r : Rest e) :
    Integrable (fun A => Real.exp (exponent e β U W r A)) law := by
  have hm : Measurable (fun A => Real.exp (exponent e β U W r A)) :=
    ((exponent_measurable e β U W).comp (measurable_const.prodMk measurable_id)).exp
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (768*|β|)^2)
  filter_upwards with A
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), exp_exponent]
  exact PeriodicAugmentedBridge.density_upper β U W _

theorem exp_joint_integrable (β : ℝ) (U W : State) :
    Integrable (fun z : Rest e × SU2 => Real.exp (exponent e β U W z.1 z.2))
      ((restReference e).prod law) := by
  apply Integrable.of_bound (exponent_measurable e β U W).exp.aestronglyMeasurable
    (Real.exp (768*|β|)^2)
  filter_upwards with z
  dsimp only [Function.uncurry_def]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), exp_exponent]
  exact PeriodicAugmentedBridge.density_upper β U W _

def joint (β : ℝ) (U W : State) : Measure (Rest e × SU2) :=
  ExponentialJointDisintegration.joint (restReference e) law (exponent e β U W)

def marginal (β : ℝ) (U W : State) : Measure (Rest e) :=
  ExponentialJointDisintegration.boundary (restReference e) law (exponent e β U W)

def conditionalKernel (β : ℝ) (U W : State) : Kernel (Rest e) SU2 :=
  MeasurableExponentialKernel.kernel law (exponent e β U W)

theorem kernel_markov (β : ℝ) (U W : State) : IsMarkovKernel (conditionalKernel e β U W) :=
  MeasurableExponentialKernel.kernel_markov law _ (exponent_measurable e β U W)
    (exp_fiber_integrable e β U W)

theorem joint_probability (β : ℝ) (U W : State) : IsProbabilityMeasure (joint e β U W) :=
  ExponentialJointDisintegration.joint_probability (restReference e) law _
    (exponent_measurable e β U W) (exp_fiber_integrable e β U W) (exp_joint_integrable e β U W)

theorem factorization (β : ℝ) (U W : State) :
    joint e β U W = (marginal e β U W) ⊗ₘ (conditionalKernel e β U W) :=
  ExponentialJointDisintegration.factorization (restReference e) law _
    (exponent_measurable e β U W) (exp_fiber_integrable e β U W)

theorem conditional_kernel (β : ℝ) (U W : State) :
    (joint e β U W).IsCondKernel (conditionalKernel e β U W) :=
  ExponentialJointDisintegration.conditional_kernel (restReference e) law _
    (exponent_measurable e β U W) (exp_fiber_integrable e β U W) (exp_joint_integrable e β U W)

theorem kernel_eq_linkLaw (β : ℝ) (U W : State) (r : Rest e) :
    conditionalKernel e β U W r = linkLaw β U (baseField e r) W r.2.1 r.2.2 e := by
  rw [conditionalKernel, MeasurableExponentialKernel.kernel_apply law _ (exponent_measurable e β U W)]
  unfold linkLaw MeasurableExponentialKernel.density MeasurableExponentialKernel.partition
  congr 1
  funext A
  simp_rw [exp_exponent, assemble]
  rfl

attribute [local irreducible] exponent conditionalKernel joint marginal

theorem total_partition (β : ℝ) (U W : State) :
    ExponentialJointDisintegration.totalPartition (restReference e) law (exponent e β U W) =
      PeriodicGroundBridge.normalizer β U W := by
  unfold ExponentialJointDisintegration.totalPartition
  simp_rw [exp_exponent]
  have h := (split_preserving e).integral_comp'
    (fun z => PeriodicAugmentedBridge.density β U W ((split e).symm z))
  simp only [MeasurableEquiv.symm_apply_apply] at h
  exact h.symm.trans (PeriodicAugmentedBridge.total_integral β U W)

theorem augmented_withDensity (β : ℝ) (U W : State) :
    PeriodicAugmentedBridge.law β U W = PeriodicAugmentedBridge.reference.withDensity
      (fun q => ENNReal.ofReal (PeriodicAugmentedBridge.density β U W q /
        PeriodicGroundBridge.normalizer β U W)) := by
  unfold PeriodicAugmentedBridge.law SignedDensityProbabilitySampling.sampler
  rw [PeriodicAugmentedBridge.mass_identity]
  unfold SignedAbsoluteIntegration.absoluteDensity
  simp_rw [abs_of_pos (PeriodicAugmentedBridge.density_pos β U W _)]
  rw [← withDensity_smul _ (PeriodicAugmentedBridge.density_measurable β U W).ennreal_ofReal]
  apply congrArg (fun f => PeriodicAugmentedBridge.reference.withDensity f)
  funext q
  rw [ENNReal.ofReal_div_of_pos (PeriodicGroundBridge.normalizer_pos β U W), div_eq_mul_inv]
  exact mul_comm _ _

/-- The generic exponential joint law IS the actual augmented law in one-link coordinates. -/
theorem split_augmented_law (β : ℝ) (U W : State) :
    (PeriodicAugmentedBridge.law β U W).map (split e) = joint e β U W := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (split e).measurable hs, augmented_withDensity,
    withDensity_apply _ ((split e).measurable hs)]
  unfold joint ExponentialJointDisintegration.joint
  rw [withDensity_apply _ hs, total_partition]
  have hm : Measurable (fun z : Rest e × SU2 => ENNReal.ofReal
      (Real.exp (exponent e β U W z.1 z.2) / PeriodicGroundBridge.normalizer β U W)) :=
    (exponent_measurable e β U W).exp.div_const _ |>.ennreal_ofReal
  have he := setLIntegral_map (μ := PeriodicAugmentedBridge.reference) hs hm (split e).measurable
  rw [(split_preserving e).map_eq] at he
  simpa only [exp_exponent, Prod.eta, MeasurableEquiv.symm_apply_apply] using he.symm

theorem split_augmented_conditional (β : ℝ) (U W : State) :
    ((PeriodicAugmentedBridge.law β U W).map (split e)).IsCondKernel
      (conditionalKernel e β U W) := by
  rw [split_augmented_law]
  exact conditional_kernel e β U W

theorem marginal_probability (β : ℝ) (U W : State) : IsProbabilityMeasure (marginal e β U W) := by
  unfold marginal
  exact ExponentialJointDisintegration.boundary_probability (restReference e) law _
    (exponent_measurable e β U W) (exp_fiber_integrable e β U W) (exp_joint_integrable e β U W)

theorem actual_rest_marginal (β : ℝ) (U W : State) :
    ((PeriodicAugmentedBridge.law β U W).map (split e)).fst = marginal e β U W := by
  rw [split_augmented_law]
  unfold joint marginal
  exact ExponentialJointDisintegration.boundary_marginal (restReference e) law _
    (exponent_measurable e β U W) (exp_fiber_integrable e β U W) (exp_joint_integrable e β U W)

theorem actual_factorization (β : ℝ) (U W : State) :
    (PeriodicAugmentedBridge.law β U W).map (split e) =
      (marginal e β U W) ⊗ₘ (conditionalKernel e β U W) := by
  rw [split_augmented_law]
  exact factorization e β U W

/-- The already proved local lower bound now belongs to a genuine conditional kernel
of the actual augmented law, with its correctly reweighted marginal. -/
theorem conditional_variance_lower (β : ℝ) (hβ : 0 ≤ β) (U W : State) (r : Rest e) (C : SU2) :
    6/(49*(1+6*β)^2) ≤
      (∫ A, halfTrace (C*A)^2 ∂conditionalKernel e β U W r) -
      (∫ A, halfTrace (C*A) ∂conditionalKernel e β U W r)^2 := by
  rw [kernel_eq_linkLaw]
  exact linkLaw_variance_lower β hβ U (baseField e r) W r.2.1 r.2.2 e C

theorem actual_rectangles (β : ℝ) (U W : State)
    (s : Set (Rest e)) (t : Set SU2) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ((PeriodicAugmentedBridge.law β U W).map (split e)) (s ×ˢ t) =
      ∫⁻ r in s, conditionalKernel e β U W r t ∂marginal e β U W := by
  rw [split_augmented_law]
  unfold joint conditionalKernel marginal
  exact ExponentialJointDisintegration.conditional_rectangles (restReference e) law _
    (exponent_measurable e β U W) (exp_fiber_integrable e β U W) (exp_joint_integrable e β U W)
    s t hs ht

end OperatorDerivativeRewrite.Foundation.PeriodicLinkDisintegration
