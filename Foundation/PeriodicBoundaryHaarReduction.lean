import Foundation.PeriodicVacuumNormalizationObstruction
import Foundation.SU2TiltEnergyResponse
/-! Exact rooted-tree/chord Haar reduction of the actual64-vertex periodic
Wilson boundary. All192 links split into63 original tree links and129 reduced
Haar chords, with the common SU(2) root conjugation retained. Actual kernel,
ground law, unbounded native domains and transition formulas are transported.
The field-dependent gauge-fixed section is measurable but NOT full-Haar-
preserving. No stationary spectral or continuum mass-gap result is asserted. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.PeriodicBoundaryHaarReduction
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge PeriodicSlabGround
open PeriodicGaugeSaturatedGround (root depth parent axis depth_zero parent_shift parent_depth rel_count RelFieldIndex)
attribute [local irreducible] kernel boundaryHaar gaugeAction

def treeEdge (v : SpatialVertex) : SpatialEdge := (parent v,axis v)
def isTree (e : SpatialEdge) : Prop :=
  shift e.1 e.2≠root ∧ parent (shift e.1 e.2)=e.1 ∧ axis (shift e.1 e.2)=e.2
instance tree_decidable : DecidablePred isTree := by unfold isTree; infer_instance

abbrev TreeIndex := {e : SpatialEdge // isTree e}
abbrev ChordIndex := {e : SpatialEdge // ¬isTree e}
abbrev TreeState := TreeIndex → SU2
abbrev Chords := ChordIndex → SU2

theorem treeEdge_mem (v : SpatialVertex) (hv : v≠root) : isTree (treeEdge v) := by
  unfold treeEdge isTree
  rw [parent_shift v hv]
  exact ⟨hv,rfl,rfl⟩

def treeEquiv : RelFieldIndex ≃ TreeIndex where
  toFun v := ⟨treeEdge v.val,treeEdge_mem v.val v.property⟩
  invFun e := ⟨shift e.val.1 e.val.2,e.property.1⟩
  left_inv v := Subtype.ext (parent_shift v.val v.property)
  right_inv e := Subtype.ext (Prod.ext e.property.2.1 e.property.2.2)

theorem tree_count : Fintype.card TreeIndex=63 := by
  rw [← Fintype.card_congr treeEquiv,rel_count]

theorem chord_count : Fintype.card ChordIndex=129 := by
  rw [Fintype.card_subtype_compl isTree,tree_count,edge_count]

abbrev ChordVelocities := ChordIndex → SU2GaussianConeCoordinates.Triple

theorem chord_finrank : Module.finrank ℝ ChordVelocities=387 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fin_fun,Finset.sum_const,Finset.card_univ,chord_count]
  norm_num

def rootedGauge (U : State) (v : SpatialVertex) : SU2 :=
  if hv : v=root then 1 else rootedGauge U (parent v)*U (treeEdge v)
termination_by depth v
decreasing_by have h := parent_depth v hv; omega

theorem rooted_root (U : State) : rootedGauge U root=1 := by rw [rootedGauge,dif_pos rfl]

theorem rooted_parent (U : State) (v : SpatialVertex) (hv : v≠root) :
    rootedGauge U v=rootedGauge U (parent v)*U (treeEdge v) := by rw [rootedGauge,dif_neg hv]

theorem rooted_measurable (v : SpatialVertex) : Measurable (fun U : State => rootedGauge U v) := by
  generalize hn : depth v=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v=root
    · subst v
      simpa only [rooted_root] using (measurable_const : Measurable (fun _ : State => (1 : SU2)))
    · have hd : depth (parent v)<n := by have h := parent_depth v hv; omega
      have hm := ih (depth (parent v)) hd (parent v) rfl
      have he : (fun U : State => rootedGauge U v)=
          (fun U : State => rootedGauge U (parent v)*U (treeEdge v)) := funext (fun U => rooted_parent U v hv)
      rw [he]
      exact hm.mul (measurable_pi_apply (treeEdge v))

def reduced (U : State) (e : ChordIndex) : SU2 := gaugeAction (rootedGauge U) U e.val
def axialState (c : Chords) (e : SpatialEdge) : SU2 := if he : isTree e then 1 else c ⟨e,he⟩

theorem tree_cancel (U : State) (v : SpatialVertex) (hv : v≠root) :
    gaugeAction (rootedGauge U) U (treeEdge v)=1 := by
  unfold gaugeAction treeEdge
  rw [parent_shift v hv,rooted_parent U v hv]
  unfold treeEdge
  group

theorem reconstruction (U : State) : gaugeAction (rootedGauge U) U=axialState (reduced U) := by
  funext e
  unfold axialState
  split_ifs with he
  · have hh : treeEdge (shift e.1 e.2)=e := Prod.ext he.2.1 he.2.2
    rw [← hh]
    exact tree_cancel U _ he.1
  · rfl

theorem axial_tree (c : Chords) (v : SpatialVertex) (hv : v≠root) : axialState c (treeEdge v)=1 := by
  simp only [axialState,dif_pos (treeEdge_mem v hv)]

theorem rooted_axial (c : Chords) (v : SpatialVertex) : rootedGauge (axialState c) v=1 := by
  generalize hn : depth v=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v=root
    · subst v; exact rooted_root _
    · have hd : depth (parent v)<n := by have h := parent_depth v hv; omega
      rw [rooted_parent _ v hv,ih _ hd _ rfl,axial_tree c v hv,one_mul]

theorem reduced_axial (c : Chords) : reduced (axialState c)=c := by
  funext e
  unfold reduced gaugeAction
  rw [rooted_axial,rooted_axial]
  simp only [one_mul,inv_one,mul_one,axialState,dif_neg e.property]

theorem reduced_measurable : Measurable reduced := by
  apply measurable_pi_iff.mpr
  intro e
  unfold reduced gaugeAction
  convert ((rooted_measurable e.val.1).mul (measurable_pi_apply e.val)).mul
    (rooted_measurable (shift e.val.1 e.val.2)).inv
    using 1

theorem axial_measurable : Measurable axialState := by
  apply measurable_pi_iff.mpr
  intro e
  unfold axialState
  split_ifs with he
  · exact measurable_const
  · exact measurable_pi_apply (⟨e,he⟩ : ChordIndex)

def treeHaar : Measure TreeState := Measure.pi (fun _ => law)
def chordHaar : Measure Chords := Measure.pi (fun _ => law)
instance tree_probability : IsProbabilityMeasure treeHaar := by unfold treeHaar; infer_instance
instance chord_probability : IsProbabilityMeasure chordHaar := by unfold chordHaar; infer_instance

def split : State ≃ᵐ (TreeState × Chords) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : SpatialEdge => SU2) isTree

theorem split_preserving : MeasurePreserving split boundaryHaar (treeHaar.prod chordHaar) := by
  simpa only [split,boundaryHaar,treeHaar,chordHaar] using
    measurePreserving_piEquivPiSubtypeProd (fun _ : SpatialEdge => law) isTree

def rawState (t : TreeState) (c : Chords) : State := split.symm (t,c)

theorem rawState_tree (t : TreeState) (c : Chords) (e : SpatialEdge) (he : isTree e) :
    rawState t c e=t ⟨e,he⟩ := by
  simp [rawState,split,MeasurableEquiv.piEquivPiSubtypeProd,he]

theorem rawState_chord (t : TreeState) (c : Chords) (e : ChordIndex) : rawState t c e.val=c e := by
  simp [rawState,split,MeasurableEquiv.piEquivPiSubtypeProd,e.property]

theorem rooted_tree_only (t : TreeState) (c c' : Chords) (v : SpatialVertex) :
    rootedGauge (rawState t c) v=rootedGauge (rawState t c') v := by
  generalize hn : depth v=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v=root
    · subst v; rw [rooted_root,rooted_root]
    · have hd : depth (parent v)<n := by have h := parent_depth v hv; omega
      rw [rooted_parent _ v hv,rooted_parent _ v hv,ih _ hd _ rfl,
        rawState_tree t c _ (treeEdge_mem v hv),rawState_tree t c' _ (treeEdge_mem v hv)]

private def frame (t : TreeState) : Gauge := rootedGauge (rawState t 1)

theorem conditional_formula (t : TreeState) (c : Chords) (e : ChordIndex) :
    reduced (rawState t c) e=frame t e.val.1*c e*(frame t (shift e.val.1 e.val.2))⁻¹ := by
  unfold reduced gaugeAction frame
  rw [rooted_tree_only t c 1,rooted_tree_only t c 1,rawState_chord]

theorem conditional_preserving (t : TreeState) :
    MeasurePreserving (fun c : Chords => reduced (rawState t c)) chordHaar chordHaar := by
  have he : (fun c : Chords => reduced (rawState t c))=
      (fun c : Chords => fun e => frame t e.val.1*c e*(frame t (shift e.val.1 e.val.2))⁻¹) := by
    funext c e
    exact conditional_formula t c e
  rw [he]
  unfold chordHaar
  apply measurePreserving_pi (fun _ : ChordIndex => law) (fun _ : ChordIndex => law)
    (f := fun e x => frame t e.val.1*x*(frame t (shift e.val.1 e.val.2))⁻¹)
  intro e
  exact (measurePreserving_mul_right law ((frame t (shift e.val.1 e.val.2))⁻¹)).comp
    (measurePreserving_mul_left law (frame t e.val.1))

theorem joint_preserving :
    MeasurePreserving (fun U : State => ((split U).1,reduced U)) boundaryHaar (treeHaar.prod chordHaar) := by
  have hm : Measurable (Function.uncurry (fun t c => reduced (rawState t c))) :=
    reduced_measurable.comp split.symm.measurable
  have h := (MeasurePreserving.id treeHaar).skew_product hm
    (ae_of_all treeHaar (fun t => (conditional_preserving t).map_eq))
  convert h.comp split_preserving using 1
  funext U
  change ((split U).1,reduced U)=((split U).1,reduced (split.symm (split U)))
  rw [MeasurableEquiv.symm_apply_apply]

theorem reduced_preserving : MeasurePreserving reduced boundaryHaar chordHaar :=
  (measurePreserving_snd (μ := treeHaar) (ν := chordHaar)).comp joint_preserving

theorem integral_reduced (f : Chords → ℝ) (hf : Measurable f) :
    (∫ U,f (reduced U) ∂boundaryHaar)=∫ q,f q ∂chordHaar := by
  have h := integral_map reduced_preserving.measurable.aemeasurable (μ := boundaryHaar) (f := f)
  rw [reduced_preserving.map_eq] at h
  exact (h hf.aestronglyMeasurable).symm

theorem kernel_reduced (β : ℝ) (U V : State) :
    kernel β U V=kernel β (axialState (reduced U)) (axialState (reduced V)) := by
  have h1 := kernel_left_invariant β (rootedGauge U) U V
  rw [reconstruction] at h1
  have h2 := kernel_right_invariant β (rootedGauge V) (axialState (reduced U)) V
  rw [reconstruction] at h2
  exact (h2.trans h1).symm

variable {β : ℝ} (g : GroundData β)

theorem function_reduced (U : State) : g.function U=g.function (axialState (reduced U)) := by
  have h := g.invariant (rootedGauge U) U
  rw [reconstruction] at h
  exact h.symm

theorem normalizer_chords : g.normalizer=∫ q,g.function (axialState q)^2 ∂chordHaar := by
  calc
    _ = ∫ U,g.function (axialState (reduced U))^2 ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with U
      rw [function_reduced g U]
    _ = _ := integral_reduced _ ((g.measurable.comp axial_measurable).pow_const 2)

theorem stationary_integrable_iff (f : State → ℝ) :
    Integrable f g.stationary ↔ Integrable (fun U => g.function U^2*f U) boundaryHaar := by
  change Integrable f ((ENNReal.ofReal (SignedDensityProbabilitySampling.mass boundaryHaar
    (fun U => g.function U^2)))⁻¹ • SignedAbsoluteIntegration.absoluteDensity boundaryHaar
      (fun U => g.function U^2)) ↔ _
  have hm : SignedDensityProbabilitySampling.mass boundaryHaar (fun U => g.function U^2)=g.normalizer := by
    unfold SignedDensityProbabilitySampling.mass GroundData.normalizer
    simp only [abs_pow,sq_abs]
  rw [hm,integrable_inv_smul_measure
    (ne_of_gt (ENNReal.ofReal_pos.mpr g.normalizer_pos)) ENNReal.ofReal_ne_top]
  unfold SignedAbsoluteIntegration.absoluteDensity
  simp only [abs_pow,sq_abs]
  have h := integrable_withDensity_iff_integrable_smul₀'
    (g.measurable.pow_const 2).ennreal_ofReal.aemeasurable
    (ae_of_all boundaryHaar (fun _ => ENNReal.ofReal_lt_top)) (g := f)
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul] using h

theorem native_integrable_iff (f : Chords → ℝ) (hf : Measurable f) :
    Integrable (fun U => f (reduced U)) g.stationary ↔
      Integrable (fun q => g.function (axialState q)^2*f q) chordHaar := by
  rw [stationary_integrable_iff]
  have h := reduced_preserving.integrable_comp
    (((g.measurable.comp axial_measurable).pow_const 2).mul hf).aestronglyMeasurable
  have he : (fun U => g.function U^2*f (reduced U))=
      (fun U => g.function (axialState (reduced U))^2*f (reduced U)) := by
    funext U
    rw [function_reduced g U]
  rw [he]
  exact h

theorem native_memLp_iff (f : Chords → ℝ) (hf : Measurable f) :
    MemLp (fun U => f (reduced U)) 2 g.stationary ↔
      Integrable (fun q => g.function (axialState q)^2*f q^2) chordHaar := by
  have h := memLp_two_iff_integrable_sq (μ := g.stationary)
    (f := fun U : State => f (reduced U)) (hf.comp reduced_measurable).aestronglyMeasurable
  exact h.trans (native_integrable_iff g (fun q => f q^2) (hf.pow_const 2))

theorem native_integral_chords (f : Chords → ℝ) (hf : Measurable f) :
    (∫ U,f (reduced U) ∂g.stationary)=
      (∫ q,g.function (axialState q)^2*f q ∂chordHaar)/g.normalizer := by
  rw [g.stationary_integral]
  congr 1
  calc
    _ = ∫ U,g.function (axialState (reduced U))^2*f (reduced U) ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with U
      rw [function_reduced g U]
    _ = _ := integral_reduced _ (((g.measurable.comp axial_measurable).pow_const 2).mul hf)

theorem eigen_chords (q : Chords) :
    (∫ r,kernel β (axialState q) (axialState r)*g.function (axialState r) ∂chordHaar)=
      g.value*g.function (axialState q) := by
  have hm : Measurable (fun r : Chords => kernel β (axialState q) (axialState r)*g.function (axialState r)) :=
    ((kernel_joint_measurable β).comp (measurable_const.prodMk axial_measurable)).mul
      (g.measurable.comp axial_measurable)
  rw [← integral_reduced _ hm]
  calc
    _ = ∫ V,kernel β (axialState q) V*g.function V ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with V
      have hk := kernel_right_invariant β (rootedGauge V) (axialState q) V
      rw [reconstruction] at hk
      rw [hk,← function_reduced g V]
    _ = _ := g.eigen (axialState q)

theorem transition_chords (f : Chords → ℝ) (hf : Measurable f) (U : State) :
    (∫ V,f (reduced V) ∂g.transition U)=
      (∫ r,kernel β (axialState (reduced U)) (axialState r)*(g.function (axialState r)*f r) ∂chordHaar)/
        (g.value*g.function (axialState (reduced U))) := by
  rw [g.transition_integral,function_reduced g U]
  congr 1
  calc
    _ = ∫ V,kernel β (axialState (reduced U)) (axialState (reduced V))*
        (g.function (axialState (reduced V))*f (reduced V)) ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with V
      rw [kernel_reduced β U V,function_reduced g V]
    _ = _ := integral_reduced _ (((kernel_joint_measurable β).comp
      (measurable_const.prodMk axial_measurable)).mul ((g.measurable.comp axial_measurable).mul hf))

def conjugate (c : SU2) (q : Chords) : Chords := fun e => c*q e*c⁻¹

theorem rooted_gauge_covariant (a : Gauge) (U : State) (v : SpatialVertex) :
    rootedGauge (gaugeAction a U) v=a root*rootedGauge U v*(a v)⁻¹ := by
  generalize hn : depth v=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v=root
    · subst v
      rw [rooted_root,rooted_root]
      group
    · have hd : depth (parent v)<n := by have h := parent_depth v hv; omega
      rw [rooted_parent _ v hv,rooted_parent U v hv,ih _ hd _ rfl]
      unfold gaugeAction treeEdge
      rw [parent_shift v hv]
      group

theorem reduced_covariant (a : Gauge) (U : State) :
    reduced (gaugeAction a U)=conjugate (a root) (reduced U) := by
  funext e
  unfold conjugate reduced
  rw [show gaugeAction (rootedGauge (gaugeAction a U)) (gaugeAction a U) e.val=
    rootedGauge (gaugeAction a U) e.val.1*(gaugeAction a U) e.val*
      (rootedGauge (gaugeAction a U) (shift e.val.1 e.val.2))⁻¹ by unfold gaugeAction; rfl]
  simp_rw [rooted_gauge_covariant]
  unfold gaugeAction
  group

theorem axial_conjugate (c : SU2) (q : Chords) :
    axialState (conjugate c q)=gaugeAction (fun _ => c) (axialState q) := by
  funext e
  unfold axialState gaugeAction conjugate
  split_ifs with he
  · simp only [dif_pos he]
    group
  · simp only [dif_neg he]

theorem kernel_conjugate_left (β : ℝ) (c : SU2) (q r : Chords) :
    kernel β (axialState (conjugate c q)) (axialState r)=kernel β (axialState q) (axialState r) := by
  rw [axial_conjugate]
  exact kernel_left_invariant β (fun _ => c) _ _

theorem kernel_conjugate_right (β : ℝ) (c : SU2) (q r : Chords) :
    kernel β (axialState q) (axialState (conjugate c r))=kernel β (axialState q) (axialState r) := by
  rw [axial_conjugate]
  exact kernel_right_invariant β (fun _ => c) _ _

theorem function_conjugate (c : SU2) (q : Chords) :
    g.function (axialState (conjugate c q))=g.function (axialState q) := by
  rw [axial_conjugate]
  exact g.invariant (fun _ => c) _

theorem gauge_invariant_lift (f : Chords → ℝ) (hf : ∀ c q,f (conjugate c q)=f q)
    (a : Gauge) (U : State) : f (reduced (gaugeAction a U))=f (reduced U) := by
  rw [reduced_covariant,hf]

theorem gaugeFix_measurable : Measurable (fun U : State => gaugeAction (rootedGauge U) U) := by
  have he : (fun U : State => gaugeAction (rootedGauge U) U)=axialState ∘ reduced := funext reconstruction
  rw [he]
  exact axial_measurable.comp reduced_measurable

theorem haar_link_trace_zero (e : SpatialEdge) : (∫ U : State,halfTrace (U e) ∂boundaryHaar)=0 := by
  have hp : MeasurePreserving (fun U : State => U e) boundaryHaar law := by
    unfold boundaryHaar
    exact measurePreserving_eval (fun _ : SpatialEdge => law) e
  have h := integral_map (μ := boundaryHaar) hp.measurable.aemeasurable halfTrace_measurable.aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h.symm.trans (SU2TiltEnergyResponse.moment_values law).1

/-- The actual section map is measurable but cannot preserve full boundary
Haar: it pins every tree link. Only the proved conditional chord law is Haar. -/
theorem gaugeFix_not_preserving :
    ¬ MeasurePreserving (fun U : State => gaugeAction (rootedGauge U) U) boundaryHaar boundaryHaar := by
  intro hp
  let v : SpatialVertex := shift root 0
  have hv : v≠root := by decide
  have hm : Measurable (fun U : State => halfTrace (U (treeEdge v))) :=
    halfTrace_measurable.comp (measurable_pi_apply (treeEdge v))
  have h := integral_map (μ := boundaryHaar) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at h
  change (∫ U : State,halfTrace (U (treeEdge v)) ∂boundaryHaar)=
    (∫ U : State,halfTrace (gaugeAction (rootedGauge U) U (treeEdge v)) ∂boundaryHaar) at h
  rw [haar_link_trace_zero] at h
  simp_rw [tree_cancel _ v hv,FourCubeWilsonCubic.trace_one] at h
  norm_num at h

end OperatorDerivativeRewrite.Foundation.PeriodicBoundaryHaarReduction
