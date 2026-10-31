import Foundation.FourCubeStandardResponse
import Foundation.ExponentialJointDisintegration
/-! Exact spatial conditioning of the finite nearest-neighbor four-dimensional box.
Use only valid edges, all admitted plaquettes, and the actual32-link core. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeSpatialConditioning
open QuaternionSU2Representation FourCubeDirichletBox
open OneSidedBlockRank FourCubeHaarParity
open FourCubePinnedCoercivity (defect defect_nonneg)
attribute [local irreducible] faces OneSidedBlockIncidence.edges

abbrev Edge := {e : BoxEdge // (e.1 e.2).val<3}
abbrev Face := {p : BoxFace // p∈faces}
abbrev Field := Edge → SU2

def core (i : Interior) : Edge := ⟨embed i.val,by
  rw [(FourCubeCoreIncident.core_embed i).2]
  decide⟩

theorem core_injective : Function.Injective core := by
  intro i j h
  have he := congrArg (fun e : Edge => label e.val) h
  change label (embed i.val)=label (embed j.val) at he
  rw [label_interior,label_interior] at he
  exact Sum.inl.inj (Option.some.inj he)

abbrev Exterior := {e : Edge // e∉Set.range core}
noncomputable instance exterior_fintype : Fintype Exterior := Fintype.ofFinite Exterior
abbrev ExteriorState := Exterior → SU2

def indexEquiv : Exterior ⊕ Interior ≃ Edge := by
  classical
  exact (Equiv.sumComm _ _).trans
    ((Equiv.sumCongr (Equiv.ofInjective core core_injective) (Equiv.refl Exterior)).trans
      (Equiv.Set.sumCompl (Set.range core)))

theorem index_interior (i : Interior) : indexEquiv (.inr i)=core i := rfl
theorem index_exterior (e : Exterior) : indexEquiv (.inl e)=e.val := rfl

def join : (ExteriorState × InteriorState) ≃ᵐ Field :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Exterior ⊕ Interior => SU2)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Edge => SU2) indexEquiv)

theorem join_apply (A : ExteriorState) (s : InteriorState) (j : Exterior ⊕ Interior) :
    join (A,s) (indexEquiv j)=Sum.elim A s j := by
  change (MeasurableEquiv.piCongrLeft (fun _ : Edge => SU2) indexEquiv) _ (indexEquiv j) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases j <;> rfl

theorem join_interior (A : ExteriorState) (s : InteriorState) (i : Interior) :
    join (A,s) (core i)=s i := by
  rw [← index_interior]
  exact join_apply A s (.inr i)

theorem join_exterior (A : ExteriorState) (s : InteriorState) (e : Exterior) :
    join (A,s) e.val=A e := by
  rw [← index_exterior]
  exact join_apply A s (.inl e)

def exteriorHaar : Measure ExteriorState :=
  Measure.pi (fun _ => QuaternionSU2Representation.law)
def fieldHaar : Measure Field := Measure.pi (fun _ => QuaternionSU2Representation.law)
instance exterior_probability : IsProbabilityMeasure exteriorHaar := by
  unfold exteriorHaar
  infer_instance
instance field_probability : IsProbabilityMeasure fieldHaar := by
  unfold fieldHaar
  infer_instance

theorem join_preserving : MeasurePreserving join (exteriorHaar.prod interiorHaar) fieldHaar := by
  exact (measurePreserving_piCongrLeft (fun _ : Edge => QuaternionSU2Representation.law) indexEquiv).comp
    (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Exterior ⊕ Interior => QuaternionSU2Representation.law))

private theorem face_edge_valid (p : Face) (k : Fin 4) :
    ((faceEdges p.val k).1 (faceEdges p.val k).2).val<3 := by
  have hp := p.property
  simp only [faces,Finset.mem_filter,Finset.mem_univ,true_and] at hp
  have hi : (p.val.1 p.val.2.1).val < 3 := hp.2.1
  have hj : (p.val.1 p.val.2.2).val < 3 := hp.2.2
  fin_cases k
  · simpa [faceEdges] using hi
  · simpa [faceEdges,step,hp.1.ne.symm] using hj
  · simpa [faceEdges,step,hp.1.ne] using hi
  · simpa [faceEdges] using hj

def faceEdge (p : Face) (k : Fin 4) : Edge := ⟨faceEdges p.val k,face_edge_valid p k⟩

def word (F : Field) (p : Face) : SU2 :=
  F (faceEdge p 0)*F (faceEdge p 1)*(F (faceEdge p 2))⁻¹*(F (faceEdge p 3))⁻¹

def action (F : Field) : ℝ := ∑ p : Face,defect (word F p)

theorem action_bounds (F : Field) : 0≤action F ∧ action F≤1728 := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ => defect_nonneg _)
  · calc
      action F ≤ ∑ _ : Face,(2:ℝ) := by
        apply Finset.sum_le_sum
        intro p _
        have h := (abs_le.mp (halfTrace_bound (word F p))).1
        unfold defect
        linarith
      _ = 1728 := by simp [face_count]; norm_num

theorem action_measurable : Measurable action := by
  unfold action
  apply Finset.measurable_sum
  intro p _
  exact measurable_const.sub (halfTrace_measurable.comp
    ((((measurable_pi_apply (faceEdge p 0)).mul (measurable_pi_apply (faceEdge p 1))).mul
      (measurable_pi_apply (faceEdge p 2)).inv).mul (measurable_pi_apply (faceEdge p 3)).inv))

/-- The exponent retains every spatial plaquette, including exterior-only ones. -/
def exponent (β : ℝ) (A : ExteriorState) (s : InteriorState) : ℝ :=
  -β*action (join (A,s))

theorem exponent_measurable (β : ℝ) : Measurable (Function.uncurry (exponent β)) :=
  measurable_const.mul (action_measurable.comp join.measurable)

private theorem bounded_weight_integrable {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → Field) (hf : Measurable f) (β : ℝ) :
    Integrable (fun x => Real.exp (-β*action (f x))) ν := by
  apply Integrable.of_bound
    ((measurable_const.mul (action_measurable.comp hf)).exp.aestronglyMeasurable)
    (Real.exp (1728*|β|))
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    -β*action (f x) ≤ |β| *action (f x) :=
      mul_le_mul_of_nonneg_right (neg_le_abs β) (action_bounds _).1
    _ ≤ |β| *1728 := mul_le_mul_of_nonneg_left (action_bounds _).2 (abs_nonneg β)
    _ = 1728*|β| := mul_comm _ _

theorem section_integrable (β : ℝ) (A : ExteriorState) :
    Integrable (fun s => Real.exp (exponent β A s)) interiorHaar :=
  bounded_weight_integrable interiorHaar (fun s => join (A,s))
    (join.measurable.comp (measurable_const.prodMk measurable_id)) β

theorem joint_integrable (β : ℝ) : Integrable
    (fun z : ExteriorState × InteriorState => Real.exp (exponent β z.1 z.2))
    (exteriorHaar.prod interiorHaar) :=
  bounded_weight_integrable _ join join.measurable β

def partition (β : ℝ) : ℝ := ∫ F, Real.exp (-β*action F) ∂fieldHaar

def fullLaw (β : ℝ) : Measure Field := fieldHaar.withDensity
  (fun F => ENNReal.ofReal (Real.exp (-β*action F)/partition β))

def jointLaw (β : ℝ) : Measure (ExteriorState × InteriorState) :=
  ExponentialJointDisintegration.joint exteriorHaar interiorHaar (exponent β)

def exteriorLaw (β : ℝ) : Measure ExteriorState :=
  ExponentialJointDisintegration.boundary exteriorHaar interiorHaar (exponent β)

def conditional (β : ℝ) : Kernel ExteriorState InteriorState :=
  MeasurableExponentialKernel.kernel interiorHaar (exponent β)

theorem partition_identification (β : ℝ) :
    ExponentialJointDisintegration.totalPartition exteriorHaar interiorHaar (exponent β) =
      partition β := by
  exact join_preserving.integral_comp' (fun F => Real.exp (-β*action F))

theorem partition_positive (β : ℝ) : 0 < partition β := by
  rw [← partition_identification]
  exact ExponentialJointDisintegration.total_positive _ _ _ (joint_integrable β)

theorem actual_factorization (β : ℝ) :
    jointLaw β = exteriorLaw β ⊗ₘ conditional β :=
  ExponentialJointDisintegration.factorization _ _ _
    (exponent_measurable β) (section_integrable β)

theorem actual_conditional (β : ℝ) : (jointLaw β).IsCondKernel (conditional β) :=
  ExponentialJointDisintegration.conditional_kernel _ _ _
    (exponent_measurable β) (section_integrable β) (joint_integrable β)

theorem exterior_marginal (β : ℝ) : (jointLaw β).fst = exteriorLaw β :=
  ExponentialJointDisintegration.boundary_marginal _ _ _
    (exponent_measurable β) (section_integrable β) (joint_integrable β)

theorem joint_probability (β : ℝ) : IsProbabilityMeasure (jointLaw β) :=
  ExponentialJointDisintegration.joint_probability _ _ _
    (exponent_measurable β) (section_integrable β) (joint_integrable β)

/-- This is the full Wilson density, not an independently postulated joint law. -/
theorem full_law_identification (β : ℝ) : (jointLaw β).map join = fullLaw β := by
  ext S hS
  rw [Measure.map_apply join.measurable hS]
  unfold jointLaw ExponentialJointDisintegration.joint fullLaw
  rw [withDensity_apply _ (join.measurable hS),withDensity_apply _ hS]
  rw [← lintegral_indicator (join.measurable hS),← lintegral_indicator hS]
  rw [partition_identification]
  have hm : Measurable (S.indicator
      (fun F => ENNReal.ofReal (Real.exp (-β*action F)/partition β))) :=
    (((measurable_const.mul action_measurable).exp.div_const _).ennreal_ofReal).indicator hS
  convert join_preserving.lintegral_comp hm using 1
  apply lintegral_congr
  intro z
  by_cases hz : join z ∈ S <;> simp [Set.indicator, hz, exponent]


/-- The previous three-source model is an explicit exterior, not an arbitrary one. -/
def sourceExterior (b : Fin 3 → SU2) (e : Exterior) : SU2 :=
  FourCubeDirichletBox.link b 1 e.val.val

private theorem exterior_link (b : Fin 3 → SU2) (s : InteriorState) (e : Exterior) :
    FourCubeDirichletBox.link b s e.val.val = FourCubeDirichletBox.link b 1 e.val.val := by
  have hn (i : Interior) : label e.val.val ≠ some (.inl i) := by
    intro h
    apply e.property
    refine ⟨i,Subtype.ext (FourCubeCoreIncident.label_core_source _ i h)⟩
  unfold FourCubeDirichletBox.link
  cases h : label e.val.val with
  | none => rfl
  | some v =>
    cases v with
    | inl i => exact (hn i h).elim
    | inr j => rfl

theorem source_join (b : Fin 3 → SU2) (s : InteriorState) (e : Edge) :
    join (sourceExterior b,s) e = FourCubeDirichletBox.link b s e.val := by
  classical
  by_cases h : e ∈ Set.range core
  · obtain ⟨i,rfl⟩ := h
    rw [join_interior]
    exact (link_interior b s i).symm
  · have he := join_exterior (sourceExterior b) s ⟨e,h⟩
    exact he.trans (exterior_link b s ⟨e,h⟩).symm

theorem source_word (b : Fin 3 → SU2) (s : InteriorState) (p : Face) :
    word (join (sourceExterior b,s)) p = FourCubeDirichletBox.word b s p.val := by
  unfold word
  simp only [source_join]
  rfl

theorem source_action (b : Fin 3 → SU2) (s : InteriorState) :
    action (join (sourceExterior b,s)) = FourCubeDirichletBox.action b s := by
  unfold action FourCubeDirichletBox.action
  simp only [source_word]
  exact Finset.sum_attach faces (fun p => defect (FourCubeDirichletBox.word b s p))

theorem source_kernel (β : ℝ) (b : Fin 3 → SU2) :
    conditional β (sourceExterior b) = FourCubeScalarCalibration.standardLaw β b := by
  rw [conditional, MeasurableExponentialKernel.kernel_apply _ _ (exponent_measurable β)]
  unfold FourCubeScalarCalibration.standardLaw
  congr 1
  funext s
  simp only [MeasurableExponentialKernel.density,MeasurableExponentialKernel.partition,
    exponent,source_action,FourCubeCompletedHaar.standardWeight,
    FourCubeCompletedHaar.standardPartition]


theorem full_probability (β : ℝ) : IsProbabilityMeasure (fullLaw β) := by
  let _ := joint_probability β
  rw [← full_law_identification]
  infer_instance

/-- An actual exterior/core pair reconstructs this full flat field. -/
theorem join_constant (q : SU2) : join (fun _ => q,fun _ => q) = fun _ => q := by
  funext e
  obtain ⟨j,rfl⟩ := indexEquiv.surjective e
  rw [join_apply]
  cases j <;> rfl

theorem constant_flat (q : SU2) (p : Face) : word (fun _ => q) p=1 := by
  unfold word
  group

theorem constant_action_zero (q : SU2) : action (fun _ => q)=0 := by
  simp [action,constant_flat,FourCubePinnedCoercivity.defect_one]

/-- The thin cell's identity-pinned link bound cannot be used at arbitrary exteriors.
This is a gauge-variant link obstruction, not a physical mass-gap obstruction. -/
theorem no_exterior_uniform_pin (i : Interior) (C : ℝ) :
    ¬∀ (A : ExteriorState) (s : InteriorState),
      defect (s i) ≤ C*action (join (A,s)) := by
  intro h
  have hh := h (fun _ => SU2JointPlaquetteCubic.axis 0 Real.pi)
    (fun _ => SU2JointPlaquetteCubic.axis 0 Real.pi)
  rw [join_constant,constant_action_zero,mul_zero] at hh
  norm_num [defect,FourCubeWilsonCubic.axis_trace,Real.cos_pi] at hh

end OperatorDerivativeRewrite.Foundation.FourCubeSpatialConditioning
