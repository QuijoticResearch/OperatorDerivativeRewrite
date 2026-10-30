import Foundation.CubePolynomialGround

/-! Actual temporal Haar root/relative coordinates, retaining the free global root. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.CubeTemporalRootHaar
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab SU2HaarSmallCap

private instance vertexDecidableEq : DecidableEq SpatialVertex :=
  fun v w => decidable_of_decidable_of_iff (p := ∀ i,v i=w i) funext_iff.symm

def root : SpatialVertex := fun _ => 0
abbrev RootIndex := {v : SpatialVertex // v=root}
abbrev RelativeIndex := {v : SpatialVertex // ¬v=root}
private instance rootIndexFintype : Fintype RootIndex := Subtype.fintype (fun v => v=root)

abbrev RootField := RootIndex → SU2
abbrev Relative := RelativeIndex → SU2

def rootHaar : Measure RootField := Measure.pi (fun _ => law)
def relativeHaar : Measure Relative := Measure.pi (fun _ => law)
instance root_probability : IsProbabilityMeasure rootHaar := by unfold rootHaar; infer_instance
instance relative_probability : IsProbabilityMeasure relativeHaar := by unfold relativeHaar; infer_instance

def split : Gauge ≃ᵐ (RootField × Relative) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : SpatialVertex => SU2) (fun v => v=root)

theorem split_preserving : MeasurePreserving split gaugeHaar (rootHaar.prod relativeHaar) := by
  simpa only [split,gaugeHaar,rootHaar,relativeHaar] using
    measurePreserving_piEquivPiSubtypeProd (fun _ : SpatialVertex => law) (fun v => v=root)

def relative (g : Gauge) (v : RelativeIndex) : SU2 := g v.val*(g root)⁻¹

theorem relative_measurable : Measurable relative := by
  apply measurable_pi_iff.mpr
  intro v
  exact (measurable_pi_apply v.val).mul (measurable_pi_apply root).inv

private theorem raw_preserving :
    MeasurePreserving (fun g : Gauge => (g root,fun v : RelativeIndex => g v.val))
      gaugeHaar (law.prod relativeHaar) := by
  have hr : MeasurePreserving (fun c : RootField => c ⟨root,rfl⟩) rootHaar law := by
    unfold rootHaar
    exact measurePreserving_eval (fun _ : RootIndex => law) ⟨root,rfl⟩
  have h := (hr.prod (MeasurePreserving.id relativeHaar)).comp split_preserving
  convert h using 1
  funext g
  rfl

/-- The actual global root is independent Haar, and all seven relative variables
remain independent Haar. No pointwise root fixing is performed. -/
theorem joint_preserving :
    MeasurePreserving (fun g : Gauge => (g root,relative g)) gaugeHaar (law.prod relativeHaar) := by
  have hm : Measurable (fun p : SU2 × Relative => fun v : RelativeIndex => p.2 v*p.1⁻¹) := by
    apply measurable_pi_iff.mpr
    intro v
    exact ((measurable_pi_apply v).comp measurable_snd).mul measurable_fst.inv
  have hc (c : SU2) :
      MeasurePreserving (fun h : Relative => fun v => h v*c⁻¹) relativeHaar relativeHaar := by
    unfold relativeHaar
    exact measurePreserving_pi (fun _ : RelativeIndex => law) (fun _ : RelativeIndex => law)
      (fun _ => measurePreserving_mul_right law c⁻¹)
  have hs := (MeasurePreserving.id law).skew_product hm
    (ae_of_all law (fun c => (hc c).map_eq))
  exact hs.comp raw_preserving

theorem relative_preserving : MeasurePreserving relative gaugeHaar relativeHaar :=
  (measurePreserving_snd (μ := law) (ν := relativeHaar)).comp joint_preserving

def anchored (h : Relative) (v : SpatialVertex) : SU2 :=
  if hv : v=root then 1 else h ⟨v,hv⟩
def assemble (c : SU2) (h : Relative) (v : SpatialVertex) : SU2 := anchored h v*c

theorem anchored_root (h : Relative) : anchored h root=1 := by simp [anchored]
theorem assemble_root (c : SU2) (h : Relative) : assemble c h root=c := by
  simp [assemble,anchored_root]

theorem assemble_relative (g : Gauge) : assemble (g root) (relative g)=g := by
  funext v
  by_cases hv : v=root
  · subst v
    exact assemble_root _ _
  · simp [assemble,anchored,hv,relative,mul_assoc]

theorem assemble_measurable : Measurable (fun p : SU2 × Relative => assemble p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro v
  unfold assemble anchored
  split_ifs <;> fun_prop

/-- The reconstruction transports product Haar back to the actual temporal law. -/
theorem assemble_preserving :
    MeasurePreserving (fun p : SU2 × Relative => assemble p.1 p.2) (law.prod relativeHaar) gaugeHaar := by
  refine ⟨assemble_measurable,?_⟩
  rw [← joint_preserving.map_eq,Measure.map_map assemble_measurable joint_preserving.measurable]
  have he : (fun g : Gauge => assemble (g root) (relative g))=id := funext assemble_relative
  change Measure.map (fun g : Gauge => assemble (g root) (relative g)) gaugeHaar = gaugeHaar
  rw [he,Measure.map_id]

/-- Exact product-Haar integral with the free root and every relative link retained. -/
theorem integral_split (f : Gauge → ℝ) (hf : Measurable f) :
    (∫ g,f g ∂gaugeHaar)=∫ p : SU2 × Relative,f (assemble p.1 p.2) ∂law.prod relativeHaar := by
  have h := integral_map joint_preserving.measurable.aemeasurable
    (μ := gaugeHaar) (f := fun p : SU2 × Relative => f (assemble p.1 p.2))
  rw [joint_preserving.map_eq] at h
  have he := h ((hf.comp assemble_measurable).aestronglyMeasurable)
  simpa only [Function.comp_apply,assemble_relative] using he.symm

def box (t : ℝ) : Set Relative := Set.univ.pi (fun _ => cap t)
def cylinder (t : ℝ) : Set Gauge := relative ⁻¹' box t

theorem relative_count : Fintype.card RelativeIndex=7 := by decide +kernel

theorem box_measurable (t : ℝ) : MeasurableSet (box t) := MeasurableSet.univ_pi (fun _ => cap_measurable t)
theorem cylinder_measurable (t : ℝ) : MeasurableSet (cylinder t) :=
  (box_measurable t).preimage relative_measurable

theorem cylinder_mass (t : ℝ) : gaugeHaar.real (cylinder t)=(law.real (cap t))^7 := by
  have h := Measure.map_apply relative_measurable (box_measurable t) (μ := gaugeHaar)
  rw [relative_preserving.map_eq] at h
  change (gaugeHaar (relative ⁻¹' box t)).toReal=(law (cap t)).toReal^7
  rw [← h]
  simp only [relativeHaar,box,Measure.pi_pi,Finset.prod_const,Finset.card_univ,
    relative_count,ENNReal.toReal_pow]

theorem anchored_cap (t : ℝ) (h : Relative) (hh : h ∈ box t) (v : SpatialVertex) :
    anchored h v ∈ cap t := by
  unfold anchored
  split_ifs with hv
  · change FourCubePinnedCoercivity.defect 1 ≤ 3*t^2
    rw [FourCubePinnedCoercivity.defect_one]
    positivity
  · exact hh ⟨v,hv⟩ (Set.mem_univ _)

end OperatorDerivativeRewrite.Foundation.CubeTemporalRootHaar
