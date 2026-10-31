import Foundation.PeriodicAnchoredHaarLimit
import Foundation.PeriodicBoundaryHaarReduction
import Foundation.PeriodicTemporalConcentration
/-! Exact critical gauge fields and nonlinear localization with the compact
root FREE. Existing tree/chord reduction identifies the root centralizer;
fixed-background gauge conjugation transports the complete product Haar law.
Uniform rooted-error envelopes retain all63 relative variables and the common
root, without claiming a stationary spectrum or physical mass gap. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicTransportedRoot
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicGaugeSaturatedGround (root)
open PeriodicBoundaryHaarReduction

def transportedRoot (U : State) (c : SU2) : Gauge :=
  fun v => (rootedGauge U v)⁻¹*c*rootedGauge U v

def chordCentralizes (U : State) (c : SU2) : Prop := ∀ e : ChordIndex,c*reduced U e=reduced U e*c

theorem transported_root (U : State) (c : SU2) : transportedRoot U c root=c := by
  simp [transportedRoot,rooted_root]

theorem fixed_gauge_transport (U : State) (g : Gauge) (hg : gaugeAction g U=U) :
    g=transportedRoot U (g root) := by
  funext v
  have hh := rooted_gauge_covariant g U v
  rw [hg] at hh
  have he := congrArg (fun q : SU2 => (rootedGauge U v)⁻¹*q*g v) hh
  unfold transportedRoot
  convert he using 1 <;> group

theorem fixed_gauge_centralizes (U : State) (g : Gauge) (hg : gaugeAction g U=U) :
    chordCentralizes U (g root) := by
  have hh := reduced_covariant g U
  rw [hg] at hh
  intro e
  have he := congrFun hh e
  change reduced U e=g root*reduced U e*(g root)⁻¹ at he
  calc
    _ = (g root*reduced U e*(g root)⁻¹)*g root := by group
    _ = _ := by rw [← he]

private theorem action_injective (a : Gauge) : Function.Injective (gaugeAction a) := by
  intro U V hh
  funext e
  have he := congrArg (fun q : SU2 => (a e.1)⁻¹*q*a (shift e.1 e.2)) (congrFun hh e)
  unfold gaugeAction at he
  convert he using 1 <;> group

theorem transported_fixes (U : State) (c : SU2) (hc : chordCentralizes U c) :
    gaugeAction (transportedRoot U c) U=U := by
  apply action_injective (rootedGauge U)
  have he : gaugeAction (rootedGauge U) (gaugeAction (transportedRoot U c) U)=
      gaugeAction (fun _ => c) (gaugeAction (rootedGauge U) U) := by
    funext e
    unfold gaugeAction transportedRoot
    group
  rw [he,reconstruction,← axial_conjugate]
  congr 1
  funext e
  unfold conjugate
  rw [hc e]
  group

theorem temporal_zero_iff_transport (U : State) (g : Gauge) :
    temporalAction U U g=0 ↔ g=transportedRoot U (g root) ∧ chordCentralizes U (g root) := by
  rw [PeriodicTemporalConcentration.temporal_zero_iff_alignment]
  constructor
  · intro h
    exact ⟨fixed_gauge_transport U g h.symm,fixed_gauge_centralizes U g h.symm⟩
  · rintro ⟨hg,hc⟩
    calc
      U=gaugeAction (transportedRoot U (g root)) U := (transported_fixes U (g root) hc).symm
      _=gaugeAction g U := by rw [← hg]

open FourCubePinnedCoercivity
open PeriodicGaugeSaturatedGround (depth parent axis parent_depth parent_shift depth_le)

def rootError (U : State) (g : Gauge) (v : SpatialVertex) : SU2 :=
  (rootedGauge U v*g v*(rootedGauge U v)⁻¹)*(g root)⁻¹

theorem rootError_root (U : State) (g : Gauge) : rootError U g root=1 := by
  simp [rootError,rooted_root]

theorem tree_error_step (U : State) (g : Gauge) (v : SpatialVertex) (hv : v≠root) :
    defect (rootError U g v)≤3*(defect (temporalWord U U g (treeEdge v))+
      defect (rootError U g (parent v))) := by
  have he : rootError U g v=
      (rootedGauge U (parent v)*temporalWord U U g (treeEdge v)*(rootedGauge U (parent v))⁻¹)*
        rootError U g (parent v) := by
    unfold rootError
    rw [rooted_parent U v hv]
    unfold temporalWord treeEdge
    rw [parent_shift v hv]
    group
  rw [he]
  have hh := FourCubeBoundaryCoercivity.defect_mul
    (rootedGauge U (parent v)*temporalWord U U g (treeEdge v)*(rootedGauge U (parent v))⁻¹)
    (rootError U g (parent v))
  rwa [PeriodicRootedHaarControl.defect_conjugate] at hh

theorem root_error_bound (U : State) (g : Gauge) (v : SpatialVertex) :
    defect (rootError U g v)≤((3 : ℝ)^(depth v+1)-3)/2*temporalAction U U g := by
  generalize hn : depth v=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v=root
    · subst v
      rw [← hn]
      simp [rootError_root,depth,root,defect_one]
    · have hd := parent_depth v hv
      have hp := ih (depth (parent v)) (by omega) (parent v) rfl
      have hs := tree_error_step U g v hv
      have ht := PeriodicRootedHaarControl.temporal_term_le U U g (treeEdge v)
      have he : ((3 : ℝ)^(depth v+1)-3)/2=
          3+3*(((3 : ℝ)^(depth (parent v)+1)-3)/2) := by
        rw [← hd,pow_succ]
        ring
      rw [← hn,he]
      linarith

theorem root_error_uniform (U : State) (g : Gauge) (v : SpatialVertex) :
    defect (rootError U g v)≤29523*temporalAction U U g := by
  have h := root_error_bound U g v
  have hp : (3 : ℝ)^(depth v+1)≤3^10 :=
    pow_le_pow_right₀ (by norm_num) (by have hd := depth_le v; omega)
  have hn := (temporal_action_bounds U U g).1
  nlinarith

open MeasureTheory
open PeriodicGaugeSaturatedGround (RelField relFieldHaar relField assemble assemble_root assemble_relField
  assemble_measurable assemble_preserving joint_preserving)

def framedGauge (U : State) (g : Gauge) : Gauge :=
  fun v => rootedGauge U v*g v*(rootedGauge U v)⁻¹

def unframedGauge (U : State) (g : Gauge) : Gauge :=
  fun v => (rootedGauge U v)⁻¹*g v*rootedGauge U v

theorem framed_root (U : State) (g : Gauge) : framedGauge U g root=g root := by
  simp [framedGauge,rooted_root]

theorem unframed_root (U : State) (g : Gauge) : unframedGauge U g root=g root := by
  simp [unframedGauge,rooted_root]

theorem framed_unframed (U : State) (g : Gauge) : framedGauge U (unframedGauge U g)=g := by
  funext v
  unfold framedGauge unframedGauge
  group

theorem unframed_framed (U : State) (g : Gauge) : unframedGauge U (framedGauge U g)=g := by
  funext v
  unfold framedGauge unframedGauge
  group

theorem framed_preserving (U : State) : MeasurePreserving (framedGauge U) gaugeHaar gaugeHaar := by
  unfold framedGauge gaugeHaar
  exact measurePreserving_pi (fun _ : SpatialVertex => law) (fun _ : SpatialVertex => law)
    (fun v => (measurePreserving_mul_right law (rootedGauge U v)⁻¹).comp
      (measurePreserving_mul_left law (rootedGauge U v)))

theorem unframed_preserving (U : State) : MeasurePreserving (unframedGauge U) gaugeHaar gaugeHaar := by
  unfold unframedGauge gaugeHaar
  exact measurePreserving_pi (fun _ : SpatialVertex => law) (fun _ : SpatialVertex => law)
    (fun v => (measurePreserving_mul_right law (rootedGauge U v)).comp
      (measurePreserving_mul_left law (rootedGauge U v)⁻¹))

def coordinates (U : State) (g : Gauge) : SU2 × RelField := (g root,relField (framedGauge U g))
def fromCoordinates (U : State) (p : SU2 × RelField) : Gauge := unframedGauge U (assemble p.1 p.2)

theorem coordinates_preserving (U : State) :
    MeasurePreserving (coordinates U) gaugeHaar (law.prod relFieldHaar) := by
  have hh := joint_preserving.comp (framed_preserving U)
  have he : ((fun g : Gauge => (g root,relField g)) ∘ framedGauge U)=coordinates U := by
    funext g
    exact Prod.ext (framed_root U g) rfl
  rw [he] at hh
  exact hh

theorem fromCoordinates_preserving (U : State) :
    MeasurePreserving (fromCoordinates U) (law.prod relFieldHaar) gaugeHaar :=
  (unframed_preserving U).comp assemble_preserving

theorem fromCoordinates_coordinates (U : State) (g : Gauge) : fromCoordinates U (coordinates U g)=g := by
  unfold fromCoordinates coordinates
  rw [← framed_root U g,assemble_relField,unframed_framed]

theorem coordinates_fromCoordinates (U : State) (p : SU2 × RelField) :
    coordinates U (fromCoordinates U p)=p := by
  apply Prod.ext
  · exact (unframed_root _ _).trans (assemble_root _ _)
  · change relField (framedGauge U (unframedGauge U (assemble p.1 p.2)))=p.2
    rw [framed_unframed]
    funext v
    simp [relField,assemble,PeriodicGaugeSaturatedGround.anchored,v.property,mul_assoc]

theorem integral_coordinates (U : State) (f : Gauge → ℝ) (hf : Measurable f) :
    (∫ g,f g ∂gaugeHaar)=∫ p : SU2 × RelField,f (fromCoordinates U p) ∂law.prod relFieldHaar := by
  have h := integral_map (coordinates_preserving U).measurable.aemeasurable
    (μ := gaugeHaar) (f := fun p => f (fromCoordinates U p))
  rw [(coordinates_preserving U).map_eq] at h
  have he := h ((hf.comp (fromCoordinates_preserving U).measurable).aestronglyMeasurable)
  simpa only [Function.comp_apply,fromCoordinates_coordinates] using he.symm

theorem root_error_chart_bound (H : State) (X Y : PeriodicFlatBackgroundHessian.Velocity)
    (t : ℝ) (g : Gauge) (v : SpatialVertex) :
    defect (rootError H g v)≤88569*(temporalAction (PeriodicRootedHaarControl.chartState H X t)
      (PeriodicRootedHaarControl.chartState H Y t) g+t^2*PeriodicRootedHaarControl.budget X Y) := by
  have h := root_error_uniform H g v
  have hc := mul_le_mul_of_nonneg_left (PeriodicRootedHaarControl.ray_comparison H X Y t g)
    (by norm_num : (0 : ℝ)≤29523)
  nlinarith

open SU2GaussianConeCoordinates SU2HemisphereJets PeriodicRelativeGaugeGaussian
open PeriodicRootedHaarControl (chartState budget exteriorRate envelopeRate)
open PeriodicRelativeGaugeTails (smallGauge chart_size_local halfAction_temporal)

theorem rootError_unframed (U : State) (g : Gauge) (v : SpatialVertex) :
    rootError U (unframedGauge U g) v=g v*(g root)⁻¹ := by
  change framedGauge U (unframedGauge U g) v*(unframedGauge U g root)⁻¹=_
  rw [framed_unframed,unframed_root]

def normalGauge (H : State) (Z : Field) (c : SU2) (t : ℝ) : Gauge :=
  unframedGauge H (gaugeRay Z c t)

theorem rootError_ray (H : State) (Z : Field) (c : SU2) (t : ℝ) (v : SpatialVertex) :
    rootError H (normalGauge H Z c t) v=hemisphereChart (t • velocity Z v) := by
  rw [normalGauge,rootError_unframed]
  exact PeriodicRelativeGaugeTails.gaugeRay_relative Z c t v

theorem outside_action (H : State) (X Y : PeriodicFlatBackgroundHessian.Velocity)
    (t : ℝ) (g : Gauge) (hg : framedGauge H g∉smallGauge) :
    exteriorRate≤temporalAction (chartState H X t) (chartState H Y t) g+t^2*budget X Y := by
  change ¬∀ v : SpatialVertex,defect (framedGauge H g v*(framedGauge H g root)⁻¹)<1/4 at hg
  rw [framed_root] at hg
  obtain ⟨v,hv⟩ := not_forall.mp hg
  change ¬defect (rootError H g v)<1/4 at hv
  have hh := root_error_chart_bound H X Y t g v
  have hv' : (1 : ℝ)/4≤defect (rootError H g v) := le_of_not_gt hv
  unfold exteriorRate
  linarith

theorem outside_weight_bound (H : State) (X Y : PeriodicFlatBackgroundHessian.Velocity)
    (t : ℝ) (ht : t≠0) (g : Gauge) (hg : framedGauge H g∉smallGauge) :
    PeriodicWilsonSlab.weight (1/t^2) (chartState H X t) (chartState H Y t) g≤
      Real.exp (budget X Y)*Real.exp (-exteriorRate/t^2) := by
  have h := outside_action H X Y t g hg
  have ha := halfAction_temporal (chartState H X t) (chartState H Y t) g
  have hb : exteriorRate/t^2≤halfAction (chartState H X t) (chartState H Y t) g/t^2+budget X Y := by
    apply (div_le_iff₀ (sq_pos_of_ne_zero ht)).mpr
    rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 ht)]
    nlinarith
  rw [← Real.exp_add]
  unfold PeriodicWilsonSlab.weight
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv,one_mul] at hb ⊢
  linarith

theorem inside_action (H : State) (X Y : PeriodicFlatBackgroundHessian.Velocity)
    (Z : Field) (c : SU2) (t : ℝ) (ht : t≠0) (hg : gaugeRay Z c t∈smallGauge) :
    envelopeRate*fieldSizeSq Z≤
      temporalAction (chartState H X t) (chartState H Y t) (normalGauge H Z c t)/t^2+budget X Y := by
  have he (v : PeriodicGaugeSaturatedGround.RelFieldIndex) : t^2*sizeSq (Z v)≤531414*
      (temporalAction (chartState H X t) (chartState H Y t) (normalGauge H Z c t)+t^2*budget X Y) := by
    have hv := hg v.val
    change defect (gaugeRay Z c t v.val*(gaugeRay Z c t root)⁻¹)<1/4 at hv
    rw [PeriodicRelativeGaugeTails.gaugeRay_relative,velocity_rel] at hv
    have hl := chart_size_local (t • Z v) hv
    have hh := root_error_chart_bound H X Y t (normalGauge H Z c t) v.val
    rw [rootError_ray,velocity_rel] at hh
    have hs : sizeSq (t • Z v)=t^2*sizeSq (Z v) := by
      unfold sizeSq
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
    rw [hs] at hl
    linarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => he v)
  simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,PeriodicGaugeSaturatedGround.rel_count,nsmul_eq_mul] at h
  change t^2*fieldSizeSq Z≤_ at h
  have hf : t^2*fieldSizeSq Z≤t^2*(33479082*
      (temporalAction (chartState H X t) (chartState H Y t) (normalGauge H Z c t)/t^2+budget X Y)) := by
    convert h using 1 <;> field_simp [ht] <;> ring
  have hd := le_of_mul_le_mul_left hf (sq_pos_of_ne_zero ht)
  unfold envelopeRate
  linarith

theorem inside_weight_bound (H : State) (X Y : PeriodicFlatBackgroundHessian.Velocity)
    (Z : Field) (c : SU2) (t : ℝ) (ht : t≠0) (hg : gaugeRay Z c t∈smallGauge) :
    PeriodicWilsonSlab.weight (1/t^2) (chartState H X t) (chartState H Y t) (normalGauge H Z c t)≤
      Real.exp (budget X Y)*Real.exp (-envelopeRate*fieldSizeSq Z) := by
  have h := inside_action H X Y Z c t ht hg
  have ha := div_le_div_of_nonneg_right
    (halfAction_temporal (chartState H X t) (chartState H Y t) (normalGauge H Z c t)) (sq_nonneg t)
  rw [← Real.exp_add]
  unfold PeriodicWilsonSlab.weight
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv,one_mul] at h ha ⊢
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicTransportedRoot
