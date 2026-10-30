import Foundation.PeriodicTemporalSlab
import Foundation.CubeSlabGauge

/-! The actual periodic spatial-slice transfer kernel, integrated over all temporal
links. Bounds here depend on coupling and fixed volume; they are not mass gaps. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicWilsonSlab
open QuaternionSU2Representation PeriodicTemporalSlab

def spatialAction (U : State) : ℝ := ∑ p : SpatialFace,(1-halfTrace (spatialWord U p))
def temporalAction (U V : State) (g : Gauge) : ℝ :=
  ∑ e : SpatialEdge,(1-halfTrace (temporalWord U V g e))
def halfAction (U V : State) (g : Gauge) : ℝ :=
  spatialAction U/2+temporalAction U V g+spatialAction V/2

def weight (beta : ℝ) (U V : State) (g : Gauge) : ℝ := Real.exp (-beta*halfAction U V g)

attribute [local irreducible] spatialAction temporalAction

theorem spatial_action_bounds (U : State) : 0 ≤ spatialAction U ∧ spatialAction U ≤ 384 := by
  unfold spatialAction
  have he (p : SpatialFace) := abs_le.mp (halfTrace_bound (spatialWord U p))
  constructor
  · exact Finset.sum_nonneg (fun p _ => by linarith [(he p).2])
  · calc
      _ ≤ ∑ _ : SpatialFace,(2 : ℝ) := Finset.sum_le_sum (fun p _ => by linarith [(he p).1])
      _ = 384 := by norm_num [face_count]

theorem temporal_action_bounds (U V : State) (g : Gauge) :
    0 ≤ temporalAction U V g ∧ temporalAction U V g ≤ 384 := by
  unfold temporalAction
  have he (e : SpatialEdge) := abs_le.mp (halfTrace_bound (temporalWord U V g e))
  constructor
  · exact Finset.sum_nonneg (fun e _ => by linarith [(he e).2])
  · calc
      _ ≤ ∑ _ : SpatialEdge,(2 : ℝ) := Finset.sum_le_sum (fun e _ => by linarith [(he e).1])
      _ = 384 := by norm_num [edge_count]

theorem half_action_bounds (U V : State) (g : Gauge) : 0 ≤ halfAction U V g ∧ halfAction U V g ≤ 768 := by
  have hU := spatial_action_bounds U
  have hV := spatial_action_bounds V
  have hg := temporal_action_bounds U V g
  unfold halfAction
  constructor <;> linarith

theorem weight_bounds (beta : ℝ) (U V : State) (g : Gauge) :
    Real.exp (-768*|beta|) ≤ weight beta U V g ∧ weight beta U V g ≤ Real.exp (768*|beta|) := by
  have hh := half_action_bounds U V g
  have ha : |-beta*halfAction U V g| ≤ 768*|beta| := by
    rw [abs_mul,abs_neg,abs_of_nonneg hh.1]
    nlinarith [mul_le_mul_of_nonneg_left hh.2 (abs_nonneg beta)]
  have he := abs_le.mp ha
  exact ⟨Real.exp_le_exp.mpr (by linarith [he.1]),Real.exp_le_exp.mpr he.2⟩

theorem spatial_action_measurable : Measurable spatialAction := by
  unfold spatialAction
  apply Finset.measurable_sum
  intro p _
  exact measurable_const.sub (halfTrace_measurable.comp (by unfold spatialWord; fun_prop))

theorem temporal_action_joint_measurable :
    Measurable (fun q : (State × State) × Gauge => temporalAction q.1.1 q.1.2 q.2) := by
  unfold temporalAction
  apply Finset.measurable_sum
  intro e _
  exact measurable_const.sub (halfTrace_measurable.comp (by unfold temporalWord; fun_prop))

theorem weight_joint_measurable (beta : ℝ) :
    Measurable (fun q : (State × State) × Gauge => weight beta q.1.1 q.1.2 q.2) := by
  unfold weight halfAction
  exact (((spatial_action_measurable.comp (measurable_fst.comp measurable_fst)).div_const 2 |>.add
    temporal_action_joint_measurable).add
      ((spatial_action_measurable.comp (measurable_snd.comp measurable_fst)).div_const 2)).const_mul (-beta) |>.exp

def gaugeHaar : Measure Gauge := Measure.pi (fun _ => law)
instance gaugeHaar_probability : IsProbabilityMeasure gaugeHaar := by unfold gaugeHaar; infer_instance

def boundaryHaar : Measure State := Measure.pi (fun _ => law)
instance boundaryHaar_probability : IsProbabilityMeasure boundaryHaar := by unfold boundaryHaar; infer_instance

def kernel (beta : ℝ) (U V : State) : ℝ := ∫ g,weight beta U V g ∂gaugeHaar

attribute [local irreducible] weight gaugeHaar boundaryHaar

theorem weight_integrable (beta : ℝ) (U V : State) : Integrable (weight beta U V) gaugeHaar := by
  have hc : Measurable (fun g : Gauge => ((U,V),g)) :=
    measurable_const.prodMk measurable_id
  have hm : Measurable (fun g : Gauge => weight beta U V g) :=
    (weight_joint_measurable beta).comp hc
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (768*|beta|))
  filter_upwards with g
  rw [weight]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  simpa only [weight] using (weight_bounds beta U V g).2

theorem kernel_bounds (beta : ℝ) (U V : State) :
    Real.exp (-768*|beta|) ≤ kernel beta U V ∧ kernel beta U V ≤ Real.exp (768*|beta|) := by
  unfold kernel
  constructor
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (integrable_const (Real.exp (-768*|beta|))) (weight_integrable beta U V)
        (fun g => (weight_bounds beta U V g).1)
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (weight_integrable beta U V) (integrable_const (Real.exp (768*|beta|)))
        (fun g => (weight_bounds beta U V g).2)

theorem kernel_positive (beta : ℝ) (U V : State) : 0 < kernel beta U V :=
  (Real.exp_pos _).trans_le (kernel_bounds beta U V).1

theorem kernel_joint_measurable (beta : ℝ) : Measurable (Function.uncurry (kernel beta)) :=
  (weight_joint_measurable beta).stronglyMeasurable.integral_prod_right.measurable

theorem temporal_swap (U V : State) (g : Gauge) (e : SpatialEdge) :
    halfTrace (temporalWord V U g⁻¹ e)=halfTrace (temporalWord U V g e) := by
  have he : temporalWord V U g⁻¹ e=
      (g e.1)⁻¹*(temporalWord U V g e)⁻¹*g e.1 := by
    unfold temporalWord
    simp only [Pi.inv_apply]
    group
  rw [he]
  have hc := halfTrace_conjugate ((g e.1)⁻¹) ((temporalWord U V g e)⁻¹)
  simpa only [inv_inv] using hc.trans (SU2WilsonConvolution.halfTrace_inv _)

theorem weight_swap (beta : ℝ) (U V : State) (g : Gauge) :
    weight beta V U g⁻¹=weight beta U V g := by
  have ht : temporalAction V U g⁻¹=temporalAction U V g := by
    unfold temporalAction
    apply Finset.sum_congr rfl
    intro e _
    rw [temporal_swap U V g e]
  unfold weight halfAction
  rw [ht]
  congr 1
  ring

private theorem su2_inv_preserving : MeasurePreserving (fun A : SU2 => A⁻¹) law law := by
  letI : IsProbabilityMeasure law.inv := by
    change IsProbabilityMeasure (law.map (fun A : SU2 => A⁻¹))
    infer_instance
  letI : law.inv.IsHaarMeasure :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior law.inv Set.univ isCompact_univ
      (by simp) (by simp) (by simp)
  have h : law.inv=law := (law_eq_probability_haar law.inv).symm
  exact ⟨measurable_inv,h⟩

theorem gauge_inv_preserving : MeasurePreserving (fun g : Gauge => g⁻¹) gaugeHaar gaugeHaar := by
  unfold gaugeHaar
  exact measurePreserving_pi (fun _ => law) (fun _ => law) (fun _ => su2_inv_preserving)

/-- Symmetry of the actual temporal-integrated kernel; not an operator positivity claim. -/
theorem kernel_symmetric (beta : ℝ) (U V : State) : kernel beta U V=kernel beta V U := by
  have h := gauge_inv_preserving.integral_comp (MeasurableEquiv.inv Gauge).measurableEmbedding
    (weight beta V U)
  change (∫ g,weight beta V U g⁻¹ ∂gaugeHaar)=kernel beta V U at h
  rw [← h]
  simp_rw [weight_swap]
  rfl

/-- Constructed positive eigenfunction of this actual periodic kernel, not a supplied vacuum. -/
theorem positive_ground_exists (beta : ℝ) :
    ∃ lam : ℝ, ∃ psi : State → ℝ, 0 < lam ∧ Measurable psi ∧
      (∀ U,Real.exp (-768*|beta|)/Real.exp (768*|beta|) ≤ psi U ∧
        psi U ≤ Real.exp (768*|beta|)/Real.exp (-768*|beta|)) ∧
      (∀ U,∫ V,kernel beta U V*psi V ∂boundaryHaar=lam*psi U) := by
  obtain ⟨lam,psi,hl,_,hm,hb,he⟩ :=
    YMPositivePower.positive_eigenfunction_exists boundaryHaar (kernel beta)
      (Real.exp (-768*|beta|)) (Real.exp (768*|beta|)) (kernel_joint_measurable beta)
      (Real.exp_pos _) (kernel_bounds beta) (fun _ => 1)
  exact ⟨lam,psi,(Real.exp_pos _).trans_le hl,hm,hb,he⟩

end OperatorDerivativeRewrite.Foundation.PeriodicWilsonSlab
