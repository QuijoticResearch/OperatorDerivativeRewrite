import Foundation.CubeTemporalSlab
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual unit-slab Wilson weights and temporal Haar integration with homogeneous
spatial half-weights. No continuum or uniform spectral-gap theorem is claimed. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeWilsonSlab
open QuaternionSU2Representation CubeTemporalSlab

def spatialAction (U : State) : ℝ := ∑ p : SpatialFace,(1-halfTrace (spatialWord U p))
def temporalAction (U V : State) (g : Gauge) : ℝ := ∑ e : SpatialEdge,(1-halfTrace (temporalWord U V g e))
def halfAction (U V : State) (g : Gauge) : ℝ := spatialAction U/2+temporalAction U V g+spatialAction V/2

def spatialTrace (U : State) : ℝ := ∑ p : SpatialFace,halfTrace (spatialWord U p)
def temporalTrace (U V : State) (g : Gauge) : ℝ := ∑ e : SpatialEdge,halfTrace (temporalWord U V g e)
def spatialHalfWeight (beta : ℝ) (U : State) : ℝ := Real.exp ((beta/2)*spatialTrace U)
def traceWeight (beta : ℝ) (U V : State) (g : Gauge) : ℝ :=
  spatialHalfWeight beta U*Real.exp (beta*temporalTrace U V g)*spatialHalfWeight beta V
def weight (beta : ℝ) (U V : State) (g : Gauge) : ℝ := Real.exp (-beta*halfAction U V g)

theorem spatial_action_formula (U : State) : spatialAction U=6-spatialTrace U := by
  simp [spatialAction,spatialTrace,Finset.sum_sub_distrib,face_count]

theorem temporal_action_formula (U V : State) (g : Gauge) : temporalAction U V g=12-temporalTrace U V g := by
  simp [temporalAction,temporalTrace,Finset.sum_sub_distrib,edge_count]

/-- Exact correspondence with all24 actual unit4-cube plaquettes. -/
theorem full_action (U V : State) (g : Gauge) :
    FourCubeWilsonCubic.innerAction (link U V g)=spatialAction U+spatialAction V+temporalAction U V g := by
  unfold FourCubeWilsonCubic.innerAction
  rw [faces_split,Finset.sum_union faces_disjoint]
  rw [Finset.sum_image (fun a _ b _ h => spatialFace_injective h),
    Finset.sum_image (fun a _ b _ h => temporalFace_injective h)]
  simp only [FourCubeWilsonCubic.faceAction,spatial_word,temporal_word]
  simp [Fintype.sum_prod_type,Fin.sum_univ_two,spatialAction,temporalAction,Finset.sum_add_distrib]
  <;> ring

/-- Half spatial boundary sharing, rather than relabeling the full24-face action. -/
theorem half_action_full (U V : State) (g : Gauge) :
    halfAction U V g=FourCubeWilsonCubic.innerAction (link U V g)-
      (spatialAction U+spatialAction V)/2 := by
  rw [full_action]
  unfold halfAction
  ring

/-- Both spatial weights and the kinetic weight have the SAME beta. -/
theorem trace_weight_factor (beta : ℝ) (U V : State) (g : Gauge) :
    traceWeight beta U V g=Real.exp (18*beta)*weight beta U V g := by
  unfold traceWeight spatialHalfWeight weight
  rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
  congr 1
  unfold halfAction
  rw [spatial_action_formula,spatial_action_formula,temporal_action_formula]
  ring

theorem spatial_action_bounds (U : State) : 0 ≤ spatialAction U ∧ spatialAction U ≤ 12 := by
  have he (p : SpatialFace) := abs_le.mp (halfTrace_bound (spatialWord U p))
  constructor
  · exact Finset.sum_nonneg (fun p _ => by linarith [(he p).2])
  · calc
      _ ≤ ∑ _ : SpatialFace,(2 : ℝ) := Finset.sum_le_sum (fun p _ => by linarith [(he p).1])
      _ = 12 := by norm_num [face_count]

theorem temporal_action_bounds (U V : State) (g : Gauge) :
    0 ≤ temporalAction U V g ∧ temporalAction U V g ≤ 24 := by
  have he (e : SpatialEdge) := abs_le.mp (halfTrace_bound (temporalWord U V g e))
  constructor
  · exact Finset.sum_nonneg (fun e _ => by linarith [(he e).2])
  · calc
      _ ≤ ∑ _ : SpatialEdge,(2 : ℝ) := Finset.sum_le_sum (fun e _ => by linarith [(he e).1])
      _ = 24 := by norm_num [edge_count]

theorem half_action_bounds (U V : State) (g : Gauge) : 0 ≤ halfAction U V g ∧ halfAction U V g ≤ 36 := by
  have hU := spatial_action_bounds U
  have hV := spatial_action_bounds V
  have hg := temporal_action_bounds U V g
  unfold halfAction
  constructor <;> linarith

theorem weight_bounds (beta : ℝ) (U V : State) (g : Gauge) :
    Real.exp (-36*|beta|) ≤ weight beta U V g ∧ weight beta U V g ≤ Real.exp (36*|beta|) := by
  have hh := half_action_bounds U V g
  have ha : |-beta*halfAction U V g| ≤ 36*|beta| := by
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
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (36*|beta|))
  filter_upwards with g
  rw [weight]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  simpa only [weight] using (weight_bounds beta U V g).2

theorem kernel_bounds (beta : ℝ) (U V : State) :
    Real.exp (-36*|beta|) ≤ kernel beta U V ∧ kernel beta U V ≤ Real.exp (36*|beta|) := by
  unfold kernel
  constructor
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (integrable_const (Real.exp (-36*|beta|))) (weight_integrable beta U V)
        (fun g => (weight_bounds beta U V g).1)
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (weight_integrable beta U V) (integrable_const (Real.exp (36*|beta|)))
        (fun g => (weight_bounds beta U V g).2)

theorem kernel_positive (beta : ℝ) (U V : State) : 0 < kernel beta U V :=
  (Real.exp_pos _).trans_le (kernel_bounds beta U V).1

theorem kernel_joint_measurable (beta : ℝ) : Measurable (Function.uncurry (kernel beta)) :=
  (weight_joint_measurable beta).stronglyMeasurable.integral_prod_right.measurable

/-- Actual temporal Haar integration preserves the exact defect/trace normalization. -/
theorem trace_integral_factor (beta : ℝ) (U V : State) :
    (∫ g,traceWeight beta U V g ∂gaugeHaar)=Real.exp (18*beta)*kernel beta U V := by
  simp_rw [trace_weight_factor]
  exact integral_const_mul _ _

end OperatorDerivativeRewrite.Foundation.CubeWilsonSlab
