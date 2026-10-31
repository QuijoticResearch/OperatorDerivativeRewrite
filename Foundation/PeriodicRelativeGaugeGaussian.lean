import Foundation.PeriodicConstantRootLimit
import Foundation.SU2FourCurveJetTransfer
import Foundation.PeriodicGaugeSaturatedGround
/-! Actual periodic Wilson mixed temporal jet with all63 anchored relative
SU(2) triples. Periodic gradient cancellation splits the common-root energy
from a coercive anchored graph energy. Its Gaussian is integrable with positive
mass, and the joint limiting integral factors exactly. This does not pass the
rescaled full Haar kernel to its limit: chart Jacobians and uniform tail control
remain separate obligations. No stationary spectrum or mass gap is asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped Quaternion Matrix Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicRelativeGaugeGaussian
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart SU2HemisphereJets
open SU2RootAdjoint PeriodicConstantQuarticJet PeriodicConstantRootLimit PeriodicTemporalSlab PeriodicWilsonSlab
open PeriodicGaugeSaturatedGround
attribute [local irreducible] SU2RootAdjoint.rotate sizeSq halfAction spatialAction temporalAction

abbrev Field := RelFieldIndex → Triple

def velocity (Z : Field) (v : SpatialVertex) : Triple := if hv : v=root then 0 else Z ⟨v,hv⟩
def chartField (Z : Field) (t : ℝ) : RelField := fun v => hemisphereChart (t • Z v)
def gaugeRay (Z : Field) (c : SU2) (t : ℝ) : Gauge := assemble c (chartField Z t)

theorem velocity_root (Z : Field) : velocity Z root=0 := by simp [velocity]
theorem velocity_rel (Z : Field) (v : RelFieldIndex) : velocity Z v.val=Z v := by simp [velocity,v.property]

theorem gaugeRay_apply (Z : Field) (c : SU2) (t : ℝ) (v : SpatialVertex) :
    gaugeRay Z c t v=hemisphereChart (t • velocity Z v)*c := by
  unfold gaugeRay assemble anchored chartField velocity
  split_ifs with hv
  · rw [smul_zero,CubeChartAction.chart_zero]
  · rfl

def wordRay (v : Fin 4 → Triple) (t : ℝ) : ℝ :=
  SU2FourCurveJetTransfer.traceAction (fun i => SU2HemisphereJets.curve (v i) t)

theorem frame_signed (u v w z : Triple) : frame u+frame v-frame w-frame z=frame (u+v-w-z) := by
  ext i
  fin_cases i <;> simp [frame] <;> ring

theorem word_jet (v : Fin 4 → Triple) :
    ContDiff ℝ 2 (wordRay v) ∧ wordRay v 0=0 ∧ deriv (wordRay v) 0=0 ∧
      deriv (deriv (wordRay v)) 0=sizeSq (v 0+v 1-v 2-v 3) := by
  have h := SU2FourCurveJetTransfer.trace_component_jets
    (fun t i => SU2HemisphereJets.curve (v i) t) (fun i => frame (v i))
    (fun i => CubeChartAction.curve_contDiff (v i))
    (fun i => curve_zero (v i)) (fun i => curve_first_zero (v i))
    (fun i => curve_second_generator (v i))
  have he : SU2MatrixExponentialBridge.lengthSq (frame (v 0)+frame (v 1)-frame (v 2)-frame (v 3))/4=
      sizeSq (v 0+v 1-v 2-v 3) := by
    rw [frame_signed,lengthSq_frame]
    ring
  refine ⟨h.1,?_,h.2.1,h.2.2.trans he⟩
  unfold wordRay SU2FourCurveJetTransfer.traceAction
  simp only [curve_zero]
  norm_num [SU2TraceHessianModel.traceReal,Matrix.trace_fin_two]

theorem word_quadratic_limit (v : Fin 4 → Triple) :
    Tendsto (fun t : ℝ => wordRay v t/t^2) (𝓝[≠] 0)
      (𝓝 (sizeSq (v 0+v 1-v 2-v 3)/2)) := by
  let f := wordRay v
  let q := sizeSq (v 0+v 1-v 2-v 3)
  have hj := word_jet v
  have hf : ContDiff ℝ 2 f := hj.1
  have h0 : f 0=0 := hj.2.1
  have h1 : deriv f 0=0 := hj.2.2.1
  have h2 : deriv (deriv f) 0=q := hj.2.2.2
  have ht (t : ℝ) : taylorWithinEval f 2 Set.univ 0 t=(q/2)*t^2 := by
    simp [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_univ,
      iteratedDeriv_succ,iteratedDeriv_zero,h0,h1,h2]
    ring
  have hr : (fun t : ℝ => f t-(q/2)*t^2)=o[𝓝 0](fun t : ℝ => t^2) := by
    simpa only [ht,sub_zero] using taylor_isLittleO_univ (x₀ := 0) (n := 2) hf
  have h := ((hr.tendsto_div_nhds_zero.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ)≤𝓝 0)).add_const (q/2))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : t≠0 := ht
  field_simp [hn]
  <;> ring

theorem temporal_word_ray (a b : Velocities) (Z : Field) (c : SU2) (t : ℝ) (e : SpatialEdge) :
    temporalWord (constantState a t) (constantState b t) (gaugeRay Z c t) e=
      hemisphereChart (t • a e.2)*hemisphereChart (t • velocity Z (shift e.1 e.2))*
        (hemisphereChart (t • rotate c (b e.2)))⁻¹*(hemisphereChart (t • velocity Z e.1))⁻¹ := by
  unfold temporalWord constantState
  rw [gaugeRay_apply,gaugeRay_apply,← rotate_smul,← chart_conjugates]
  group

theorem temporal_word_action (a b : Velocities) (Z : Field) (c : SU2) (t : ℝ) (e : SpatialEdge) :
    1-halfTrace (temporalWord (constantState a t) (constantState b t) (gaugeRay Z c t) e)=
      wordRay ![a e.2,velocity Z (shift e.1 e.2),rotate c (b e.2),velocity Z e.1] t := by
  rw [temporal_word_ray]
  rfl

def gradient (Z : Field) (e : SpatialEdge) : Triple := velocity Z (shift e.1 e.2)-velocity Z e.1
def graphEnergy (Z : Field) : ℝ := (∑ e : SpatialEdge,sizeSq (gradient Z e))/2
def mixedEnergy (a b : Velocities) (c : SU2) (Z : Field) : ℝ :=
  (∑ e : SpatialEdge,sizeSq (a e.2-rotate c (b e.2)+gradient Z e))/2

theorem mixed_temporal_limit (a b : Velocities) (Z : Field) (c : SU2) :
    Tendsto (fun t : ℝ => temporalAction (constantState a t) (constantState b t) (gaugeRay Z c t)/t^2)
      (𝓝[≠] 0) (𝓝 (mixedEnergy a b c Z)) := by
  have h := tendsto_finsetSum Finset.univ (fun e (_ : e∈(Finset.univ : Finset SpatialEdge)) =>
    word_quadratic_limit ![a e.2,velocity Z (shift e.1 e.2),rotate c (b e.2),velocity Z e.1])
  have he (e : SpatialEdge) : a e.2+velocity Z (shift e.1 e.2)-rotate c (b e.2)-velocity Z e.1=
      a e.2-rotate c (b e.2)+gradient Z e := by unfold gradient; abel
  change Tendsto _ _ (𝓝 (∑ e : SpatialEdge, sizeSq (a e.2+velocity Z (shift e.1 e.2)-rotate c (b e.2)-velocity Z e.1)/2)) at h
  simp_rw [he] at h
  have hf : (fun t : ℝ => temporalAction (constantState a t) (constantState b t) (gaugeRay Z c t)/t^2)=
      (fun t => ∑ e : SpatialEdge,wordRay ![a e.2,velocity Z (shift e.1 e.2),rotate c (b e.2),velocity Z e.1] t/t^2) := by
    funext t
    unfold temporalAction
    simp_rw [temporal_word_action]
    exact Finset.sum_div _ _ _
  rw [hf]
  simpa only [mixedEnergy,Finset.sum_div] using h


theorem sum_shift (f : SpatialVertex → ℝ) (i : Fin 3) :
    (∑ v : SpatialVertex,f (shift v i))=∑ v : SpatialVertex,f v := by
  let w : SpatialVertex := fun k => if k=i then 1 else 0
  change (∑ v : SpatialVertex,f ((Equiv.addRight w) v))=∑ v : SpatialVertex,f v
  exact Fintype.sum_equiv (Equiv.addRight w) _ _ (fun _ => rfl)

theorem sum_gradient (Z : Field) (i j : Fin 3) :
    (∑ v : SpatialVertex,gradient Z (v,i) j)=0 := by
  simp only [gradient,Pi.sub_apply,Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (sum_shift (fun v => velocity Z v j) i)

theorem sizeSq_add (u v : Triple) : sizeSq (u+v)=sizeSq u+sizeSq v+2*dot3 u v := by
  unfold sizeSq dot3
  simp only [Pi.add_apply]
  ring

theorem sum_dot_gradient (Z : Field) (i : Fin 3) (u : Triple) :
    (∑ v : SpatialVertex,dot3 u (gradient Z (v,i)))=0 := by
  simp only [dot3,Finset.sum_add_distrib,← Finset.mul_sum,sum_gradient,mul_zero,add_zero]

/-- Actual periodic gradient cancellation keeps the constant root-dependent
source orthogonal to all relative gauge velocities. -/
theorem mixedEnergy_split (a b : Velocities) (c : SU2) (Z : Field) :
    mixedEnergy a b c Z=rootEnergy a b c+graphEnergy Z := by
  have hc : (∑ e : SpatialEdge,dot3 (a e.2-rotate c (b e.2)) (gradient Z e))=0 := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [sum_dot_gradient,Finset.sum_const_zero]
  have hm : (∑ e : SpatialEdge,sizeSq (a e.2-rotate c (b e.2)))=
      64*∑ i : Fin 3,sizeSq (a i-rotate c (b i)) := by
    simp only [SpatialEdge,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    norm_num [SpatialVertex,Fintype.card_fun]
  unfold mixedEnergy
  simp_rw [sizeSq_add]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  rw [hc,hm]
  unfold rootEnergy graphEnergy
  ring

theorem mixed_halfAction_limit (a b : Velocities) (Z : Field) (c : SU2) :
    Tendsto (fun t : ℝ => halfAction (constantState a t) (constantState b t) (gaugeRay Z c t)/t^2)
      (𝓝[≠] 0) (𝓝 (rootEnergy a b c+graphEnergy Z)) := by
  have h := (((spatial_quadratic_vanish a).div_const 2).add
    (mixed_temporal_limit a b Z c)).add ((spatial_quadratic_vanish b).div_const 2)
  simp only [zero_div,zero_add,add_zero,mixedEnergy_split] at h
  convert h using 1
  funext t
  unfold halfAction
  ring

theorem mixed_weight_limit (a b : Velocities) (Z : Field) (c : SU2) :
    Tendsto (fun t : ℝ => PeriodicWilsonSlab.weight (1/t^2) (constantState a t) (constantState b t) (gaugeRay Z c t))
      (𝓝[≠] 0) (𝓝 (gaussianIntegrand a b c*Real.exp (-graphEnergy Z))) := by
  have h := (Real.continuous_exp.tendsto (-(rootEnergy a b c+graphEnergy Z))).comp
    (mixed_halfAction_limit a b Z c).neg
  simp only [neg_add,Real.exp_add] at h
  unfold gaussianIntegrand
  convert h using 1
  funext t
  unfold PeriodicWilsonSlab.weight
  congr 1
  ring


private theorem term_le_fintype_sum {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i,0 ≤ f i) (i : ι) : f i ≤ ∑ j,f j := by
  exact Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

theorem gauge_relative_point_bound (g : Gauge) (v : SpatialVertex) :
    FourCubePinnedCoercivity.defect (g v*(g root)⁻¹) ≤
      (4 : ℝ)^10*temporalAction (1 : State) 1 g := by
  classical
  apply rooted_uniform g _ (temporal_action_bounds (1 : State) 1 g).1
  intro e
  have hi : (g e.1*(g (shift e.1 e.2))⁻¹)⁻¹=g (shift e.1 e.2)*(g e.1)⁻¹ := by group
  rw [← FourCubePinnedCoercivity.defect_inv,hi]
  change (1-halfTrace (g (shift e.1 e.2)*(g e.1)⁻¹)) ≤ _
  have he : temporalWord (1 : State) 1 g e=g (shift e.1 e.2)*(g e.1)⁻¹ := by
    simp [temporalWord]
  rw [← he]
  unfold temporalAction
  exact term_le_fintype_sum (fun k : SpatialEdge => 1-halfTrace (temporalWord (1 : State) 1 g k))
    (fun k => sub_nonneg.mpr (abs_le.mp (halfTrace_bound _)).2) e

theorem rotate_zero (c : SU2) : rotate c (0 : Triple)=0 := by
  simpa only [zero_smul] using rotate_smul c 0 (0 : Triple)

theorem zero_mixedEnergy (c : SU2) (Z : Field) : mixedEnergy 0 0 c Z=graphEnergy Z := by
  unfold mixedEnergy graphEnergy
  simp only [Pi.zero_apply,rotate_zero,sub_self,zero_add]

theorem velocity_coercive (Z : Field) (v : SpatialVertex) :
    sizeSq (velocity Z v) ≤ (2*4^10 : ℝ)*graphEnergy Z := by
  have hl := relative_quadratic_limit (velocity Z v) 0
  simp only [smul_zero,CubeChartAction.chart_zero,inv_one,mul_one,sub_zero] at hl
  have hr := (mixed_temporal_limit 0 0 Z 1).const_mul ((4 : ℝ)^10)
  simp only [constantState_zero,zero_mixedEnergy] at hr
  have hp : ∀ t : ℝ, (1-halfTrace (hemisphereChart (t • velocity Z v)))/t^2 ≤
      (4 : ℝ)^10*(temporalAction (1 : State) 1 (gaugeRay Z 1 t)/t^2) := by
    intro t
    have h := gauge_relative_point_bound (gaugeRay Z 1 t) v
    rw [gaugeRay_apply,gaugeRay_apply,velocity_root,smul_zero,CubeChartAction.chart_zero] at h
    simp only [mul_one,inv_one] at h
    have hd := div_le_div_of_nonneg_right h (sq_nonneg t)
    simpa only [FourCubePinnedCoercivity.defect,mul_div_assoc] using hd
  have h := le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall hp)
  nlinarith

def fieldSizeSq (Z : Field) : ℝ := ∑ v : RelFieldIndex,sizeSq (Z v)

theorem graph_coercive (Z : Field) :
    fieldSizeSq Z ≤ (126*4^10 : ℝ)*graphEnergy Z := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (v : RelFieldIndex) _ => velocity_coercive Z v.val)
  simp only [velocity_rel,Finset.sum_const,Finset.card_univ,rel_count,nsmul_eq_mul] at h
  unfold fieldSizeSq
  convert h using 1 <;> ring

theorem graphEnergy_nonneg (Z : Field) : 0 ≤ graphEnergy Z := by
  unfold graphEnergy
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => by unfold sizeSq; positivity)) (by norm_num)

theorem velocity_continuous (v : SpatialVertex) : Continuous (fun Z : Field => velocity Z v) := by
  unfold velocity
  split_ifs with hv
  · exact continuous_const
  · exact continuous_apply (⟨v,hv⟩ : RelFieldIndex)

theorem graphEnergy_continuous : Continuous graphEnergy := by
  have hg (e : SpatialEdge) : Continuous (fun Z : Field => gradient Z e) :=
    (velocity_continuous (shift e.1 e.2)).sub (velocity_continuous e.1)
  have hs (e : SpatialEdge) : Continuous (fun Z : Field => sizeSq (gradient Z e)) := by
    unfold sizeSq
    exact (((continuous_apply 0).comp (hg e)).pow 2 |>.add
      (((continuous_apply 1).comp (hg e)).pow 2)).add (((continuous_apply 2).comp (hg e)).pow 2)
  exact (continuous_finsetSum Finset.univ (fun e _ => hs e)).div_const 2


def coercivityRate : ℝ := 1/(126*4^10)

theorem coercivityRate_pos : 0 < coercivityRate := by norm_num [coercivityRate]

theorem graph_lower (Z : Field) : coercivityRate*fieldSizeSq Z ≤ graphEnergy Z := by
  have h := graph_coercive Z
  unfold coercivityRate
  norm_num at h ⊢
  linarith

theorem tripleGaussian_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun y : Triple => Real.exp (-b*sizeSq y)) := by
  have hi := Integrable.fintype_prod (fun _ : Fin 3 =>
    integrable_exp_neg_mul_sq (b := b) hb)
  rw [volume_pi]
  convert hi using 1
  funext y
  rw [← Real.exp_sum]
  congr 1
  simp [sizeSq,Fin.sum_univ_three]
  ring

theorem fieldGaussian_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun Z : Field => Real.exp (-b*fieldSizeSq Z)) := by
  have hi := Integrable.fintype_prod (fun _ : RelFieldIndex => tripleGaussian_integrable b hb)
  rw [volume_pi]
  convert hi using 1
  funext Z
  rw [← Real.exp_sum]
  congr 1
  simp only [fieldSizeSq,← Finset.mul_sum]

theorem graphGaussian_integrable : Integrable (fun Z : Field => Real.exp (-graphEnergy Z)) := by
  apply (fieldGaussian_integrable coercivityRate coercivityRate_pos).mono'
    (Real.continuous_exp.comp graphEnergy_continuous.neg).aestronglyMeasurable
  filter_upwards [] with Z
  change ‖Real.exp (-graphEnergy Z)‖ ≤ Real.exp (-coercivityRate*fieldSizeSq Z)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg (graph_lower Z))

def graphGaussianMass : ℝ := ∫ Z : Field,Real.exp (-graphEnergy Z)

theorem graphGaussianMass_pos : 0 < graphGaussianMass :=
  integral_exp_pos graphGaussian_integrable

theorem jointGaussian_integrable (a b : Velocities) :
    Integrable (fun x : SU2 × Field => gaussianIntegrand a b x.1*Real.exp (-graphEnergy x.2))
      (law.prod volume) :=
  ((gaussianIntegrand_memLp a b).integrable (by norm_num)).mul_prod graphGaussian_integrable

theorem jointGaussian_factor (a b : Velocities) :
    (∫ x : SU2 × Field,gaussianIntegrand a b x.1*Real.exp (-graphEnergy x.2) ∂law.prod volume)=
      gaussianKernel a b*graphGaussianMass := by
  exact integral_prod_mul (gaussianIntegrand a b) (fun Z : Field => Real.exp (-graphEnergy Z))


end OperatorDerivativeRewrite.Foundation.PeriodicRelativeGaugeGaussian
