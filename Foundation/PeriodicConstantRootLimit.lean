import Foundation.PeriodicConstantQuarticJet
import Foundation.SU2RootEuclideanMeasure
/-! Actual common-root Wilson-ray Gaussian limit, including squared L2
convergence on the root Haar probability space. The chart/adjoint bridge is
exact and uses one shared root. This is not the full64-vertex Haar kernel.
A strict actual-kernel counterexample and nonconvergence theorem show why
unrescaled substitution of the root model for that full kernel fails.
No native ground-normalized spectral or continuum conclusion is asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped Quaternion Matrix Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicConstantRootLimit
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart SU2HemisphereJets
open SU2RootAdjoint SU2RootEuclideanMeasure PeriodicConstantQuarticJet PeriodicTemporalSlab PeriodicWilsonSlab
attribute [local irreducible] SU2RootAdjoint.rotate sizeSq halfAction spatialAction temporalAction

theorem radius_rotate (c : SU2) (u : Triple) : radius (rotate c u)=radius u := by
  apply (sq_eq_sq₀ (radius_positive _).le (radius_positive _).le).mp
  rw [radius_square,radius_square,rotate_sizeSq]

theorem chart_conjugates (c : SU2) (u : Triple) :
    c*hemisphereChart u*c⁻¹=hemisphereChart (rotate c u) := by
  apply Subtype.ext
  change (c : SU2TraceHessianModel.M2)*(hemisphereChart u : SU2TraceHessianModel.M2)*
    (c : SU2TraceHessianModel.M2)ᴴ=(hemisphereChart (rotate c u) : SU2TraceHessianModel.M2)
  rw [chart_matrix,chart_matrix,rawPoint_matrix,rawPoint_matrix,radius_rotate,generator_rotate]
  unfold CubeMixedForm.adjointVelocity
  rw [mul_smul_comm,smul_mul_assoc]
  congr 1
  have hc : (c : SU2TraceHessianModel.M2)*(c : SU2TraceHessianModel.M2)ᴴ=1 := by
    change ((c*c⁻¹ : SU2) : SU2TraceHessianModel.M2)=1
    simp
  rw [mul_add,add_mul,mul_one,hc]

def rotated (c : SU2) (a : Velocities) : Velocities := fun i => rotate c (a i)
def constantGauge (c : SU2) : Gauge := fun _ => c

theorem constant_state_gauge (c : SU2) (a : Velocities) (t : ℝ) :
    PeriodicSlabGauge.gaugeAction (constantGauge c) (constantState a t)=constantState (rotated c a) t := by
  funext e
  change c*hemisphereChart (t • a e.2)*c⁻¹=hemisphereChart (t • rotate c (a e.2))
  rw [chart_conjugates,rotate_smul]

theorem rooted_temporal_exact (a b : Velocities) (c : SU2) (t : ℝ) :
    temporalAction (constantState a t) (constantState b t) (constantGauge c)=
      temporalAction (constantState a t) (constantState (rotated c b) t) 1 := by
  rw [← constant_state_gauge]
  unfold temporalAction
  apply Finset.sum_congr rfl
  intro e _
  rw [PeriodicSlabGauge.temporal_right_word]
  simp only [one_mul]

theorem rooted_halfAction_exact (a b : Velocities) (c : SU2) (t : ℝ) :
    halfAction (constantState a t) (constantState b t) (constantGauge c)=
      halfAction (constantState a t) (constantState (rotated c b) t) 1 := by
  have hs : spatialAction (constantState (rotated c b) t)=spatialAction (constantState b t) := by
    rw [← constant_state_gauge,PeriodicSlabGauge.spatial_action_invariant]
  unfold halfAction
  rw [rooted_temporal_exact,hs]

def rootEnergy (a b : Velocities) (c : SU2) : ℝ := 32*∑ i : Fin 3,sizeSq (a i-rotate c (b i))

theorem rootEnergy_nonnegative (a b : Velocities) (c : SU2) : 0≤rootEnergy a b c := by
  unfold rootEnergy
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => sizeSq_nonneg _))

theorem rootEnergy_continuous (a b : Velocities) : Continuous (rootEnergy a b) := by
  have hs : Continuous (sizeSq : Triple → ℝ) := by unfold sizeSq; fun_prop
  have hsum : Continuous (fun c : SU2 => ∑ i : Fin 3,sizeSq (a i-rotate c (b i))) := by
    apply continuous_finset_sum
    intro i _
    have hr : Continuous (fun c : SU2 => rotate c (b i)) :=
      rotate_joint_continuous.comp (continuous_id.prodMk continuous_const)
    exact hs.comp (continuous_const.sub hr)
  exact hsum.const_mul 32

theorem rooted_quadratic_limit (a b : Velocities) (c : SU2) :
    Tendsto (fun t : ℝ => halfAction (constantState a t) (constantState b t) (constantGauge c)/t^2)
      (𝓝[≠] 0) (𝓝 (rootEnergy a b c)) := by
  simp_rw [rooted_halfAction_exact]
  simpa only [rootEnergy,rotated] using halfAction_identity_quadratic_limit a (rotated c b)

def rootIntegrand (a b : Velocities) (t : ℝ) (c : SU2) : ℝ :=
  PeriodicWilsonSlab.weight (1/t^2) (constantState a t) (constantState b t) (constantGauge c)

def gaussianIntegrand (a b : Velocities) (c : SU2) : ℝ := Real.exp (-rootEnergy a b c)

theorem rootIntegrand_measurable (a b : Velocities) (t : ℝ) : Measurable (rootIntegrand a b t) := by
  have hg : Measurable (constantGauge : SU2 → Gauge) := by
    unfold constantGauge
    exact measurable_pi_iff.mpr (fun _ => measurable_id)
  have hc : Measurable (fun c : SU2 => ((constantState a t,constantState b t),constantGauge c)) :=
    measurable_const.prodMk hg
  exact (weight_joint_measurable (1/t^2)).comp hc

theorem rootIntegrand_bound (a b : Velocities) (t : ℝ) (c : SU2) : |rootIntegrand a b t c|≤1 := by
  unfold rootIntegrand PeriodicWilsonSlab.weight
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have hβ : 0≤1/t^2 := one_div_nonneg.mpr (sq_nonneg t)
  have hA := (half_action_bounds (constantState a t) (constantState b t) (constantGauge c)).1
  simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hβ hA)

theorem rootIntegrand_tendsto (a b : Velocities) (c : SU2) :
    Tendsto (fun t : ℝ => rootIntegrand a b t c) (𝓝[≠] 0) (𝓝 (gaussianIntegrand a b c)) := by
  unfold gaussianIntegrand
  have h := (Real.continuous_exp.tendsto (-rootEnergy a b c)).comp (rooted_quadratic_limit a b c).neg
  convert h using 1
  funext t
  unfold rootIntegrand PeriodicWilsonSlab.weight
  congr 1
  ring

def rootKernel (a b : Velocities) (t : ℝ) : ℝ := ∫ c,rootIntegrand a b t c ∂law
def gaussianKernel (a b : Velocities) : ℝ := ∫ c,gaussianIntegrand a b c ∂law

/-- A genuine common-root Haar-integrated limit. This is NOT the full
64-vertex temporal Gauge Haar integral or a ground-normalized operator limit. -/
theorem rootKernel_tendsto (a b : Velocities) :
    Tendsto (rootKernel a b) (𝓝[≠] 0) (𝓝 (gaussianKernel a b)) := by
  unfold rootKernel gaussianKernel
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : SU2 => (1:ℝ))
  · exact Filter.Eventually.of_forall (fun t => (rootIntegrand_measurable a b t).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun t => ae_of_all _ (rootIntegrand_bound a b t))
  · exact integrable_const 1
  · exact ae_of_all _ (rootIntegrand_tendsto a b)


theorem gaussianIntegrand_measurable (a b : Velocities) : Measurable (gaussianIntegrand a b) :=
  (Real.continuous_exp.comp (rootEnergy_continuous a b).neg).measurable

theorem gaussianIntegrand_bound (a b : Velocities) (c : SU2) : |gaussianIntegrand a b c|≤1 := by
  unfold gaussianIntegrand
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (rootEnergy_nonnegative a b c))

theorem rootIntegrand_memLp (a b : Velocities) (t : ℝ) : MemLp (rootIntegrand a b t) 2 law :=
  MemLp.of_bound (rootIntegrand_measurable a b t).aestronglyMeasurable 1
    (ae_of_all _ (fun c => by simpa only [Real.norm_eq_abs] using rootIntegrand_bound a b t c))

theorem gaussianIntegrand_memLp (a b : Velocities) : MemLp (gaussianIntegrand a b) 2 law :=
  MemLp.of_bound (gaussianIntegrand_measurable a b).aestronglyMeasurable 1
    (ae_of_all _ (fun c => by simpa only [Real.norm_eq_abs] using gaussianIntegrand_bound a b c))

/-- Squared L2 convergence on the actual COMMON-ROOT Haar probability space,
not on the Wilson boundary or all temporal vertex gauges. -/
theorem root_integral_sq_error_tendsto (a b : Velocities) :
    Tendsto (fun t : ℝ => ∫ c,(rootIntegrand a b t c-gaussianIntegrand a b c)^2 ∂law)
      (𝓝[≠] 0) (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => ∫ c,(rootIntegrand a b t c-gaussianIntegrand a b c)^2 ∂law)
      (𝓝[≠] 0) (𝓝 (∫ _ : SU2,(0:ℝ) ∂law)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : SU2 => (4:ℝ))
    · exact Filter.Eventually.of_forall (fun t =>
        (((rootIntegrand_measurable a b t).aestronglyMeasurable.sub
          (gaussianIntegrand_measurable a b).aestronglyMeasurable).pow 2))
    · apply Filter.Eventually.of_forall
      intro t
      apply ae_of_all
      intro c
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hf := rootIntegrand_bound a b t c
      have hg := gaussianIntegrand_bound a b c
      have hsub := (abs_sub (rootIntegrand a b t c) (gaussianIntegrand a b c)).trans
        (show |rootIntegrand a b t c|+|gaussianIntegrand a b c|≤2 by linarith)
      have hp := pow_le_pow_left₀ (abs_nonneg _) hsub 2
      simpa only [sq_abs,show (2:ℝ)^2=4 by norm_num] using hp
    · exact integrable_const 4
    · exact ae_of_all _ (fun c => by
        have hp := ((rootIntegrand_tendsto a b c).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => gaussianIntegrand a b c) (𝓝[≠] 0)
            (𝓝 (gaussianIntegrand a b c)))).pow 2
        simpa only [sub_self,zero_pow (by decide : (2:ℕ)≠0)] using hp)
  simpa only [integral_zero] using h



/-- The full temporal vertex-Haar kernel is strictly below1 even at identity
boundaries and positive coupling. A common constant gauge has cost0 there;
therefore the root-only integral is NOT the full temporal Haar integral. -/
theorem full_kernel_identity_lt_one (β : ℝ) (hβ : 0<β) :
    PeriodicWilsonSlab.kernel β (1 : State) 1<1 := by
  classical
  letI : gaugeHaar.IsOpenPosMeasure := by unfold gaugeHaar; infer_instance
  let origin : SpatialVertex := fun _ => 0
  let q : Gauge := fun v => if v=origin then SU2StapleExtremes.minusOne else 1
  have hv : shift origin 0≠origin := by decide
  have hroot : q origin=SU2StapleExtremes.minusOne := by simp [q]
  have hshift : q (shift origin 0)=1 := by simp [q,hv]
  have hn : temporalAction (1 : State) 1 q≠0 := by
    intro hz
    have he := congrFun ((PeriodicTemporalConcentration.temporal_zero_iff_alignment (1 : State) 1 q).mp hz) (origin,0)
    change (1 : SU2)=q origin*1*(q (shift origin 0))⁻¹ at he
    simp only [hroot,hshift,mul_one,inv_one] at he
    have hh := congrArg halfTrace he
    norm_num [SU2StapleExtremes.minusOne,halfTrace,hom,QuaternionSU2Representation.repr,
      SU2TraceHessianModel.traceReal,Matrix.trace_fin_two] at hh
  have hT : 0<temporalAction (1 : State) 1 q :=
    lt_of_le_of_ne (temporal_action_bounds (1 : State) 1 q).1 hn.symm
  have hA : 0<halfAction (1 : State) 1 q := by
    unfold halfAction
    linarith [(spatial_action_bounds (1 : State)).1]
  have hm : Continuous (fun g : Gauge => (((1 : State),(1 : State)),g)) :=
    continuous_const.prodMk continuous_id
  have ha : Continuous (fun g : Gauge => halfAction (1 : State) 1 g) :=
    PeriodicLowActionBlock.action_continuous.comp hm
  have hw : Continuous (fun g : Gauge => PeriodicWilsonSlab.weight β (1 : State) 1 g) := by
    change Continuous (fun g : Gauge => Real.exp ((-β)*halfAction (1 : State) 1 g))
    exact Real.continuous_exp.comp (continuous_const.mul ha)
  have hf : Continuous (fun g : Gauge => 1-PeriodicWilsonSlab.weight β (1 : State) 1 g) :=
    continuous_const.sub hw
  have hnonneg : ∀ g : Gauge,0≤1-PeriodicWilsonSlab.weight β (1 : State) 1 g := by
    intro g
    apply sub_nonneg.mpr
    unfold PeriodicWilsonSlab.weight
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) (half_action_bounds (1 : State) 1 g).1
  have hpoint : 1-PeriodicWilsonSlab.weight β (1 : State) 1 q≠0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    unfold PeriodicWilsonSlab.weight
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hβ) hA)
  have hp := hf.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := gaugeHaar)
    (HasCompactSupport.of_compactSpace _) hnonneg hpoint
  have hi := hw.integrable_of_hasCompactSupport (μ := gaugeHaar) (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (integrable_const 1) hi] at hp
  have hconst : (∫ _ : Gauge,(1:ℝ) ∂gaugeHaar)=1 := by simp
  rw [hconst] at hp
  change 0<1-PeriodicWilsonSlab.kernel β (1 : State) 1 at hp
  linarith



theorem constantState_zero (t : ℝ) : constantState (0 : Velocities) t=(1 : State) := by
  funext e
  change hemisphereChart (t • (0 : Triple))=1
  rw [smul_zero,CubeChartAction.chart_zero]

theorem rootIntegrand_zero (t : ℝ) (c : SU2) : rootIntegrand 0 0 t c=1 := by
  unfold rootIntegrand
  rw [constantState_zero]
  have hs : spatialAction (1 : State)=0 := by
    unfold spatialAction spatialWord
    simp [SU2OpenLinkGaugeObstruction.halfTrace_one]
  have hT : temporalAction (1 : State) 1 (constantGauge c)=0 := by
    unfold temporalAction temporalWord constantGauge
    simp [SU2OpenLinkGaugeObstruction.halfTrace_one]
  unfold PeriodicWilsonSlab.weight halfAction
  rw [hs,hT]
  norm_num

theorem rootKernel_zero (t : ℝ) : rootKernel 0 0 t=1 := by
  unfold rootKernel
  simp_rw [rootIntegrand_zero]
  simp

theorem full_kernel_identity_le_fixed (β : ℝ) (hβ : 1≤β) :
    PeriodicWilsonSlab.kernel β (1 : State) 1≤PeriodicWilsonSlab.kernel 1 1 1 := by
  unfold PeriodicWilsonSlab.kernel
  apply integral_mono (weight_integrable β 1 1) (weight_integrable 1 1 1)
  intro g
  unfold PeriodicWilsonSlab.weight
  apply Real.exp_le_exp.mpr
  have hA := (half_action_bounds (1 : State) 1 g).1
  nlinarith

/-- Even unrescaled pointwise convergence of the FULL vertex-Haar kernel to
the common-root model fails at identity boundaries. This does not rule out
a correctly renormalized transverse/common-root asymptotic theorem. -/
theorem full_kernel_not_unrescaled_root_limit :
    ¬Tendsto (fun t : ℝ => PeriodicWilsonSlab.kernel (1/t^2) (1 : State) 1)
      (𝓝[≠] 0) (𝓝 1) := by
  intro h
  have hs : ∀ᶠ t : ℝ in 𝓝 0,t∈Set.Ioo (-1:ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hb : ∀ᶠ t : ℝ in 𝓝[≠] 0,PeriodicWilsonSlab.kernel (1/t^2) (1 : State) 1≤
      PeriodicWilsonSlab.kernel 1 1 1 := by
    filter_upwards [hs.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t hs ht
    change t≠0 at ht
    apply full_kernel_identity_le_fixed
    apply (le_div_iff₀ (sq_pos_of_ne_zero ht)).mpr
    nlinarith [mul_pos (show 0<1-t by linarith [hs.2]) (show 0<1+t by linarith [hs.1])]
  have hl := le_of_tendsto h hb
  have hu := full_kernel_identity_lt_one 1 (by norm_num)
  linarith



theorem rootKernel_pos (a b : Velocities) (t : ℝ) : 0<rootKernel a b t := by
  exact integral_exp_pos ((rootIntegrand_memLp a b t).integrable (by norm_num))

theorem rootKernel_le_one (a b : Velocities) (t : ℝ) : rootKernel a b t≤1 := by
  unfold rootKernel
  have h := integral_mono ((rootIntegrand_memLp a b t).integrable (by norm_num)) (integrable_const (1:ℝ))
    (fun c => (le_abs_self _).trans (rootIntegrand_bound a b t c))
  simpa only [integral_const,probReal_univ,one_smul] using h

theorem gaussianKernel_pos (a b : Velocities) : 0<gaussianKernel a b := by
  exact integral_exp_pos ((gaussianIntegrand_memLp a b).integrable (by norm_num))

theorem gaussianKernel_le_one (a b : Velocities) : gaussianKernel a b≤1 := by
  unfold gaussianKernel
  have h := integral_mono ((gaussianIntegrand_memLp a b).integrable (by norm_num)) (integrable_const (1:ℝ))
    (fun c => (le_abs_self _).trans (gaussianIntegrand_bound a b c))
  simpa only [integral_const,probReal_univ,one_smul] using h


end OperatorDerivativeRewrite.Foundation.PeriodicConstantRootLimit
