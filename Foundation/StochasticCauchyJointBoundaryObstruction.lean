import Foundation.StochasticCauchyResolventExit
import Foundation.StochasticCauchyBoundaryConstraint
import Foundation.GaussianFirstChaosRecovery
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyJointBoundaryObstruction
open InfiniteGaussian ProductL2Curry StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyMalliavinBridge StochasticCauchyBoundaryConstraint
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  GaussianTimeHilbert.timeHilbert_secondCountable
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct

/-- Original source order: differentiated source inside, OTHER source outside. -/
theorem sourceCurry_actual (F : JointL2) :
    ∀ᵐ y ∂gaussianProduct,∀ᵐ x ∂gaussianProduct,sourceCurry F y x=F (x,y) := by
  rw [sourceCurry_apply]
  filter_upwards [curryEquiv_coeFn gaussianProduct gaussianProduct (swap gaussianProduct gaussianProduct F),
    ae_ae_of_ae_prod (swap_coeFn gaussianProduct gaussianProduct F)] with y hc hs
  filter_upwards [hc,hs] with x hc hs
  exact hc.trans hs

private theorem swap_ae (h : Sample → Prop) (hh : ∀ᵐ w ∂μ,h w) :
    ∀ᵐ w ∂μ,h (w.2,w.1) :=
  (measurePreserving_swap (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae hh

/-- Circle support and a ZERO derivative of the other component force this
component's scalar clock-weighted gradient energy to vanish. The reverse Fubini
step uses an explicitly MEASURABLE scalar predicate, not raw nested L2 values. -/
theorem partial_scalar_zero (F H : JointL2) (G : DerivativeField)
    (hF : (F,G) ∈ sourceDerivative.graph) (hH : (H,0) ∈ sourceDerivative.graph)
    (hc : ∀ᵐ w ∂μ,(F w)^2+(H w)^2=1)
    (τ : Sample → ℝ) (hτ : Measurable τ)
    (hn : ∀ᵐ y ∂gaussianProduct,∀ᵐ x ∂gaussianProduct,‖G y x‖^2=τ (x,y)) :
    ∀ᵐ w ∂μ,(F w)^2*τ w=0 := by
  have hcurry := ae_ae_of_ae_prod (swap_ae _ hc)
  have hscalar : ∀ᵐ y ∂gaussianProduct,∀ᵐ x ∂gaussianProduct,(F (x,y))^2*τ (x,y)=0 := by
    filter_upwards [(sourceDerivative_graph F G).mp hF,(sourceDerivative_graph H 0).mp hH,
      sourceCurry_actual F,sourceCurry_actual H,hcurry,hn,
      Lp.coeFn_zero GaussianVectorL2 2 gaussianProduct] with y hFg hH0 hFy hHy hc hn h0
    simp only [Pi.zero_apply] at h0
    rw [h0] at hH0
    have hcy : ∀ᵐ x ∂gaussianProduct,(sourceCurry F y x)^2+(sourceCurry H y x)^2=1 := by
      filter_upwards [hFy,hHy,hc] with x hf hh hc
      rw [hf,hh]
      exact hc
    have ht := circle_tangency (sourceCurry F y) (sourceCurry H y) (G y) 0 hFg hH0 hcy
    filter_upwards [ht,hFy,hn,Lp.coeFn_zero CoefficientSpace 2 gaussianProduct] with x ht hf hn hz
    simp only [Pi.zero_apply] at hz
    rw [hf,hz,smul_zero,add_zero] at ht
    rcases smul_eq_zero.mp ht with hf0|hg0
    · simp only [hf0,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul]
    · rw [hg0,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] at hn
      rw [← hn,mul_zero]
  have hm : Measurable (fun w : Sample => (F (w.2,w.1))^2*τ (w.2,w.1)) :=
    (((Lp.stronglyMeasurable F).measurable.comp measurable_swap).pow_const 2).mul (hτ.comp measurable_swap)
  have hp : ∀ᵐ w ∂μ,(F (w.2,w.1))^2*τ (w.2,w.1)=0 :=
    (ae_prod_iff_ae_ae (measurableSet_eq_fun hm measurable_const)).mpr hscalar
  exact swap_ae _ hp

/-- A sparse flat two-source gradient template on the ORIGINAL four partial
graphs forces its actual clock to vanish. Distinct kernel directions are allowed;
only their shared Brownian norm-clock law is required. -/
theorem sparse_clock_zero (F H : JointL2) (GX KY : DerivativeField)
    (hFX : (F,GX) ∈ sourceDerivative.graph) (hHX : (H,0) ∈ sourceDerivative.graph)
    (hFY : (swap gaussianProduct gaussianProduct F,0) ∈ sourceDerivative.graph)
    (hHY : (swap gaussianProduct gaussianProduct H,KY) ∈ sourceDerivative.graph)
    (hc : ∀ᵐ w ∂μ,(F w)^2+(H w)^2=1)
    (τ : Sample → ℝ) (hτ : Measurable τ)
    (hNX : ∀ᵐ y ∂gaussianProduct,∀ᵐ x ∂gaussianProduct,‖GX y x‖^2=τ (x,y))
    (hNY : ∀ᵐ x ∂gaussianProduct,∀ᵐ y ∂gaussianProduct,‖KY x y‖^2=τ (x,y)) :
    τ =ᵐ[μ] fun _ => 0 := by
  have hX := partial_scalar_zero F H GX hFX hHX hc τ hτ hNX
  have hcs : ∀ᵐ w ∂μ,(swap gaussianProduct gaussianProduct H w)^2+
      (swap gaussianProduct gaussianProduct F w)^2=1 := by
    filter_upwards [swap_coeFn gaussianProduct gaussianProduct H,swap_coeFn gaussianProduct gaussianProduct F,
      swap_ae _ hc] with w hh hf hc
    rw [hh,hf]
    linarith
  have hY' := partial_scalar_zero (swap gaussianProduct gaussianProduct H) (swap gaussianProduct gaussianProduct F)
    KY hHY hFY hcs (fun w => τ (w.2,w.1)) (hτ.comp measurable_swap) hNY
  have hYs : ∀ᵐ w ∂μ,(H (w.2,w.1))^2*τ (w.2,w.1)=0 := by
    filter_upwards [hY',swap_coeFn gaussianProduct gaussianProduct H] with w hh hs
    simpa only [hs] using hh
  have hY := swap_ae _ hYs
  filter_upwards [hX,hY,hc] with w hx hy hc
  have he := congrArg (fun t : ℝ => t*τ w) hc
  simp only [add_mul,one_mul,hx,hy,zero_add] at he
  exact he.symm

/-- REAL coordinate of the ACTUAL continuous two-source unit-circle exit. -/
def exitReal : JointL2 := ComplexL2Isometry.realPart μ
  (StochasticCauchyExitOccupation.exitClass 1 (by norm_num))

/-- IMAGINARY coordinate on the SAME original physical source order. -/
def exitImag : JointL2 := ComplexL2Isometry.imagPart μ
  (StochasticCauchyExitOccupation.exitClass 1 (by norm_num))

theorem exit_circle : ∀ᵐ w ∂μ,(exitReal w)^2+(exitImag w)^2=1 := by
  let F := StochasticCauchyExitOccupation.exitClass 1 (by norm_num)
  filter_upwards [Complex.reCLM.coeFn_compLpL F,Complex.imCLM.coeFn_compLpL F,
    StochasticCauchyExitOccupation.exitClass_actual 1 (by norm_num),
    StochasticCauchyExitOccupation.exitValue_boundary 1 (by norm_num)] with w hr hi hf hb
  change exitReal w=(F w).re at hr
  change exitImag w=(F w).im at hi
  rw [hr,hi,hf]
  have hn := congrArg (fun t : ℝ => t^2) hb
  rw [Complex.sq_norm,Complex.normSq_apply] at hn
  nlinarith

/-- The source's sparse flat random-clock template cannot hold on the actual
unit-disk exit and ORIGINAL two-source partial derivative graphs. This does not
assert nonmembership if different, nonflat derivatives exist. -/
theorem actual_unit_exit_no_flat : ¬ ∃ GX KY : DerivativeField,
    (exitReal,GX) ∈ sourceDerivative.graph ∧ (exitImag,0) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct exitReal,0) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct exitImag,KY) ∈ sourceDerivative.graph ∧
    (∀ᵐ y ∂gaussianProduct,∀ᵐ x ∂gaussianProduct,‖GX y x‖^2=StochasticCauchyExitOccupation.realDuration 1 (x,y)) ∧
    (∀ᵐ x ∂gaussianProduct,∀ᵐ y ∂gaussianProduct,‖KY x y‖^2=StochasticCauchyExitOccupation.realDuration 1 (x,y)) := by
  rintro ⟨GX,KY,hFX,hHX,hFY,hHY,hNX,hNY⟩
  have hm : Measurable (StochasticCauchyExitOccupation.realDuration 1) := by
    exact ENNReal.measurable_toReal.comp (StochasticCauchyExitClock.exitTime_stopping 1).measurable'
  have hz := sparse_clock_zero exitReal exitImag GX KY hFX hHX hFY hHY exit_circle
    (StochasticCauchyExitOccupation.realDuration 1) hm hNX hNY
  have hi : (∫ w,StochasticCauchyExitOccupation.realDuration 1 w ∂μ)=0 := by
    rw [integral_congr_ae hz,integral_zero]
  have he := StochasticCauchyExitOccupation.expected_exit_time 1 (by norm_num)
  norm_num at he
  linarith

/-- The ACTUAL time direction used by the original GaussianTimeProcess,
not a substituted direction from the older paired-Hilbert realization. -/
def timeKernel (t : ℝ≥0) : CoefficientSpace :=
  SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert (GaussianTimeHilbert.timeVector t)

theorem timeKernel_norm_sq (t : ℝ≥0) : ‖timeKernel t‖^2=(t:ℝ) := by
  rw [timeKernel,(SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert).norm_map,
    GaussianTimeHilbert.timeVector_norm_sq]

/-- Fixed-time template REALLY IS valid on the original full Gaussian graph.
The actual-exit theorem below rejects the unproved random-time substitution. -/
theorem fixed_time_kernel_graph (t : ℝ≥0) :
    (GaussianTimeProcess.wienerL2 t,scalarTensor (timeKernel t) gaussianOne) ∈ closedCylindricalDerivative.graph :=
  GaussianFirstChaosRecovery.firstChaos_derivative_graph (timeKernel t)

private theorem duration_actual : ∀ᵐ w ∂μ,
    StochasticCauchyExitOccupation.realDuration 1 w=(StochasticCauchyExitOccupation.finiteExit 1 w:ℝ) := by
  filter_upwards [StochasticCauchyExitOccupation.finiteExit_actual 1 (by norm_num)] with w hw
  have he : StochasticCauchyExitOccupation.exitDuration 1 w=
      (StochasticCauchyExitOccupation.finiteExit 1 w:ℝ≥0∞) := hw.symm
  simpa only [StochasticCauchyExitOccupation.realDuration,ENNReal.coe_toReal] using congrArg ENNReal.toReal he

/-- No original four-partial-graph realization of the source's ACTUAL Brownian
time-kernel template exists at the genuine unit-disk exit. -/
theorem actual_unit_exit_no_kernel : ¬ ∃ GX KY : DerivativeField,
    (exitReal,GX) ∈ sourceDerivative.graph ∧ (exitImag,0) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct exitReal,0) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct exitImag,KY) ∈ sourceDerivative.graph ∧
    (∀ᵐ y ∂gaussianProduct,∀ᵐ x ∂gaussianProduct,GX y x=timeKernel (StochasticCauchyExitOccupation.finiteExit 1 (x,y))) ∧
    (∀ᵐ x ∂gaussianProduct,∀ᵐ y ∂gaussianProduct,KY x y=timeKernel (StochasticCauchyExitOccupation.finiteExit 1 (x,y))) := by
  rintro ⟨GX,KY,hFX,hHX,hFY,hHY,hGX,hKY⟩
  apply actual_unit_exit_no_flat
  refine ⟨GX,KY,hFX,hHX,hFY,hHY,?_,?_⟩
  · filter_upwards [hGX,ae_ae_of_ae_prod (swap_ae _ duration_actual)] with y hx ht
    filter_upwards [hx,ht] with x hx ht
    rw [hx,timeKernel_norm_sq,← ht]
  · filter_upwards [hKY,ae_ae_of_ae_prod duration_actual] with x hy ht
    filter_upwards [hy,ht] with y hy ht
    rw [hy,timeKernel_norm_sq,← ht]

end OperatorDerivativeRewrite.Foundation.StochasticCauchyJointBoundaryObstruction
