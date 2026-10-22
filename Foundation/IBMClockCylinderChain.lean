import Foundation.IBMClockWeakChain

/-! Actual multitime Fourier-type cylinders have nonlinear clock-chain limits.
No ordinary derivative of the positive-time IBM point is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockCylinderChain
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMClockGraphDualLimit ClosedOperatorGraphDualDerivative
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
variable {N : ℕ}

def value (a : Fin N → ℝ) (t : Fin N → ℝ≥0) : JointL2 :=
  ∑ i, a i • jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i))

def mollified (a : Fin N → ℝ) (t : Fin N → ℝ≥0) (n : ℕ) : JointL2 :=
  ∑ i, a i • jointRealization (IBMRandomTimeHilbert.randomMollifiedL2 n (t i))

def gradient (a : Fin N → ℝ) (t : Fin N → ℝ≥0) (n : ℕ) : FieldSpace :=
  ∑ i, a i • IBMFirstSourceClockGraph.clockGradient n (t i)

def actualValue (a : Fin N → ℝ) (t : Fin N → ℝ≥0)
    (ω : IBMSourceLaws.JointSample) : ℝ :=
  ∑ i, a i * IBMConstructedSources.ibmValue (t i) ω

theorem value_intrinsic (a : Fin N → ℝ) (t : Fin N → ℝ≥0) : value a t ∈ IntrinsicSpace := by
  apply IntrinsicSpace.sum_mem
  intro i hi
  exact IntrinsicSpace.smul_mem (a i) (joint_point_intrinsic (t i))

theorem nonlinear_value_intrinsic (φ : IBMClockWeakChain.TestFunction)
    (a : Fin N → ℝ) (t : Fin N → ℝ≥0) : IBMClockWeakChain.value φ (value a t) ∈ IntrinsicSpace :=
  IBMIntrinsicChainRule.composition_observable ⟨value a t, value_intrinsic a t⟩ _ _
    (IBMClockWeakChain.continuous_value φ) (IBMClockWeakChain.value_ae φ _)

theorem value_actual_ae (a : Fin N → ℝ) (t : Fin N → ℝ≥0) :
    value a t =ᵐ[IBMSourceLaws.jointMeasure] actualValue a t := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i =>
      a i • jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i))),
    ae_all_iff.mpr (fun i => joint_point_actual_ae (t i)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i)
      (jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i))))] with ω hs ha hm
  change (∑ i, a i • jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i))) ω = _
  rw [hs]
  simp only [actualValue, hm, Pi.smul_apply, smul_eq_mul, ha]

theorem mollified_graph (a : Fin N → ℝ) (t : Fin N → ℝ≥0) (ht : ∀ i, 0 < t i)
    (n : ℕ) : (clockUnitary (mollified a t n), gradient a t n) ∈ Clock.graph := by
  unfold mollified gradient
  rw [map_sum]
  simp_rw [map_smul]
  rw [prod_mk_sum]
  apply Clock.graph.sum_mem
  intro i hi
  have hg := Clock.graph.smul_mem (a i)
    (IBMFirstSourceClockGraph.mollified_clock_graph n (t i) (ht i))
  exact hg

theorem mollified_error (a : Fin N → ℝ) (t : Fin N → ℝ≥0) (n : ℕ) :
    ‖mollified a t n - value a t‖ ≤
      ∑ i, |a i| * Real.sqrt (IBMMollifier.bump n).rOut := by
  unfold mollified value
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [← smul_sub, norm_smul, ← map_sub, jointRealization.norm_map, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (IBMRandomTimeHilbert.randomMollifiedL2_error_le n (t i)) (abs_nonneg _)

theorem mollified_tendsto (a : Fin N → ℝ) (t : Fin N → ℝ≥0) :
    Tendsto (mollified a t) atTop (𝓝 (value a t)) := by
  apply tendsto_finsetSum
  intro i hi
  exact (jointRealization.continuous.tendsto _ |>.comp
    (IBMRandomTimeHilbert.randomMollifiedL2_tendsto (t i))).const_smul (a i)

def chainGradient (φ : IBMClockWeakChain.TestFunction)
    (a : Fin N → ℝ) (t : Fin N → ℝ≥0) (n : ℕ) : FieldSpace :=
  IBMClockWeakChain.chainField φ (mollified a t n) (gradient a t n)

def weakDerivative (φ : IBMClockWeakChain.TestFunction)
    (a : Fin N → ℝ) (t : Fin N → ℝ≥0) : StrongDual ℝ (Tests Clock clock_dense) :=
  IBMClockWeakChain.weakDerivative φ (value a t)

theorem weakDerivative_time_continuous (φ : IBMClockWeakChain.TestFunction)
    (a : Fin N → ℝ) : Continuous (weakDerivative φ a) := by
  have hv : Continuous (fun t : Fin N → ℝ≥0 => value a t) := by
    unfold value
    apply continuous_finsetSum
    intro i hi
    exact (continuous_const : Continuous (fun _ : Fin N → ℝ≥0 => a i)).smul
      (jointRealization.continuous.comp
      (source_time_continuous.comp (show Continuous (fun t : Fin N → ℝ≥0 => t i) from
        continuous_apply i)))
  exact (IBMClockWeakChain.weakDerivative_continuous φ).comp hv

theorem chainGradient_actual_ae (φ : IBMClockWeakChain.TestFunction)
    (a : Fin N → ℝ) (t : Fin N → ℝ≥0) (n : ℕ) :
    IBMIntrinsicChainRule.uncurryField (chainGradient φ a t n)
      =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ.slope (mollified a t n ω) •
        IBMIntrinsicChainRule.uncurryField (gradient a t n) ω := by
  have he : IBMIntrinsicChainRule.uncurryField (chainGradient φ a t n) =
      IBMClockWeakChain.slopeField φ (mollified a t n)
        (IBMIntrinsicChainRule.uncurryField (gradient a t n)) :=
    (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm_apply_apply _
  rw [he]
  exact IBMClockWeakChain.slopeField_ae _ _ _

theorem chain_radius_error (φ : IBMClockWeakChain.TestFunction)
    (a : Fin N → ℝ) (t : Fin N → ℝ≥0) (ht : ∀ i, 0 < t i) (n : ℕ) :
    ‖embed Clock clock_dense (chainGradient φ a t n) - weakDerivative φ a t‖ ≤
      φ.slopeBound * ∑ i, |a i| * Real.sqrt (IBMMollifier.bump n).rOut :=
  (IBMClockWeakChain.chain_dual_error φ _ _ _ (mollified_graph a t ht n)).trans
    (mul_le_mul_of_nonneg_left (mollified_error a t n) (IBMClockWeakChain.slopeBound_nonneg φ))

theorem chain_strong_limit (φ : IBMClockWeakChain.TestFunction)
    (a : Fin N → ℝ) (t : Fin N → ℝ≥0) (ht : ∀ i, 0 < t i) :
    Tendsto (fun n => embed Clock clock_dense (chainGradient φ a t n)) atTop
      (𝓝 (weakDerivative φ a t)) :=
  IBMClockWeakChain.chain_dual_limit φ _ _ (mollified_graph a t ht) _ (mollified_tendsto a t)

theorem actual_pairing (φ : IBMClockWeakChain.TestFunction)
    (a : Fin N → ℝ) (t : Fin N → ℝ≥0) (v : Clock.adjoint.domain) :
    weakDerivative φ a t (testOf Clock clock_dense v) =
      ∫ ω, φ.value (actualValue a t ω) * (clockUnitary.symm (Clock.adjoint v)) ω
        ∂IBMSourceLaws.jointMeasure :=
  IBMClockWeakChain.actual_pairing φ _ _ (value_actual_ae a t) v

theorem actual_pairing_integrable (φ : IBMClockWeakChain.TestFunction)
    (a : Fin N → ℝ) (t : Fin N → ℝ≥0) (v : Clock.adjoint.domain) :
    Integrable (fun ω => φ.value (actualValue a t ω) *
      (clockUnitary.symm (Clock.adjoint v)) ω) IBMSourceLaws.jointMeasure :=
  IBMClockWeakChain.actual_pairing_integrable φ _ _ (value_actual_ae a t) v

end OperatorDerivativeRewrite.Foundation.IBMClockCylinderChain
