import Foundation.IBMClockGraphDualLimit
import Foundation.GaussianClosedChainRule
import Foundation.IBMIntrinsicChainRule

/-! Nonlinear clock chain limits in the FULL original adjoint graph dual.
Products are formed only at genuine L² graph approximants, never by multiplying
the limiting distribution by a pointwise random coefficient. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockWeakChain
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMClockGraphDualLimit ClosedOperatorGraphDualDerivative
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

structure TestFunction where
  value : ℝ → ℝ
  slope : ℝ → ℝ
  valueBound : ℝ
  slopeBound : ℝ
  hasDeriv : ∀ x, HasDerivAt value (slope x) x
  continuous_slope : Continuous slope
  value_le : ∀ x, ‖value x‖ ≤ valueBound
  slope_le : ∀ x, ‖slope x‖ ≤ slopeBound

theorem continuous_value (φ : TestFunction) : Continuous φ.value :=
  continuous_iff_continuousAt.mpr fun x => (φ.hasDeriv x).continuousAt

theorem slopeBound_nonneg (φ : TestFunction) : 0 ≤ φ.slopeBound :=
  (norm_nonneg (φ.slope 0)).trans (φ.slope_le 0)

theorem value_lipschitz (φ : TestFunction) :
    LipschitzWith ⟨φ.slopeBound, slopeBound_nonneg φ⟩ φ.value :=
  lipschitzWith_of_nnnorm_deriv_le (fun x => (φ.hasDeriv x).differentiableAt)
    (fun x => by
      change ‖deriv φ.value x‖ ≤ φ.slopeBound
      rw [(φ.hasDeriv x).deriv]
      exact φ.slope_le x)

def value (φ : TestFunction) (f : JointL2) : JointL2 :=
  (MemLp.of_bound ((continuous_value φ).comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable f)) φ.valueBound
    (ae_of_all _ fun ω => φ.value_le (f ω))).toLp _

theorem value_ae (φ : TestFunction) (f : JointL2) :
    value φ f =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ.value (f ω) :=
  MemLp.coeFn_toLp _

def slopeField (φ : TestFunction) (f : JointL2)
    (g : IBMIntrinsicChainRule.JointVectorL2) : IBMIntrinsicChainRule.JointVectorL2 :=
  (smul_memLp (p := ∞) (q := 2) (r := 2)
    (MemLp.of_bound (φ.continuous_slope.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f)) φ.slopeBound
      (ae_of_all _ fun ω => φ.slope_le (f ω))) (Lp.memLp g)).toLp _

theorem slopeField_ae (φ : TestFunction) (f : JointL2)
    (g : IBMIntrinsicChainRule.JointVectorL2) :
    slopeField φ f g =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => φ.slope (f ω) • g ω := MemLp.coeFn_toLp _

def chainField (φ : TestFunction) (f : JointL2) (V : FieldSpace) : FieldSpace :=
  ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
    (slopeField φ f (IBMIntrinsicChainRule.uncurryField V))

def weakDerivative (φ : TestFunction) (f : JointL2) : StrongDual ℝ (Tests Clock clock_dense) :=
  derivative Clock clock_dense (clockUnitary (value φ f))

theorem value_error (φ : TestFunction) (f q : JointL2) :
    ‖value φ f - value φ q‖ ≤ φ.slopeBound * ‖f - q‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [value_ae φ f, value_ae φ q,
    Lp.coeFn_sub (value φ f) (value φ q), Lp.coeFn_sub f q] with ω hf hq hs hd
  simp only [hs, Pi.sub_apply, hf, hq, hd]
  exact (value_lipschitz φ).norm_sub_le _ _

theorem value_L2_lipschitz (φ : TestFunction) :
    LipschitzWith ⟨φ.slopeBound, slopeBound_nonneg φ⟩ (value φ) :=
  lipschitzWith_iff_norm_sub_le.mpr (value_error φ)

theorem weakDerivative_continuous (φ : TestFunction) : Continuous (weakDerivative φ) :=
  (derivative Clock clock_dense).continuous.comp
    (clockUnitary.continuous.comp (value_L2_lipschitz φ).continuous)

theorem chain_graph (φ : TestFunction) (f : JointL2) (V : FieldSpace)
    (hg : (clockUnitary f, V) ∈ Clock.graph) :
    (clockUnitary (value φ f), chainField φ f V) ∈ Clock.graph := by
  have hfg : (ProductL2Curry.curry gaussianProduct gaussianProduct f,
      ProductL2Curry.curry gaussianProduct gaussianProduct
        (IBMIntrinsicChainRule.uncurryField V)) ∈ Clock.graph := by
    change (clockUnitary f, (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct)
      ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm V)) ∈ _
    rwa [LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨F, G, hG, hF, hs⟩ := GaussianClosedChainRule.bounded_product_chain_graph
    f _ hfg φ.value φ.slope φ.hasDeriv φ.continuous_slope
    φ.valueBound φ.slopeBound φ.value_le φ.slope_le
  have heF : F = value φ f := Lp.ext (hF.trans (value_ae φ f).symm)
  have heG : G = slopeField φ f (IBMIntrinsicChainRule.uncurryField V) :=
    Lp.ext (hs.trans (slopeField_ae φ f _).symm)
  subst F
  subst G
  exact hG

theorem chain_dual_error (φ : TestFunction) (f q : JointL2) (V : FieldSpace)
    (hg : (clockUnitary f, V) ∈ Clock.graph) :
    ‖embed Clock clock_dense (chainField φ f V) - weakDerivative φ q‖ ≤
      φ.slopeBound * ‖f - q‖ := by
  have hb := graph_error_bound Clock clock_dense (chain_graph φ f V hg)
    (clockUnitary (value φ q))
  have he : ‖clockUnitary (value φ f) - clockUnitary (value φ q)‖ =
      ‖value φ f - value φ q‖ := by rw [← map_sub, clockUnitary.norm_map]
  exact (hb.trans_eq he).trans (value_error φ f q)

theorem chain_dual_limit (φ : TestFunction) (u : ℕ → JointL2) (V : ℕ → FieldSpace)
    (hg : ∀ n, (clockUnitary (u n), V n) ∈ Clock.graph) (f : JointL2)
    (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun n => embed Clock clock_dense (chainField φ (u n) (V n))) atTop
      (𝓝 (weakDerivative φ f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => chain_dual_error φ (u n) f (V n) (hg n))
  simpa using tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hu)

theorem actual_pairing (φ : TestFunction) (f : JointL2)
    (X : IBMSourceLaws.JointSample → ℝ) (hX : f =ᵐ[IBMSourceLaws.jointMeasure] X)
    (v : Clock.adjoint.domain) :
    weakDerivative φ f (testOf Clock clock_dense v) =
      ∫ ω, φ.value (X ω) * (clockUnitary.symm (Clock.adjoint v)) ω
        ∂IBMSourceLaws.jointMeasure := by
  change inner ℝ (clockUnitary (value φ f)) (Clock.adjoint v) = _
  have hi := clockUnitary.inner_map_map (value φ f) (clockUnitary.symm (Clock.adjoint v))
  rw [clockUnitary.apply_symm_apply] at hi
  rw [hi, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [value_ae φ f, hX] with ω hf hx
  rw [hf, hx, Real.inner_apply]

theorem actual_pairing_integrable (φ : TestFunction) (f : JointL2)
    (X : IBMSourceLaws.JointSample → ℝ) (hX : f =ᵐ[IBMSourceLaws.jointMeasure] X)
    (v : Clock.adjoint.domain) :
    Integrable (fun ω => φ.value (X ω) * (clockUnitary.symm (Clock.adjoint v)) ω)
      IBMSourceLaws.jointMeasure := by
  apply ((Lp.memLp (value φ f)).integrable_mul
    (Lp.memLp (clockUnitary.symm (Clock.adjoint v)))).congr
  filter_upwards [value_ae φ f, hX] with ω hf hx
  simp only [Pi.mul_apply, hf, hx]

end OperatorDerivativeRewrite.Foundation.IBMClockWeakChain
