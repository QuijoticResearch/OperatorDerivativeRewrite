import Foundation.IBMPhysicalMeasureSeparation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! Faithfulness of the ORIGINAL physical zero-order embedding, proved by
actual distribution tests and the existing Schwartz density in spatial L2. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BesselPotentialSpace SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalSpatialInjection
open GaussianTimeHilbert IBMPhysicalNoiseClock IBMPhysicalNegativeEmbedding
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

theorem real_test (u : TimeHilbert) (g : 𝓢(ℝ, ℝ)) :
    (embedding u).toDistr (g.postcompCLM Complex.ofRealCLM) =
      Complex.ofReal (inner ℝ (g.toLp 2 volume) u) := by
  rw [embedding_toDistr, Lp.toTemperedDistribution_apply, L2.inner_def]
  simp only [smul_eq_mul]
  have hi : Integrable (fun x : ℝ => (g x)*(u x)) volume :=
    (g.memLp 2 volume).integrable_mul (Lp.memLp u)
  have he : (∫ x, g.postcompCLM Complex.ofRealCLM x * complexify u x) =
      ∫ x, Complex.ofReal (g x*u x) := by
    apply integral_congr_ae
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL u] with x hc
    change complexify u x = Complex.ofReal (u x) at hc
    rw [hc,SchwartzMap.postcompCLM_apply]
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul]
  have hc := Complex.ofRealCLM.integral_comp_comm hi
  change (∫ x, Complex.ofReal (g x*u x)) = Complex.ofReal (∫ x, g x*u x) at hc
  rw [he, hc]
  congr 1
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp 2 volume] with x hx
  rw [hx,Real.inner_apply]

theorem embedding_eq_zero (u : TimeHilbert) (hu : embedding u = 0) : u = 0 := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  have hc : IsClosed {v : TimeHilbert | inner ℝ v u = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hs : range (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure ℝ)) ⊆
      {v : TimeHilbert | inner ℝ v u = 0} := by
    rintro v ⟨g,rfl⟩
    change inner ℝ (g.toLp 2 volume) u = 0
    apply Complex.ofReal_injective
    rw [← real_test u g, hu]
    rfl
  exact inner_self_eq_zero.mp ((closure_minimal hs hc) (hd u))

theorem embedding_injective : Function.Injective embedding := by
  intro u v huv
  apply sub_eq_zero.mp
  apply embedding_eq_zero
  rw [map_sub,huv,sub_self]

theorem compLp_injective {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    Function.Injective (embedding.compLpL 2 μ) := by
  intro U V h
  apply Lp.ext
  filter_upwards [embedding.coeFn_compLpL U, embedding.coeFn_compLpL V] with x hu hv
  rw [h,hv] at hu
  exact embedding_injective hu.symm

end OperatorDerivativeRewrite.Foundation.IBMPhysicalSpatialInjection
