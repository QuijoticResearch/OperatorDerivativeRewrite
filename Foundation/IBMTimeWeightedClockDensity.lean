import Foundation.IBMTimeWeightedClockOperator

/-! Strong-convergence domain of the original weighted native operators.
Uniform energy makes it closed; the existing generating-indicator density
theorem reduces its totality to genuine prefix convergence. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTimeWeightedClockDensity
open IBMClockOverlapEnergy IBMIntrinsicOperators IBMTimeWeightedClockOperator
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def convergent (T : ℝ≥0) : Submodule ℝ (TimeL2 T) where
  carrier := {g | ∃ v, Tendsto (fun n => nativeOperator n T g) atTop (𝓝 v)}
  zero_mem' := ⟨0,by simpa only [map_zero] using tendsto_const_nhds⟩
  add_mem' := by
    rintro g h ⟨v,hv⟩ ⟨w,hw⟩
    exact ⟨v+w,by simpa only [map_add] using hv.add hw⟩
  smul_mem' := by
    rintro c g ⟨v,hv⟩
    exact ⟨c • v,by simpa only [map_smul] using hv.const_smul c⟩

attribute [local irreducible] nativeOperator nativeLinear convergent bound

private theorem closed_convergence_set {E F : Type*} [MetricSpace E] [MetricSpace F]
    [CompleteSpace F] (A : ℕ → E → F) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ n x y, dist (A n x) (A n y) ≤ C * dist x y) :
    IsClosed {g | ∃ v, Tendsto (fun n => A n g) atTop (𝓝 v)} := by
  apply IsSeqClosed.isClosed
  intro u g hu hg
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hδ : 0 < ε/(4*(C+1)) := div_pos hε (by positivity)
  obtain ⟨j,hj⟩ := (hg.eventually (Metric.ball_mem_nhds g hδ)).exists
  have hj' : dist (u j) g < ε/(4*(C+1)) := hj
  have he (n : ℕ) : dist (A n g) (A n (u j)) < ε/4 := by
    have hb := hA n g (u j)
    rw [dist_comm g] at hb
    have hx : C * dist (u j) g < ε/4 := by
      have hm := (mul_lt_mul_of_pos_right hj' (by positivity : 0 < C+1))
      have hd : ε/(4*(C+1))*(C+1) = ε/4 := by
        field_simp
      rw [hd] at hm
      nlinarith [dist_nonneg (x := u j) (y := g)]
    exact hb.trans_lt hx
  obtain ⟨v,hv⟩ := hu j
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hv.cauchySeq (ε/2) (by linarith)
  refine ⟨N,fun m hm n hn => ?_⟩
  have hmid := hN m hm n hn
  have hl := he m
  have hr := he n
  have ht := dist_triangle (A m g) (A m (u j)) (A n g)
  have ht' := dist_triangle (A m (u j)) (A n (u j)) (A n g)
  rw [dist_comm (A n (u j))] at ht'
  linarith

theorem convergent_closed (T : ℝ≥0) : IsClosed (convergent T : Set (TimeL2 T)) := by
  unfold convergent
  exact closed_convergence_set (fun n => nativeOperator n T) (bound T)
    (by unfold bound; exact Real.sqrt_nonneg _) (fun n => nativeOperator_difference n T)

def prefixSets : Set (Set ℝ) := insert univ (range Iic)

theorem prefix_span_dense (T : ℝ≥0) :
    (generatingIndicatorSpan (window T) prefixSets).topologicalClosure = ⊤ := by
  have he := generatingIndicatorSpan_closure (window T) le_rfl prefixSets
    (by rw [prefixSets,MeasurableSpace.generateFrom_insert_univ,
      ← borel_eq_generateFrom_Iic,← BorelSpace.measurable_eq])
    isPiSystem_Iic.insert_univ (mem_insert _ _)
  rw [he]
  apply top_unique
  intro g _
  exact mem_lpMeas_self _ g

theorem all_of_prefix (T : ℝ≥0)
    (hp : ∀ s ∈ prefixSets, ∀ hs : MeasurableSet s,
      indicatorConstLp 2 hs (measure_ne_top (window T) s) (1 : ℝ) ∈ convergent T) :
    convergent T = ⊤ := by
  apply top_unique
  rw [← prefix_span_dense T]
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro g ⟨s,hs,hm,rfl⟩
    exact hp s hs hm
  · exact convergent_closed T

end OperatorDerivativeRewrite.Foundation.IBMTimeWeightedClockDensity
