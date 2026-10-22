import Foundation.IBMIntrinsicMartingaleSeries
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Cofinal deterministic observations recover the actual raw IBM past.
Continuity is used pointwise for the constructed IBM, without usual conditions. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCofinalPast
open IBMNaturalFiltrationObstruction IBMTimeAveragedObservable IBMIntrinsicMartingaleGrid
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.ibmValue

private instance pastProjection (t : ℝ≥0) : (past t).HasOrthogonalProjection := by
  let : CompleteSpace (past t) := (past_closed t).completeSpace_coe
  infer_instance

theorem natural_eq_iSup (τ : ℕ → ℝ≥0) (T : ℝ≥0) (hT : ∀ n, τ n ≤ T)
    (hlim : Tendsto τ atTop (𝓝 T)) :
    naturalFiltration T = ⨆ n, naturalFiltration (τ n) := by
  apply le_antisymm
  · have hm : Measurable[⨆ n, naturalFiltration (τ n)] (IBMConstructedSources.ibmValue T) := by
      let : MeasurableSpace IBMSourceLaws.JointSample := ⨆ n, naturalFiltration (τ n)
      apply measurable_of_tendsto_metrizable
        (fun n => (point_stronglyAdapted (τ n)).measurable.mono
          (le_iSup (fun k : ℕ => naturalFiltration (τ k)) n) le_rfl)
      apply tendsto_pi_nhds.mpr
      intro ω
      exact ((IBMConstructedSources.ibmValue_continuous ω).tendsto T).comp hlim
    change (⨆ s ≤ T, MeasurableSpace.comap (IBMConstructedSources.ibmValue s) inferInstance) ≤ _
    apply iSup₂_le
    intro s hs
    rcases eq_or_lt_of_le hs with he | hs
    · subst s
      exact hm.comap_le
    · have he : ∀ᶠ n in atTop, s < τ n := hlim.eventually (eventually_gt_nhds hs)
      obtain ⟨n, hn⟩ := he.exists
      exact (point_stronglyAdapted s).measurable.comap_le.trans
        ((naturalFiltration.mono hn.le).trans
          (le_iSup (fun k : ℕ => naturalFiltration (τ k)) n))
  · exact iSup_le fun n => naturalFiltration.mono (hT n)

theorem projection_ae (t : ℝ≥0) (f : JointL2) :
    (past t).starProjection f =ᵐ[IBMSourceLaws.jointMeasure]
      IBMSourceLaws.jointMeasure[f | naturalFiltration t] := by
  have he := (Lp.memLp f).condExpL2_ae_eq_condExp (𝕜 := ℝ) (naturalFiltration.le t)
  simpa only [Lp.toLp_coeFn, past, condExpL2, Submodule.starProjection_apply] using he

theorem projection_tendsto (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (T : ℝ≥0)
    (hT : ∀ n, τ n ≤ T) (hlim : Tendsto τ atTop (𝓝 T)) (f : JointL2) :
    Tendsto (fun n => (past (τ n)).starProjection f) atTop (𝓝 ((past T).starProjection f)) := by
  let : ∀ n, Fact (naturalFiltration (τ n) ≤
      (inferInstance : MeasurableSpace IBMSourceLaws.JointSample)) := fun n => ⟨naturalFiltration.le _⟩
  let : ∀ n, (past (τ n)).HasOrthogonalProjection := fun n => by
    unfold past
    infer_instance
  have hp := Submodule.starProjection_tendsto_closure_iSup (fun n => past (τ n))
    (fun i j hij f hf => hf.mono (naturalFiltration.mono (hτ hij))) f
  have hm := tendstoInMeasure_of_tendsto_Lp hp
  have hc := tendsto_eLpNorm_condExp (μ := IBMSourceLaws.jointMeasure)
    (ℱ := gridFiltration τ hτ) (f : IBMSourceLaws.JointSample → ℝ)
  change Tendsto (fun n => eLpNorm
    (IBMSourceLaws.jointMeasure[f | naturalFiltration (τ n)] -
      IBMSourceLaws.jointMeasure[f | ⨆ n, naturalFiltration (τ n)]) 1 IBMSourceLaws.jointMeasure)
        atTop (𝓝 0) at hc
  rw [← natural_eq_iSup τ T hT hlim] at hc
  have hc' := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) hc
  have he := tendstoInMeasure_ae_unique hm
    (hc'.congr (fun n => (projection_ae (τ n) f).symm) (projection_ae T f).symm)
  have heq : (⨆ n, past (τ n)).topologicalClosure.starProjection f = (past T).starProjection f :=
    Lp.ext he
  rw [heq] at hp
  exact hp

end OperatorDerivativeRewrite.Foundation.IBMCofinalPast
