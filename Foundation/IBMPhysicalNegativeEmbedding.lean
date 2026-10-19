import Foundation.IBMPhysicalDirac

/-! Bounded zero-order embedding of the actual physical L2 kernels into
the same H^-1 space as their verified distributional derivatives. -/
noncomputable section
open MeasureTheory TemperedDistribution Filter
open scoped BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalNegativeEmbedding
open GaussianTimeHilbert IBMPhysicalNoiseClock IBMPhysicalDirac

theorem realNormSMul : NormSMulClass ℝ H^{(-1 : ℝ)}(ℝ) := by
  constructor
  intro c u
  change ‖(c • u).toLp‖ = ‖c‖*‖u.toLp‖
  rw [BesselPotentialSpace.toLp_smul, norm_smul]

theorem realContinuousSMul : ContinuousSMul ℝ H^{(-1 : ℝ)}(ℝ) := by
  constructor
  apply (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).isometry.isEmbedding.continuous_iff.mpr
  change Continuous (fun p : ℝ × H^{(-1 : ℝ)}(ℝ) => p.1 • p.2.toLp)
  exact continuous_fst.smul
    ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).continuous.comp continuous_snd)

theorem l2Value_add (u v : TimeHilbert) : l2Value (u+v) = l2Value u+l2Value v := by
  apply BesselPotentialSpace.ext
  simp only [l2Value_toDistr, BesselPotentialSpace.toDistr_add, map_add]
  exact (Lp.toTemperedDistributionCLM ℂ volume 2).map_add _ _

theorem l2Value_smul (c : ℝ) (u : TimeHilbert) : l2Value (c • u) = c • l2Value u := by
  apply BesselPotentialSpace.ext
  simp only [l2Value_toDistr, BesselPotentialSpace.toDistr_smul, map_smul]
  exact ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).map_smul c _

def l2ValueLinear : TimeHilbert →ₗ[ℝ] H^{(-1 : ℝ)}(ℝ) where
  toFun := l2Value
  map_add' := l2Value_add
  map_smul' := l2Value_smul

theorem l2Value_seqClosedGraph :
    ∀ (u : ℕ → TimeHilbert) (x : TimeHilbert) (y : H^{(-1 : ℝ)}(ℝ)),
      Tendsto u atTop (nhds x) → Tendsto (l2ValueLinear ∘ u) atTop (nhds y) →
        y = l2ValueLinear x := by
  intro u x y hu hv
  let J := ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp complexify
  have hl := IBMNegativeSobolevBounded.hminusOneToDistrCLM.continuous.tendsto y |>.comp hv
  have hr := J.continuous.tendsto x |>.comp hu
  have he (n : ℕ) : IBMNegativeSobolevBounded.hminusOneToDistrCLM (l2ValueLinear (u n)) =
      J (u n) := by
    rw [IBMNegativeSobolevBounded.hminusOneToDistrCLM_apply]
    exact l2Value_toDistr _
  have hr' : Tendsto (fun n => IBMNegativeSobolevBounded.hminusOneToDistrCLM
      (l2ValueLinear (u n))) atTop (nhds (J x)) := by
    simpa only [he, Function.comp_def] using hr
  have heq := tendsto_nhds_unique hl hr'
  apply BesselPotentialSpace.ext
  change y.toDistr = (l2Value x).toDistr
  rw [l2Value_toDistr]
  rw [IBMNegativeSobolevBounded.hminusOneToDistrCLM_apply] at heq
  change y.toDistr = (Lp.toTemperedDistributionCLM ℂ volume 2) (complexify x) at heq
  simpa only [Lp.toTemperedDistributionCLM_apply] using heq

def embedding : TimeHilbert →L[ℝ] H^{(-1 : ℝ)}(ℝ) :=
  ContinuousLinearMap.ofSeqClosedGraph l2Value_seqClosedGraph

theorem embedding_apply (u : TimeHilbert) : embedding u = l2Value u := rfl

theorem embedding_toDistr (u : TimeHilbert) :
    (embedding u).toDistr = (complexify u : Lp ℂ 2 volume) := l2Value_toDistr u

end OperatorDerivativeRewrite.Foundation.IBMPhysicalNegativeEmbedding
