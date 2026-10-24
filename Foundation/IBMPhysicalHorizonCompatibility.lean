import Foundation.IBMPhysicalLpSeparation

/-! The ORIGINAL physical Ito integrals agree across horizons whenever their
actual zero-extended predictable fields agree. All scalarization-domain
witnesses are constructed; no new integral or stochastic law is postulated. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalHorizonCompatibility
open InfiniteGaussian IBMPhysicalWeakWiener GaussianTimeProductL2 GaussianTimeProcess
open GaussianPredictableFull IBMPhysicalClockIto
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

def testDomain (T : ℝ≥0) (L : Tests) (u : Domain T) :
    GaussianPredictableHorizon.PredictableDomain T :=
  ⟨L.compLpL 2 (PredictableRealL2.horizonMeasure T gaussianProduct) u.val,
    (L.continuous.comp_aestronglyMeasurable u.property).congr
      (L.coeFn_compLpL u.val).symm⟩

def scalarField (T : ℝ≥0) (L : Tests) (u : Domain T) : fullPredictable :=
  domainEquiv.symm (GaussianPredictableHorizon.horizonEmbedding T (testDomain T L u))

theorem scalarField_ae (T : ℝ≥0) (L : Tests) (u : Domain T) :
    (scalarField T L u : TimeProbabilityL2) =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => L (u.val z)) := by
  change L2ZeroExtension (PredictableRealL2.horizon_measurable T)
    (L.compLpL 2 (PredictableRealL2.horizonMeasure T gaussianProduct) u.val) =ᵐ[timeProbability] _
  exact (L2ZeroExtension_coeFn (PredictableRealL2.horizon_measurable T) _).trans
    ((ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp
      (L.coeFn_compLpL u.val))

theorem scalarization (T : ℝ≥0) (L : Tests) (u : Domain T) :
    L.compLpL 2 gaussianProduct (IBMPhysicalClockIto.integral T u) =
      GaussianPredictableFull.itoIntegral (scalarField T L u) :=
  IBMSchwartzPhysicalReflectedIto.scalarization_full T L u (scalarField T L u)
    (scalarField_ae T L u)

theorem compatible (a b : ℝ≥0) (u : Domain a) (v : Domain b)
    (h : (PredictableRealL2.horizon a).indicator (fun z => u.val z) =ᵐ[timeProbability]
      (PredictableRealL2.horizon b).indicator (fun z => v.val z)) :
    IBMPhysicalClockIto.integral a u = IBMPhysicalClockIto.integral b v := by
  apply IBMPhysicalLpSeparation.ext
  intro L
  rw [scalarization, scalarization]
  congr 1
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [scalarField_ae a L u, scalarField_ae b L v, h] with z hu hv hz
  rw [hu, hv]
  have hL := congrArg L hz
  by_cases ha : z ∈ PredictableRealL2.horizon a <;>
    by_cases hb : z ∈ PredictableRealL2.horizon b <;>
    simpa [ha, hb] using hL

end OperatorDerivativeRewrite.Foundation.IBMPhysicalHorizonCompatibility
