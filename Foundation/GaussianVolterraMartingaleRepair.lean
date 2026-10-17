import Foundation.GaussianVolterraMartingaleObstruction

/-! A genuine integrating-factor martingale for the actual exponential Volterra
convolution, with the corresponding deterministic Itô integrand. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianVolterraMartingaleRepair
set_option backward.isDefEq.respectTransparency false
open InfiniteGaussian GaussianExponentialMarkovPrediction GaussianConditionalGraph
open GaussianVolterraMartingaleObstruction SPDEExponentialForcing
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

def scaling (rate t : ℝ≥0) : ℝ := Real.exp ((rate : ℝ)*(t : ℝ))

def weightedClass (rate t : ℝ≥0) : GaussianL2 := scaling rate t • value rate t

def weighted (rate t : ℝ≥0) (ω : SampleSpace) : ℝ := scaling rate t*process rate t ω

theorem weightedClass_ae (rate t : ℝ≥0) : weightedClass rate t =ᵐ[gaussianProduct] weighted rate t := by
  filter_upwards [Lp.coeFn_smul (scaling rate t) (value rate t)] with ω hω
  exact hω

theorem scaling_decay (rate s t : ℝ≥0) : scaling rate t*decay rate s t = scaling rate s := by
  unfold scaling decay
  rw [← Real.exp_add]
  congr 1
  ring

theorem weighted_adapted (rate : ℝ≥0) : StronglyAdapted (history rate) (weighted rate) := by
  intro t
  exact (process_adapted rate t).const_mul (scaling rate t)

theorem weighted_condExp (rate s t : ℝ≥0) (hst : s ≤ t) :
    gaussianProduct[weighted rate t | history rate s] =ᵐ[gaussianProduct] weighted rate s := by
  have hc := condExp_smul (μ := gaussianProduct) (scaling rate t) (process rate t) (history rate s)
  filter_upwards [hc, process_condExp rate s t hst] with ω hω hp
  calc
    _ = scaling rate t*gaussianProduct[process rate t | history rate s] ω := hω
    _ = scaling rate t*(decay rate s t*process rate s ω) := by rw [hp]
    _ = weighted rate s ω := by rw [← mul_assoc, scaling_decay]; rfl

theorem weighted_martingale (rate : ℝ≥0) : Martingale (weighted rate) (history rate) gaussianProduct :=
  ⟨weighted_adapted rate, fun s t hst => weighted_condExp rate s t hst⟩

theorem zero_rate_martingale : Martingale (process 0) (history 0) gaussianProduct := by
  have he : weighted 0 = process 0 := by
    funext t ω
    simp [weighted, scaling]
  rw [← he]
  exact weighted_martingale 0

theorem weighted_is_actual_ito (rate t : ℝ≥0) :
    weightedClass rate t = GaussianPredictableFull.itoIntegral
      (scaling rate t • GaussianDeterministicVolterra.profileField (causalProfile rate t)) := by
  rw [map_smul, ← value_is_actual_ito]
  rfl

theorem compensated_response (rate t : ℝ≥0) (u : ℝ) :
    scaling rate t*response rate t u =
      (Ioc 0 (t : ℝ)).indicator (fun s => Real.exp ((rate : ℝ)*s)) u := by
  by_cases hu : u ∈ Ioc 0 (t : ℝ)
  · rw [response, indicator_of_mem hu, indicator_of_mem hu, scaling, ← Real.exp_add]
    congr 1
    ring
  · simp [response, hu]

end OperatorDerivativeRewrite.Foundation.GaussianVolterraMartingaleRepair
