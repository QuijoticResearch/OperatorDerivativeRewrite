import Foundation.HigherHeatProbabilitySampling

/-! Explicit measurable continuous-path lifts of actual finite higher-heat configurations. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatInterpolatedPaths
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatCylinderFourier
open HigherHeatProbabilitySampling

def nodeValue (n : ℕ) (y : Grid n) (o : Option (Fin (gridSize n))) : ℝ := o.elim 0 y

def polynomial (n : ℕ) (y : Grid n) : Polynomial ℝ :=
  Lagrange.interpolate Finset.univ (interpolationNode n) (nodeValue n y)

def process (n : ℕ) (t : ℝ) (y : Grid n) : ℝ := (polynomial n y).eval t

theorem nodeValue_continuous (n : ℕ) (o : Option (Fin (gridSize n))) :
    Continuous (fun y : Grid n => nodeValue n y o) := by
  cases o with
  | none => exact continuous_const
  | some i => exact continuous_apply i

theorem process_joint_continuous (n : ℕ) :
    Continuous (fun z : ℝ × Grid n => process n z.1 z.2) := by
  classical
  unfold process polynomial
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]
  apply continuous_finsetSum
  intro o ho
  exact ((nodeValue_continuous n o).comp continuous_snd).mul
    ((Lagrange.basis Finset.univ (interpolationNode n) o).continuous.comp continuous_fst)

theorem process_path_continuous (n : ℕ) (y : Grid n) : Continuous (fun t => process n t y) :=
  (process_joint_continuous n).comp (continuous_id.prodMk continuous_const)

theorem process_zero (n : ℕ) (y : Grid n) : process n 0 y=0 :=
  Lagrange.eval_interpolate_at_node (nodeValue n y) (interpolationNode_injective n).injOn
    (Finset.mem_univ (none : Option (Fin (gridSize n))))

theorem process_sample (n : ℕ) (y : Grid n) (i : Fin (gridSize n)) :
    process n (sampleTime n i) y=y i :=
  Lagrange.eval_interpolate_at_node (nodeValue n y) (interpolationNode_injective n).injOn
    (Finset.mem_univ (some i))

def path (n : ℕ) (y : Grid n) : Path :=
  ⟨⟨fun t => process n t y, process_path_continuous n y⟩, process_zero n y⟩

theorem path_continuous (n : ℕ) : Continuous (path n) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (process_joint_continuous n).comp continuous_swap

theorem sample_path (n : ℕ) (y : Grid n) : sample n (path n y)=y := by
  funext i
  exact process_sample n y i

theorem path_injective (n : ℕ) : Function.Injective (path n) := by
  intro x y h
  have hh := congrArg (sample n) h
  simpa only [sample_path] using hh

def incrementPath (n : ℕ) (x : Grid n) : Path :=
  path n (linearImage (cumulativeMatrix (gridSize n)) x)

theorem cumulative_continuous (n : ℕ) :
    Continuous (linearImage (cumulativeMatrix (gridSize n))) := by
  unfold linearImage
  fun_prop

theorem incrementPath_continuous (n : ℕ) : Continuous (incrementPath n) :=
  (path_continuous n).comp (cumulative_continuous n)

theorem sample_incrementPath (n : ℕ) (x : Grid n) :
    sample n (incrementPath n x)=linearImage (cumulativeMatrix (gridSize n)) x := sample_path n _

theorem incrementPath_injective (n : ℕ) : Function.Injective (incrementPath n) := by
  intro x y h
  apply (HigherHeatPositionVariation.cumulative_embedding (gridSize n)).injective
  have hh := congrArg (sample n) h
  simpa only [sample_incrementPath] using hh

def probabilityPath (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : Measure Path :=
  (dyadicProbability m hm T hT n).map (incrementPath n)

theorem probabilityPath_isProbability (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    IsProbabilityMeasure (probabilityPath m hm T hT n) := by
  letI : IsProbabilityMeasure (dyadicProbability m hm T hT n) := probability_isProbability (gridSize n) m hm
    (fun _ => duration T n) (fun _ => duration_pos T hT n)
  constructor
  rw [probabilityPath, Measure.map_apply (incrementPath_continuous n).measurable MeasurableSet.univ,
    Set.preimage_univ]
  exact measure_univ

def signedPath (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : SignedMeasure Path :=
  (HigherHeatSignedLaws.incrementLaw m hm (fun _ : Fin (gridSize n) => duration T n)
    (fun _ => duration_pos T hT n)).map (incrementPath n)

theorem signedPath_sample (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (signedPath m hm T hT n).map (sample n)=law m hm T hT n := by
  rw [signedPath, HigherHeatObservationRefinement.map_comp _ _ _
    (incrementPath_continuous n).measurable (sample_continuous n).measurable]
  change _= (HigherHeatSignedLaws.incrementLaw m hm (fun _ : Fin (gridSize n) => duration T n)
    (fun _ => duration_pos T hT n)).map (linearImage (cumulativeMatrix (gridSize n)))
  congr 1
  funext x
  exact sample_incrementPath n x

theorem signedPath_mass (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    signedPath m hm T hT n Set.univ=1 := by
  rw [signedPath, VectorMeasure.map_apply _ (incrementPath_continuous n).measurable
    MeasurableSet.univ, Set.preimage_univ, HigherHeatSignedLaws.incrementLaw_mass]

theorem signedPath_variation_mass (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ((signedPath m hm T hT n).variation Set.univ).toReal=
      (∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m hm T hT x‖)^(gridSize n) := by
  have hlo := HigherHeatPathObstruction.variation_mass_map_le (signedPath m hm T hT n)
    (sample n) (sample_continuous n).measurable
  rw [signedPath_sample, HigherHeatPositionVariation.dyadic_variation_mass] at hlo
  have hhi := HigherHeatPathObstruction.variation_mass_map_le
    (HigherHeatSignedLaws.incrementLaw m hm (fun _ : Fin (gridSize n) => duration T n)
      (fun _ => duration_pos T hT n)) (incrementPath n) (incrementPath_continuous n).measurable
  have he := (SignedDensityProbabilitySampling.mass_eq_variation (base (gridSize n))
    (density (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n))
    (HigherHeatSignedLaws.incrementDensity_integrable m hm (fun _ : Fin (gridSize n) => duration T n)
      (fun _ => duration_pos T hT n))).symm.trans (dyadic_mass m hm T hT n)
  exact le_antisymm (hhi.trans_eq he) hlo

theorem signedPath_variation_unbounded (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) (B : ℝ) :
    ∃ n, B < ((signedPath m (by omega) T hT n).variation Set.univ).toReal := by
  let C : ℝ := ∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m (by omega : 0 < m) T hT x‖
  have hC : 1 < C := HigherHeatKernelMoments.norm_integral_gt_one m hm T hT
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt B hC
  refine ⟨n, ?_⟩
  rw [signedPath_variation_mass]
  exact hn.trans_le (pow_le_pow_right₀ hC.le (HigherHeatPositionVariation.level_le_size n))

end OperatorDerivativeRewrite.Foundation.HigherHeatInterpolatedPaths
