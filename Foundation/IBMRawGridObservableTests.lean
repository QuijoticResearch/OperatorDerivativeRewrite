import Foundation.IBMRawGridWickLimit
import Foundation.IBMRawInitialPast

/-! Actual observable terminal-square tests of the ORIGINAL intrinsic grid
divergence. Random clock overlaps are retained exactly; no convergence of
their nonsmooth random-level quadratic variation is postulated. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawGridObservableTests
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMJointIntrinsicDerivative IBMRawStepSources IBMRawStepCompensation
open IBMRawGridSecondChaos IBMRawGridWickLimit IBMRawGridCompensation
open IBMUniformClockGridEnergy GaussianTimeSpaceHermite IBMQuarticSecondChaos
open IBMSourceProductBounds IBMSchwartzSourceContinuity
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] jointDerivative LinearPMap.adjoint LinearPMap.graph

def squareObservation (R : ℝ≥0) : IntrinsicSpace := -rawObservable R 0

theorem squareObservation_actual (R : ℝ≥0) :
    (squareObservation R : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => (IBMConstructedSources.ibmValue R p)^2 := by
  filter_upwards [Lp.coeFn_neg (rawStep R 0),raw_actual R 0,
    IBMRawInitialPast.ibm_zero_ae] with p hn hr hz
  change (-rawStep R 0) p = _
  rw [hn,Pi.neg_apply,hr]
  simp only [rawFunction,hz]
  ring

theorem squareObservation_memLp (R : ℝ≥0) :
    MemLp (fun p => (IBMConstructedSources.ibmValue R p)^2) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (squareObservation R : JointL2)).ae_eq (squareObservation_actual R)

theorem source_mean_zero (u : ℕ → CoefficientSpace) (n : ℕ) :
    inner ℝ (sourceSum u n) gaussianOne = 0 := by
  unfold sourceSum cross
  simp only [sum_inner,inner_smul_left,inner_sub_left]
  have hc (k : CoefficientSpace) : inner ℝ (wick k 2 : GaussianL2) gaussianOne = 0 :=
    (real_inner_comm _ _).trans (wick_centered k 1)
  simp only [hc,sub_self,mul_zero,Finset.sum_const_zero]

theorem raw_square_test (u : ℕ → CoefficientSpace) (n : ℕ) (k : CoefficientSpace) :
    inner ℝ (sourceSum u n) (rawProduct k k) =
      (inner ℝ (u n) k)^2-(inner ℝ (u 0) k)^2-
        ∑ i ∈ Finset.range n, (inner ℝ (u (i+1)) k-inner ℝ (u i) k)^2 := by
  rw [rawProduct_eq_cross,inner_add_right,inner_smul_right,source_mean_zero,mul_zero,
    add_zero,cross_self]
  exact source_test_telescope u n k

def overlap (R : ℝ≥0) (Y : SampleSpace) (t : ℝ≥0) : ℝ :=
  min |GaussianTimeProcess.process t Y| |GaussianTimeProcess.process R Y|

theorem direction_overlap (R t : ℝ≥0) (Y : SampleSpace) :
    inner ℝ (clockDirection t Y) (clockDirection R Y) = overlap R Y t := by
  have h := IBMRawTemporalKernel.source_inner
    (abs_nonneg (GaussianTimeProcess.process t Y)) (abs_nonneg (GaussianTimeProcess.process R Y))
  change inner ℝ (firstChaosEmbedding (clockDirection t Y))
    (firstChaosEmbedding (clockDirection R Y)) = _ at h
  rw [firstChaosEmbedding.inner_map_map] at h
  exact h

def overlapEnergy (h : ℝ≥0) (n : ℕ) (R : ℝ≥0) (Y : SampleSpace) : ℝ :=
  (overlap R Y (grid h n))^2-
    ∑ i ∈ Finset.range n, (overlap R Y (grid h (i+1))-overlap R Y (grid h i))^2

theorem source_square_pairing_ae (h : ℝ≥0) (n : ℕ) (R : ℝ≥0) :
    (fun Y => inner ℝ (sourceGrid h n Y) ((-rawSource R 0) Y)) =ᵐ[gaussianProduct]
      overlapEnergy h n R := by
  filter_upwards [sourceGrid_ae h n,(raw_memLp R 0).coeFn_toLp,
    Lp.coeFn_neg (rawSource R 0),clockCurve_initial h] with Y hs hr hn hz
  have hz0 : clockDirection 0 Y = 0 := by simpa only [clockCurve,grid,Nat.cast_zero,mul_zero] using hz
  change rawSource R 0 Y = rawSections R 0 Y at hr
  rw [hn,Pi.neg_apply,hs,hr]
  have he : -rawSections R 0 Y = rawProduct (clockDirection R Y) (clockDirection R Y) := by
    change -rawBilinear (clockDirection 0 Y-clockDirection R Y) (clockDirection R Y) = _
    rw [hz0,zero_sub,map_neg,ContinuousLinearMap.neg_apply,neg_neg]
    rfl
  rw [he,raw_square_test,hz,inner_zero_left]
  simp only [clockCurve,direction_overlap,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero]
  rfl

theorem overlapEnergy_integrable (h : ℝ≥0) (n : ℕ) (R : ℝ≥0) :
    Integrable (overlapEnergy h n R) gaussianProduct :=
  (L2.integrable_inner (sourceGrid h n) (-rawSource R 0)).congr (source_square_pairing_ae h n R)

theorem observable_pairing (h : ℝ≥0) (n : ℕ) (R : ℝ≥0) :
    inner ℝ (jointDivergence (gridInput h n)) (squareObservation R) =
      ∫ Y, overlapEnergy h n R Y ∂gaussianProduct := by
  rw [native_grid_value]
  have hp := IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right
    (squareObservation R) (jointRealization (sourceGrid h n))
  rw [hp]
  change inner ℝ (jointRealization (sourceGrid h n)) (-jointRealization (rawSource R 0)) = _
  rw [← map_neg,jointRealization.inner_map_map,L2_inner_eq_integral]
  exact integral_congr_ae (source_square_pairing_ae h n R)

theorem overlap_increment_bound (R s t : ℝ≥0) (Y : SampleSpace) :
    (overlap R Y t-overlap R Y s)^2 ≤
      (GaussianTimeProcess.process t Y-GaussianTimeProcess.process s Y)^2 := by
  have hm := abs_min_sub_min_le_max |GaussianTimeProcess.process t Y|
    |GaussianTimeProcess.process R Y| |GaussianTimeProcess.process s Y|
    |GaussianTimeProcess.process R Y|
  simp only [sub_self,abs_zero] at hm
  rw [max_eq_left (abs_nonneg
    (|GaussianTimeProcess.process t Y|-|GaussianTimeProcess.process s Y|))] at hm
  have ha := abs_abs_sub_abs_le_abs_sub (GaussianTimeProcess.process t Y)
    (GaussianTimeProcess.process s Y)
  have hb : |overlap R Y t-overlap R Y s| ≤
      |GaussianTimeProcess.process t Y-GaussianTimeProcess.process s Y| := hm.trans ha
  nlinarith [sq_abs (overlap R Y t-overlap R Y s),
    sq_abs (GaussianTimeProcess.process t Y-GaussianTimeProcess.process s Y),
    abs_nonneg (overlap R Y t-overlap R Y s),
    abs_nonneg (GaussianTimeProcess.process t Y-GaussianTimeProcess.process s Y)]

def clockSquares (h : ℝ≥0) (n : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i ∈ Finset.range n,
    (GaussianTimeProcess.process (grid h (i+1)) Y-GaussianTimeProcess.process (grid h i) Y)^2

private theorem increment_sq_integrable (s t : ℝ≥0) :
    Integrable (fun Y => (GaussianTimeProcess.process t Y-GaussianTimeProcess.process s Y)^2)
      gaussianProduct :=
  ((GaussianTimeProcess.process_memLp t 2 (by norm_num)).sub
    (GaussianTimeProcess.process_memLp s 2 (by norm_num))).integrable_sq

private theorem increment_sq_mean (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ Y, (GaussianTimeProcess.process t Y-GaussianTimeProcess.process s Y)^2
      ∂gaussianProduct) = (t:ℝ)-s := by
  let f := GaussianTimeProcess.wienerL2 t-GaussianTimeProcess.wienerL2 s
  calc
    _ = ∫ Y, inner ℝ (f Y) (f Y) ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (GaussianTimeProcess.wienerL2 t)
        (GaussianTimeProcess.wienerL2 s)] with Y hY
      change f Y = GaussianTimeProcess.process t Y-GaussianTimeProcess.process s Y at hY
      rw [hY,Real.inner_apply]
      ring
    _ = ‖f‖^2 := (L2_inner_eq_integral f f).symm.trans (real_inner_self_eq_norm_sq f)
    _ = _ := GaussianTimeProcess.wienerL2_sub_norm_sq s t hst

theorem clockSquares_integrable (h : ℝ≥0) (n : ℕ) : Integrable (clockSquares h n) gaussianProduct :=
  integrable_finset_sum _ fun i _ => increment_sq_integrable _ _

theorem clockSquares_mean (h : ℝ≥0) (n : ℕ) :
    (∫ Y, clockSquares h n Y ∂gaussianProduct) = (grid h n:ℝ) := by
  unfold clockSquares
  rw [integral_finset_sum _ (fun i _ => increment_sq_integrable _ _)]
  have hi (i : ℕ) : grid h i ≤ grid h (i+1) := by
    unfold grid
    gcongr
    exact_mod_cast Nat.le_succ i
  simp_rw [increment_sq_mean _ _ (hi _)]
  rw [Finset.sum_range_sub (fun i => (grid h i:ℝ)) n]
  simp [grid]

theorem overlapEnergy_bounds (h : ℝ≥0) (n : ℕ) (R : ℝ≥0) (Y : SampleSpace) :
    -clockSquares h n Y ≤ overlapEnergy h n R Y ∧
      overlapEnergy h n R Y ≤ (GaussianTimeProcess.process (grid h n) Y)^2 := by
  have hq : (∑ i ∈ Finset.range n,
      (overlap R Y (grid h (i+1))-overlap R Y (grid h i))^2) ≤ clockSquares h n Y :=
    Finset.sum_le_sum fun i _ => overlap_increment_bound R _ _ Y
  have hm : (overlap R Y (grid h n))^2 ≤ (GaussianTimeProcess.process (grid h n) Y)^2 := by
    have hp : 0 ≤ overlap R Y (grid h n) := le_min (abs_nonneg _) (abs_nonneg _)
    have hl : overlap R Y (grid h n) ≤ |GaussianTimeProcess.process (grid h n) Y| := min_le_left _ _
    nlinarith [sq_abs (GaussianTimeProcess.process (grid h n) Y)]
  have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range n) =>
    sq_nonneg (overlap R Y (grid h (i+1))-overlap R Y (grid h i)))
  unfold overlapEnergy
  constructor <;> nlinarith [sq_nonneg (overlap R Y (grid h n))]

theorem observable_pairing_bounds (h : ℝ≥0) (n : ℕ) (R : ℝ≥0) :
    -(grid h n:ℝ) ≤ inner ℝ (jointDivergence (gridInput h n)) (squareObservation R) ∧
      inner ℝ (jointDivergence (gridInput h n)) (squareObservation R) ≤ (grid h n:ℝ) := by
  rw [observable_pairing]
  have hlo := integral_mono_ae (clockSquares_integrable h n).neg
    (overlapEnergy_integrable h n R) (ae_of_all _ fun Y => (overlapEnergy_bounds h n R Y).1)
  simp only [Pi.neg_apply] at hlo
  rw [integral_neg,clockSquares_mean] at hlo
  have hs := (GaussianTimeProcess.process_memLp (grid h n) 2 (by norm_num)).integrable_sq
  have hhi := integral_mono_ae (overlapEnergy_integrable h n R) hs
    (ae_of_all _ fun Y => (overlapEnergy_bounds h n R Y).2)
  have he : (∫ Y, (GaussianTimeProcess.process (grid h n) Y)^2 ∂gaussianProduct) =
      (grid h n:ℝ) := by
    simpa only [pow_two,min_self] using GaussianTimeProcess.process_product_integral (grid h n) (grid h n)
  rw [he] at hhi
  exact ⟨hlo,hhi⟩

theorem own_terminal_pairing_nonneg (h : ℝ≥0) (n : ℕ) :
    0 ≤ inner ℝ (jointDivergence (gridInput h n)) (squareObservation (grid h n)) := by
  rw [observable_pairing]
  have hi : ∀ Y, (GaussianTimeProcess.process (grid h n) Y)^2-clockSquares h n Y ≤
      overlapEnergy h n (grid h n) Y := by
    intro Y
    have hq := Finset.sum_le_sum (s:=Finset.range n) fun i _ =>
      overlap_increment_bound (grid h n) (grid h i) (grid h (i+1)) Y
    simp only [overlapEnergy,overlap,min_self,sq_abs]
    change _ - clockSquares h n Y ≤ _
    exact sub_le_sub_left hq _
  have hm := integral_mono_ae
    (((GaussianTimeProcess.process_memLp (grid h n) 2 (by norm_num)).integrable_sq).sub
      (clockSquares_integrable h n)) (overlapEnergy_integrable h n (grid h n)) (ae_of_all _ hi)
  simp only [Pi.sub_apply] at hm
  rw [integral_sub ((GaussianTimeProcess.process_memLp (grid h n) 2 (by norm_num)).integrable_sq)
    (clockSquares_integrable h n),clockSquares_mean] at hm
  have he : (∫ Y, (GaussianTimeProcess.process (grid h n) Y)^2 ∂gaussianProduct) =
      (grid h n:ℝ) := by
    simpa only [pow_two,min_self] using GaussianTimeProcess.process_product_integral (grid h n) (grid h n)
  simpa only [he,sub_self] using hm

def clippedSquares (h : ℝ≥0) (n : ℕ) (R : ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∑ i ∈ Finset.range n, (overlap R Y (grid h (i+1))-overlap R Y (grid h i))^2

theorem clippedSquares_bounds (h : ℝ≥0) (n : ℕ) (R : ℝ≥0) (Y : SampleSpace) :
    0 ≤ clippedSquares h n R Y ∧ clippedSquares h n R Y ≤ clockSquares h n Y :=
  ⟨Finset.sum_nonneg fun _ _ => sq_nonneg _,
    Finset.sum_le_sum fun _ _ => overlap_increment_bound R _ _ Y⟩

private theorem overlap_measurable (R t : ℝ≥0) : Measurable (fun Y => overlap R Y t) :=
  (continuous_abs.measurable.comp (GaussianTimeProcess.process_stronglyMeasurable t).measurable).min
    (continuous_abs.measurable.comp (GaussianTimeProcess.process_stronglyMeasurable R).measurable)

theorem clippedSquares_integrable (h : ℝ≥0) (n : ℕ) (R : ℝ≥0) :
    Integrable (clippedSquares h n R) gaussianProduct := by
  have hm : Measurable (clippedSquares h n R) :=
    Finset.measurable_sum _ fun i _ => ((overlap_measurable R _).sub (overlap_measurable R _)).pow_const 2
  apply (clockSquares_integrable h n).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun Y => by
    rw [Real.norm_of_nonneg (clippedSquares_bounds h n R Y).1]
    exact (clippedSquares_bounds h n R Y).2

theorem own_terminal_pairing_reduction (h : ℝ≥0) (n : ℕ) :
    inner ℝ (jointDivergence (gridInput h n)) (squareObservation (grid h n)) =
      (grid h n:ℝ)-∫ Y, clippedSquares h n (grid h n) Y ∂gaussianProduct := by
  rw [observable_pairing]
  have he : overlapEnergy h n (grid h n) = fun Y =>
      (GaussianTimeProcess.process (grid h n) Y)^2-clippedSquares h n (grid h n) Y := by
    funext Y
    simp only [overlapEnergy,overlap,min_self,sq_abs,clippedSquares]
  rw [he,integral_sub ((GaussianTimeProcess.process_memLp (grid h n) 2 (by norm_num)).integrable_sq)
    (clippedSquares_integrable h n (grid h n))]
  congr 1
  simpa only [pow_two,min_self] using GaussianTimeProcess.process_product_integral (grid h n) (grid h n)

def nativeTerminalPairing (T : ℝ≥0) (N : ℕ) : ℝ :=
  inner ℝ (jointDivergence (gridInput (T/(N+1)) (N+1))) (squareObservation T)

def terminalClippedMean (T : ℝ≥0) (N : ℕ) : ℝ :=
  ∫ Y, clippedSquares (T/(N+1)) (N+1) T Y ∂gaussianProduct

private theorem uniform_endpoint (T : ℝ≥0) (N : ℕ) : grid (T/(N+1)) (N+1) = T := by
  unfold grid
  have hp : (N+1:ℝ≥0) ≠ 0 := by positivity
  simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ T hp

theorem nativeTerminalPairing_reduction (T : ℝ≥0) (N : ℕ) :
    nativeTerminalPairing T N = (T:ℝ)-terminalClippedMean T N := by
  have he := own_terminal_pairing_reduction (T/(N+1)) (N+1)
  simpa only [uniform_endpoint,nativeTerminalPairing,terminalClippedMean] using he

theorem nativeTerminalPairing_bounds (T : ℝ≥0) (N : ℕ) :
    0 ≤ nativeTerminalPairing T N ∧ nativeTerminalPairing T N ≤ T := by
  have hlo := own_terminal_pairing_nonneg (T/(N+1)) (N+1)
  have hhi := (observable_pairing_bounds (T/(N+1)) (N+1) T).2
  simpa only [uniform_endpoint,nativeTerminalPairing] using And.intro hlo hhi

theorem terminalClippedMean_bounds (T : ℝ≥0) (N : ℕ) :
    0 ≤ terminalClippedMean T N ∧ terminalClippedMean T N ≤ T := by
  have hb := nativeTerminalPairing_bounds T N
  rw [nativeTerminalPairing_reduction] at hb
  constructor <;> linarith

theorem nativeTerminalPairing_tendsto_iff (T : ℝ≥0) (L : ℝ) :
    Tendsto (nativeTerminalPairing T) atTop (𝓝 L) ↔
      Tendsto (terminalClippedMean T) atTop (𝓝 ((T:ℝ)-L)) := by
  constructor
  · intro h
    have ht := (tendsto_const_nhds (x:=(T:ℝ))).sub h
    apply ht.congr'
    exact Eventually.of_forall fun N => by
      change (T:ℝ)-nativeTerminalPairing T N = terminalClippedMean T N
      rw [nativeTerminalPairing_reduction]
      ring
  · intro h
    have ht := (tendsto_const_nhds (x:=(T:ℝ))).sub h
    have he : (T:ℝ)-((T:ℝ)-L) = L := by ring
    rw [he] at ht
    exact ht.congr' (Eventually.of_forall fun N => (nativeTerminalPairing_reduction T N).symm)

end OperatorDerivativeRewrite.Foundation.IBMRawGridObservableTests
