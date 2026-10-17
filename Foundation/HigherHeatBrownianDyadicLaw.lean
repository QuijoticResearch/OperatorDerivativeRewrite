import Foundation.HigherHeatBrownianSource

/-! The actual continuous Brownian source has exactly the order-two dyadic position laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatBrownianDyadicLaw
open InfiniteGaussian IBMConstructedSources HigherHeatBrownianSource HigherHeatDyadicLaws
open HigherHeatContinuousCylinders HigherHeatCylinderFourier HigherHeatGaussianConfigurations
attribute [local irreducible] IBMConstructedSources.clockPath

theorem cumulative_steps (N : ℕ) (g : ℕ → ℝ) (i : Fin N) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ≤ i), (g (j.val+1)-g j.val))=g (i.val+1)-g 0 := by
  classical
  have ht (r : ℕ) : (∑ k ∈ Finset.range r, (g (k+1)-g k))=g r-g 0 := by
    induction r with
    | zero => simp
    | succ r ih => rw [Finset.sum_range_succ,ih]; ring
  calc
    (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ≤ i), (g (j.val+1)-g j.val)) =
        ∑ k ∈ Finset.range (i.val+1), (g (k+1)-g k) := by
      apply Finset.sum_bij (fun j _ => j.val)
      · intro j hj
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (show j.val ≤ i.val from (Finset.mem_filter.mp hj).2))
      · intro j hj k hk h
        exact Fin.ext h
      · intro k hk
        have hk' : k < i.val+1 := Finset.mem_range.mp hk
        refine ⟨⟨k,by omega⟩,?_,rfl⟩
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        change k ≤ i.val
        omega
      · intro j hj
        rfl
    _ = g (i.val+1)-g 0 := ht _

theorem cumulative_increment (N : ℕ) (s : ℝ≥0) (ω : SampleSpace) (i : Fin N) :
    linearImage (cumulativeMatrix N) (fun j => increment N s j ω) i =
      clockPath ω (((i.val+1 : ℕ) : ℝ≥0)*(2*s))-clockPath ω 0 := by
  rw [cumulative_apply]
  have h := cumulative_steps N (fun k => clockPath ω ((k : ℝ≥0)*(2*s))) i
  simpa only [increment,Nat.cast_zero,zero_mul] using h

theorem sample_source (T : ℝ≥0) (n : ℕ) (ω : SampleSpace) (i : Fin (gridSize n)) :
    sample n (sourcePath T ω) i =
      clockPath ω (((i.val+1 : ℕ) : ℝ≥0)*(2*duration T n))-clockPath ω 0 := by
  change clockPath ω ((2*T)*(sampleTime n i).toNNReal)-clockPath ω 0 = _
  have ht : (sampleTime n i).toNNReal=HigherHeatDyadicLaws.time 1 n i := by
    rw [sampleTime,Real.toNNReal_coe]
  have he : (2*T)*HigherHeatDyadicLaws.time 1 n i =
      ((i.val+1 : ℕ) : ℝ≥0)*(2*duration T n) := by
    simp only [HigherHeatDyadicLaws.time,duration,div_eq_mul_inv]
    ring
  rw [ht,he]

theorem source_samples_eq (T : ℝ≥0) (n : ℕ) (ω : SampleSpace) :
    sample n (sourcePath T ω)=linearImage (cumulativeMatrix (gridSize n))
      (fun j => increment (gridSize n) (duration T n) j ω) := by
  funext i
  rw [sample_source,cumulative_increment]

theorem sample_hasLaw (T : ℝ≥0) (n : ℕ) :
    HasLaw (fun ω : SampleSpace => sample n (sourcePath T ω))
      (gaussianPositions (gridSize n) (fun _ => duration T n)) gaussianProduct := by
  have hc : HasLaw (linearImage (cumulativeMatrix (gridSize n)))
      (gaussianPositions (gridSize n) (fun _ => duration T n))
      (gaussianIncrements (fun _ : Fin (gridSize n) => duration T n)) :=
    ⟨(linearImage_measurable _).aemeasurable,rfl⟩
  have he : (fun ω : SampleSpace => sample n (sourcePath T ω)) =
      fun ω => linearImage (cumulativeMatrix (gridSize n))
        (fun j => increment (gridSize n) (duration T n) j ω) := funext (source_samples_eq T n)
  rw [he]
  exact hc.comp (increments_hasLaw (gridSize n) (duration T n))

theorem sourceMeasure_samples (T : ℝ≥0) (n : ℕ) :
    (sourceMeasure T).map (sample n)=gaussianPositions (gridSize n) (fun _ => duration T n) := by
  rw [sourceMeasure,Measure.map_map (sample_continuous n).measurable (sourcePath_measurable T)]
  exact (sample_hasLaw T n).map_eq

set_option backward.isDefEq.respectTransparency false in
theorem sourceMeasure_signed_samples (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (sourceMeasure T).toSignedMeasure.map (sample n)=HigherHeatDyadicLaws.law 1 (by norm_num) T hT n := by
  rw [map_toSigned _ _ (sample_continuous n).measurable]
  simpa only [sourceMeasure_samples,HigherHeatDyadicLaws.law,Grid] using
    (position_gaussian (gridSize n) (fun _ => duration T n) (fun _ => duration_pos T hT n)).symm

end OperatorDerivativeRewrite.Foundation.HigherHeatBrownianDyadicLaw
