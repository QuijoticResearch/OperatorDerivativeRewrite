import Foundation.RiemannEvenNaturalContour
/-! Exact degree-independent assembly of actual integer-even horizontal integrals.
All finite interval orientations and the right-tail domain remain explicit. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenHorizontalDecomposition
open RiemannEvenComplexWeight RiemannEvenNaturalContour

theorem horizontal_decomposition (m : ℕ) (t : ℝ) (z v : ℂ) (hh : |v.im| < Real.pi/8) (R : ℝ)
    (hRight : IntegrableOn (fun s : ℝ => weight m t z (v+(s : ℂ))) (Ioi R)) :
    (∫ s : ℝ in Ioi 0, weight m t z ((s : ℂ)+(v.im : ℂ)*Complex.I))=
      (∫ s : ℝ in 0..v.re-1, weight m t z ((s : ℂ)+(v.im : ℂ)*Complex.I))+
      (∫ s : ℝ in -1..-R, weight m t z (v+(s : ℂ)))+
      (∫ s : ℝ in -R..R, weight m t z (v+(s : ℂ)))+
      (∫ s : ℝ in Ioi R, weight m t z (v+(s : ℂ))) := by
  let a := v.re
  let F := fun s : ℝ => weight m t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let f := fun s : ℝ => weight m t z (v+(s : ℂ))
  have hfun : f=(fun s : ℝ => F (s+a)) := by
    funext s
    dsimp [f,F,a]
    rw [Complex.ofReal_add]
    congr 1
    apply Complex.ext <;> simp <;> ring
  have hc : Continuous f := by
    rw [hfun]
    exact (shifted_weight_continuous m t z v.im hh).comp (continuous_id.add_const a)
  have hIndicator : (fun s : ℝ => (Ioi (0 : ℝ)).indicator F (s+a))=(Ioi (-a)).indicator f := by
    funext s
    by_cases h : s ∈ Ioi (-a)
    · have h' : s+a ∈ Ioi (0 : ℝ) := by change -a < s at h; change 0 < s+a; linarith
      rw [indicator_of_mem h',indicator_of_mem h]
      exact (congrFun hfun s).symm
    · have h' : s+a ∉ Ioi (0 : ℝ) := by
        intro h'
        apply h
        change -a < s
        change 0 < s+a at h'
        linarith
      rw [indicator_of_notMem h',indicator_of_notMem h]
  have hshift : (∫ s : ℝ, (Ioi (0 : ℝ)).indicator F (s+a)) =
      (∫ s : ℝ, (Ioi (0 : ℝ)).indicator F s) :=
    integral_add_right_eq_self (fun s : ℝ => (Ioi (0 : ℝ)).indicator F s) a
  rw [hIndicator] at hshift
  simp only [integral_indicator measurableSet_Ioi] at hshift
  have hfirst : (∫ s : ℝ in -a..-1, f s)=(∫ s : ℝ in 0..a-1, F s) := by
    rw [hfun]
    have h := intervalIntegral.integral_comp_add_right (a := -a) (b := (-1 : ℝ)) F a
    simpa only [neg_add_cancel,show (-1 : ℝ)+a=a-1 by ring] using h
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) (-a) (-1)) (hc.intervalIntegrable (μ := volume) (-1) (-R))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) (-a) (-R)) (hc.intervalIntegrable (μ := volume) (-R) R)
  have h3 := intervalIntegral.integral_interval_add_Ioi' (hc.intervalIntegrable (μ := volume) (-a) R) hRight
  change (∫ s : ℝ in Ioi 0, F s)=(∫ s : ℝ in 0..a-1, F s)+
    (∫ s : ℝ in -1..-R, f s)+(∫ s : ℝ in -R..R, f s)+(∫ s : ℝ in Ioi R, f s)
  linear_combination -hshift-h3-h2-h1+hfirst



theorem neighborhood_decomposition (m : ℕ) (t : ℝ) (z v : ℂ)
    (hh : |v.im| < Real.pi/8) (r R : ℝ) (hr0 : 0 ≤ r) (hrR : r ≤ R) :
    (∫ s : ℝ in -R..R, weight m t z (v+(s : ℂ)))=
      (∫ s : ℝ in -r..r, weight m t z (v+(s : ℂ)))+
      (∫ s : ℝ in r..R, weight m t z (v+((-s : ℝ) : ℂ)))+
      (∫ s : ℝ in r..R, weight m t z (v+(s : ℂ))) := by
  let f := fun s : ℝ => weight m t z (v+(s : ℂ))
  let F := fun s : ℝ => weight m t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  have hfun : f=(fun s : ℝ => F (s+v.re)) := by
    funext s
    dsimp [f,F]
    rw [Complex.ofReal_add]
    congr 1
    apply Complex.ext <;> simp <;> ring
  have hc : Continuous f := by
    rw [hfun]
    exact (shifted_weight_continuous m t z v.im hh).comp (continuous_id.add_const v.re)
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-R) (-r)) (hc.intervalIntegrable (μ := volume) (-r) r)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-R) r) (hc.intervalIntegrable (μ := volume) r R)
  have hneg := intervalIntegral.integral_comp_neg (a := r) (b := R) f
  change (∫ s : ℝ in -R..R, f s)=(∫ s : ℝ in -r..r, f s)+
    (∫ s : ℝ in r..R, f (-s))+(∫ s : ℝ in r..R, f s)
  linear_combination -h2-h1-hneg

end OperatorDerivativeRewrite.Foundation.RiemannEvenHorizontalDecomposition
