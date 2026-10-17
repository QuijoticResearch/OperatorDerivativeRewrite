import Foundation.GaussianShearSpectrum
import Foundation.ShearSpectralCentroid

/-! Complete lattice sums of the actual velocity Fourier coefficients,
reindexed using the verified spectrum and an antipodal angular partition. -/
noncomputable section
open Set
namespace OperatorDerivativeRewrite.Foundation.GaussianShearSectorMoments
open FiniteFourierDifferentialTrace FiniteFourierSynthesis GaussianFourierJets
open GaussianPeriodicHeat GaussianInfiniteShear GaussianFourierCoefficient
open GaussianShearFourierTail GaussianShearSpectrum
open ShearSpectralCentroid (sector)
set_option backward.isDefEq.respectTransparency false

def radius (k : Wave) : ℝ := ∑ i, (k i : ℝ)^2
def density (p : ℕ) (nu t : ℝ) (k : Wave) : ℝ :=
  (radius k)^p*∑ i : Fin 3,
    Complex.normSq (fourierCoefficient (fun x => (velocity nu t x i : ℂ)) k)
def masked (j : Fin 2) (p : ℕ) (nu t : ℝ) (k : Wave) : ℝ :=
  if sector k = j then density p nu t k else 0
def moment (j : Fin 2) (p : ℕ) (nu t : ℝ) : ℝ := ∑' k : Wave, masked j p nu t k
def plus : Wave := Pi.single 2 1
def minus : Wave := Pi.single 2 (-1)

theorem coefficient_energy (nu t : ℝ) (k : Wave) :
    (∑ i : Fin 3, Complex.normSq (fourierCoefficient (fun x => (velocity nu t x i : ℂ)) k)) =
      Complex.normSq (fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) k) := by
  classical
  apply Finset.sum_eq_single 0
  · intro i _ hi
    rw [other_component_zero nu t k i hi]
    simp
  · simp

theorem density_nonnegative (p : ℕ) (nu t : ℝ) (k : Wave) : 0 ≤ density p nu t k := by
  unfold density radius
  exact mul_nonneg (pow_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) _)
    (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _))

theorem axis_injective : Function.Injective axis := by
  intro m n h
  have hh := congrArg (fun k : Wave => k 1) h
  simpa [axis] using hh

theorem density_axis (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (m : ℤ) :
    density p nu t (axis m) = 4*bound (2*p) (2*(1+nu*t)) m := by
  rw [density, coefficient_energy, axis_all nu t hs]
  have hr : radius (axis m) = (m : ℝ)^2 := by simp [radius, axis, Fin.sum_univ_succ]
  have hn : Complex.normSq (2*(weight (1+nu*t) m : ℂ)) =
      4*(weight (1+nu*t) m)^2 := by
    simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
    ring
  rw [hr, hn, weight_square]
  unfold bound GaussianFourierCoefficient.weight
  rw [pow_mul, sq_abs]
  ring

theorem masked_axis (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (m : ℤ) :
    masked 0 p nu t (axis m) = 4*bound (2*p) (2*(1+nu*t)) m := by
  have hj : sector (axis m) = 0 := by simp [sector, axis]
  simp only [masked, hj, ite_true]
  exact density_axis p nu t hs m

theorem masked_zero_outside_axis (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t)
    (k : Wave) (hk : k ∉ range axis) : masked 0 p nu t k = 0 := by
  by_cases h2 : k 2 = 0
  · have h0 : k 0 ≠ 0 := by
      intro h0
      apply hk
      refine ⟨k 1, ?_⟩
      ext i
      fin_cases i <;> simp_all [axis]
    have hc : fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) k = 0 := by
      rw [coefficient_formula nu t hs]
      simp [spectrumFormula, h0]
    simp only [masked, density, coefficient_energy, hc, map_zero, mul_zero, ite_self]
  · simp [masked, sector, h2]

theorem sector_zero_summable (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Summable (masked 0 p nu t) := by
  have hc : Summable ((masked 0 p nu t) ∘ axis) := by
    change Summable (fun m : ℤ => masked 0 p nu t (axis m))
    simp_rw [masked_axis p nu t hs]
    exact (bound_summable (2*p) (2*(1+nu*t)) (by positivity)).mul_left 4
  exact (axis_injective.summable_iff (masked_zero_outside_axis p nu t hs)).mp hc

theorem sector_zero_exact (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    moment 0 p nu t = 4*∑' m : ℤ, bound (2*p) (2*(1+nu*t)) m := by
  have hsup : Function.support (masked 0 p nu t) ⊆ range axis := by
    intro k hk
    by_contra hn
    exact hk (masked_zero_outside_axis p nu t hs k hn)
  have he : (∑' m : ℤ, masked 0 p nu t (axis m)) = ∑' k : Wave, masked 0 p nu t k :=
    axis_injective.tsum_eq hsup
  rw [moment, ← he]
  simp_rw [masked_axis p nu t hs]
  exact tsum_mul_left

theorem plus_ne_minus : plus ≠ minus := by decide

theorem masked_plus (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    masked 1 p nu t plus = (amplitude nu t)^2/4 := by
  have hj : sector plus = 1 := by norm_num [sector, plus]
  rw [masked, if_pos hj, density, coefficient_energy]
  change (radius plus)^p*Complex.normSq
    (fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (Pi.single 2 1)) = _
  rw [transverse_plus_normSq nu t hs]
  simp [radius, plus, Fin.sum_univ_succ]

theorem masked_minus (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    masked 1 p nu t minus = (amplitude nu t)^2/4 := by
  have hj : sector minus = 1 := by norm_num [sector, minus]
  rw [masked, if_pos hj, density, coefficient_energy]
  change (radius minus)^p*Complex.normSq
    (fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (Pi.single 2 (-1))) = _
  rw [transverse_minus_normSq nu t hs]
  simp [radius, minus, Fin.sum_univ_succ]

theorem masked_one_outside (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t)
    (k : Wave) (hk : k ∉ ({plus, minus} : Finset Wave)) : masked 1 p nu t k = 0 := by
  classical
  have hne : k ≠ plus ∧ k ≠ minus := by simpa using hk
  by_cases h2 : k 2 = 0
  · simp [masked, sector, h2]
  · have hc : fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) k = 0 := by
      by_contra hn
      rcases (coefficient_nonzero_iff nu t hs k).mp hn with haxis | ⟨h0,h1,hp|hm⟩
      · exact h2 haxis.2
      · apply hne.1
        ext i
        fin_cases i <;> simp_all [plus]
      · apply hne.2
        ext i
        fin_cases i <;> simp_all [minus]
    simp only [masked, density, coefficient_energy, hc, map_zero, mul_zero, ite_self]

theorem sector_one_summable (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Summable (masked 1 p nu t) := by
  classical
  exact summable_of_ne_finset_zero (masked_one_outside p nu t hs)

theorem sector_one_exact (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    moment 1 p nu t = (amplitude nu t)^2/2 := by
  classical
  rw [moment, tsum_eq_sum (masked_one_outside p nu t hs)]
  simp [plus_ne_minus, masked_plus p nu t hs, masked_minus p nu t hs]
  ring

theorem masked_add (p : ℕ) (nu t : ℝ) (k : Wave) :
    masked 0 p nu t k+masked 1 p nu t k = density p nu t k := by
  by_cases h : k 2 = 0 <;> simp [masked, sector, h]

theorem density_summable (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Summable (density p nu t) := by
  have h := (sector_zero_summable p nu t hs).add (sector_one_summable p nu t hs)
  change Summable (fun k => masked 0 p nu t k+masked 1 p nu t k) at h
  simpa only [masked_add] using h

theorem total_moment_exact (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    (∑' k : Wave, density p nu t k) = moment 0 p nu t+moment 1 p nu t := by
  have he : (fun k => density p nu t k) = fun k => masked 0 p nu t k+masked 1 p nu t k :=
    funext (fun k => (masked_add p nu t k).symm)
  rw [he, (sector_zero_summable p nu t hs).tsum_add (sector_one_summable p nu t hs)]
  rfl

end OperatorDerivativeRewrite.Foundation.GaussianShearSectorMoments
