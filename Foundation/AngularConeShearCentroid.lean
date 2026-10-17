import Foundation.GaussianShearCentroid

/-! Transfer the complete lattice calculation to an antipodal conic angular
partition. No particular manuscript tessellation is assumed to coincide with it. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.AngularConeShearCentroid
open FiniteFourierDifferentialTrace FiniteFourierSynthesis GaussianPeriodicHeat
open GaussianInfiniteShear GaussianShearFourierTail GaussianShearSpectrum
open GaussianShearSectorMoments GaussianShearCentroid
open ShearSpectralCentroid (sector)
set_option backward.isDefEq.respectTransparency false

def angularSector (k : Wave) : Fin 2 := if |k 2| ≤ |k 1| then 0 else 1
def angularMasked (j : Fin 2) (p : ℕ) (nu t : ℝ) (k : Wave) : ℝ :=
  if angularSector k = j then density p nu t k else 0
def angularMoment (j : Fin 2) (p : ℕ) (nu t : ℝ) : ℝ := ∑' k : Wave, angularMasked j p nu t k

theorem angular_antipodal (k : Wave) : angularSector (-k) = angularSector k := by
  simp [angularSector, Pi.neg_apply]

theorem angular_scale (q : ℤ) (hq : 0 < q) (k : Wave) :
    angularSector (fun i => q*k i) = angularSector k := by
  simp [angularSector, abs_mul, abs_of_pos hq, mul_le_mul_iff_right₀ hq]

theorem label_on_spectrum (nu t : ℝ) (hs : 0 < 1+nu*t) (k : Wave)
    (hc : fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) k ≠ 0) :
    angularSector k = sector k := by
  rcases (coefficient_nonzero_iff nu t hs k).mp hc with haxis | ⟨h0,h1,hp|hm⟩
  · simp [angularSector, sector, haxis.2]
  · simp [angularSector, sector, h1, hp]
  · simp [angularSector, sector, h1, hm]

theorem masked_transfer (j : Fin 2) (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (k : Wave) :
    angularMasked j p nu t k = masked j p nu t k := by
  by_cases hc : fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) k = 0
  · simp [angularMasked, masked, density, coefficient_energy, hc]
  · simp only [angularMasked, masked, label_on_spectrum nu t hs k hc]

theorem moment_transfer (j : Fin 2) (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    angularMoment j p nu t = moment j p nu t := by
  unfold angularMoment moment
  simp only [masked_transfer j p nu t hs]

theorem angular_summable (j : Fin 2) (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Summable (angularMasked j p nu t) := by
  have h : Summable (masked j p nu t) := by
    fin_cases j
    · exact sector_zero_summable p nu t hs
    · exact sector_one_summable p nu t hs
  exact h.congr (fun k => (masked_transfer j p nu t hs k).symm)

def angularCentroid (nu t : ℝ) : ℝ := sourceExpression
  (angularMoment 0 1 nu t) (angularMoment 1 1 nu t)
  (angularMoment 0 2 nu t) (angularMoment 1 2 nu t)

theorem angularCentroid_eq (nu t : ℝ) (hs : 0 < 1+nu*t) :
    angularCentroid nu t = sourceCentroid nu t := by
  unfold angularCentroid sourceCentroid
  simp only [moment_transfer _ _ nu t hs]

theorem angularCentroid_gt_one (nu t : ℝ) (hnu : 0 ≤ nu) (ht : 0 ≤ t) :
    1 < angularCentroid nu t := by
  have hs := positive_parameter nu t hnu ht
  rw [angularCentroid_eq nu t hs]
  exact sourceCentroid_gt_one nu t hs

theorem no_initial_interval_below_one (nu : ℝ) (hnu : 0 ≤ nu) :
    ¬ ∃ T : ℝ, 0 < T ∧ ∀ t, 0 < t → t ≤ T → angularCentroid nu t < 1 := by
  rintro ⟨T,hT,hbelow⟩
  have h := hbelow (T/2) (by positivity) (by linarith)
  have hg := angularCentroid_gt_one nu (T/2) hnu (by positivity)
  linarith

end OperatorDerivativeRewrite.Foundation.AngularConeShearCentroid
