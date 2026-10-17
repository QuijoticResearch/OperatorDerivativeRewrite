import Foundation.FiniteRayCentroid

/-! Actual lattice moments on the four nonzero support rays. Symmetry splits
the Gaussian axis into equal halves; no ray energy is prescribed independently. -/
noncomputable section
open Set
namespace OperatorDerivativeRewrite.Foundation.GaussianShearRayMoments
open FiniteFourierDifferentialTrace FiniteFourierSynthesis GaussianFourierJets
open GaussianPeriodicHeat GaussianInfiniteShear GaussianShearFourierTail GaussianShearSpectrum
open GaussianShearSectorMoments
open ShearSpectralCentroid (sector)
set_option backward.isDefEq.respectTransparency false

theorem summable_filter {α : Type*} (f : α → ℝ) (hf : Summable f)
    (P : α → Prop) [DecidablePred P] : Summable (fun n => if P n then f n else 0) := by
  have he : {n | P n}.indicator f = fun n => if P n then f n else 0 := by
    funext n
    by_cases hn : P n <;> simp [hn]
  rw [← he]
  exact hf.indicator _

theorem even_half_sums (f : ℤ → ℝ) (hf : Summable f) (hzero : f 0 = 0)
    (heven : ∀ n, f (-n) = f n) :
    (∑' n : ℤ, if 0 < n then f n else 0) = (∑' n : ℤ, f n)/2 ∧
    (∑' n : ℤ, if n < 0 then f n else 0) = (∑' n : ℤ, f n)/2 := by
  have hp : Summable (fun n : ℤ => if 0 < n then f n else 0) := by
    exact summable_filter f hf (fun n => 0 < n)
  have hn : Summable (fun n : ℤ => if n < 0 then f n else 0) := by
    exact summable_filter f hf (fun n => n < 0)
  have hpoint (n : ℤ) : f n = (if 0 < n then f n else 0)+(if n < 0 then f n else 0) := by
    by_cases hp : 0 < n
    · simp [hp, not_lt_of_ge hp.le]
    · by_cases hn : n < 0
      · simp [hp, hn]
      · have hz : n = 0 := by omega
        simp [hz, hzero]
  have hsplit : (∑' n : ℤ, f n) =
      (∑' n : ℤ, if 0 < n then f n else 0)+(∑' n : ℤ, if n < 0 then f n else 0) := by
    calc
      _ = ∑' n : ℤ, ((if 0 < n then f n else 0)+(if n < 0 then f n else 0)) :=
        tsum_congr hpoint
      _ = _ := hp.tsum_add hn
  have heq : (∑' n : ℤ, if n < 0 then f n else 0) =
      ∑' n : ℤ, if 0 < n then f n else 0 := by
    calc
      _ = ∑' n : ℤ, if 0 < -n then f (-n) else 0 := by simp only [neg_pos, heven]
      _ = _ := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => if 0 < n then f n else 0)
  constructor <;> linarith

theorem axis_density_summable (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Summable (fun m : ℤ => density p nu t (axis m)) := by
  simp_rw [density_axis p nu t hs]
  exact (bound_summable (2*p) (2*(1+nu*t)) (by positivity)).mul_left 4

theorem axis_density_even (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (m : ℤ) :
    density p nu t (axis (-m)) = density p nu t (axis m) := by
  rw [density_axis p nu t hs, density_axis p nu t hs]
  simp [bound]

theorem axis_density_zero (p : ℕ) (hp : 0 < p) (nu t : ℝ) :
    density p nu t (axis 0) = 0 := by
  simp [density, radius, axis, Fin.sum_univ_succ, zero_pow (by omega : p ≠ 0)]

theorem axis_total (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    (∑' m : ℤ, density p nu t (axis m)) = moment 0 p nu t := by
  rw [sector_zero_exact p nu t hs]
  simp_rw [density_axis p nu t hs]
  exact tsum_mul_left

theorem filtered_axis (P : ℤ → Prop) [DecidablePred P] (p : ℕ) (nu t : ℝ)
    (hs : 0 < 1+nu*t) :
    (∑' k : Wave, if P (k 1) then masked 0 p nu t k else 0) =
      ∑' m : ℤ, if P m then density p nu t (axis m) else 0 := by
  have hsup : Function.support (fun k : Wave => if P (k 1) then masked 0 p nu t k else 0)
      ⊆ range axis := by
    intro k hk
    by_contra hn
    have hz := masked_zero_outside_axis p nu t hs k hn
    simp [hz] at hk
  have he := axis_injective.tsum_eq hsup
  have hj (m : ℤ) : sector (axis m) = 0 := by simp [sector, axis]
  have hc (m : ℤ) : (axis m) 1 = m := by simp [axis]
  simpa only [hc, masked, hj, ite_true] using he.symm

def rayMask (r : Fin 4) (p : ℕ) (nu t : ℝ) (k : Wave) : ℝ :=
  ![if 0 < k 1 then masked 0 p nu t k else 0,
    if k 1 < 0 then masked 0 p nu t k else 0,
    if k = plus then density p nu t k else 0,
    if k = minus then density p nu t k else 0] r
def rayMoment (p : ℕ) (nu t : ℝ) (r : Fin 4) : ℝ := ∑' k : Wave, rayMask r p nu t k

theorem ray_table (p : ℕ) (hp : 0 < p) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    rayMoment p nu t = FiniteRayCentroid.rays (moment 0 p nu t/2) (moment 1 p nu t/2) := by
  have hh := even_half_sums (fun m => density p nu t (axis m))
    (axis_density_summable p nu t hs) (axis_density_zero p hp nu t)
    (axis_density_even p nu t hs)
  rw [axis_total p nu t hs] at hh
  have hplus : density p nu t plus = (amplitude nu t)^2/4 := by
    have h := masked_plus p nu t hs
    have hj : sector plus = 1 := by norm_num [sector, plus]
    simpa only [masked, hj, ite_true] using h
  have hminus : density p nu t minus = (amplitude nu t)^2/4 := by
    have h := masked_minus p nu t hs
    have hj : sector minus = 1 := by norm_num [sector, minus]
    simpa only [masked, hj, ite_true] using h
  ext r
  fin_cases r
  · change (∑' k : Wave, if 0 < k 1 then masked 0 p nu t k else 0) = moment 0 p nu t/2
    rw [filtered_axis (fun n => 0 < n) p nu t hs]
    exact hh.1
  · change (∑' k : Wave, if k 1 < 0 then masked 0 p nu t k else 0) = moment 0 p nu t/2
    rw [filtered_axis (fun n => n < 0) p nu t hs]
    exact hh.2
  · change (∑' k : Wave, if k = plus then density p nu t k else 0) = moment 1 p nu t/2
    simp only [tsum_ite_eq, hplus, sector_one_exact p nu t hs]
    ring
  · change (∑' k : Wave, if k = minus then density p nu t k else 0) = moment 1 p nu t/2
    simp only [tsum_ite_eq, hminus, sector_one_exact p nu t hs]
    ring

theorem masked_axis_zero (p : ℕ) (hp : 0 < p) (nu t : ℝ) (hs : 0 < 1+nu*t)
    (k : Wave) (h1 : k 1 = 0) : masked 0 p nu t k = 0 := by
  by_cases h2 : k 2 = 0
  · by_cases h0 : k 0 = 0
    · have hk : k = 0 := by ext i; fin_cases i <;> simp_all
      subst k
      simp [masked, sector, density, radius, Fin.sum_univ_succ, zero_pow (by omega : p ≠ 0)]
    · have hc : fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) k = 0 := by
        rw [coefficient_formula nu t hs]
        simp [spectrumFormula, h0]
      simp [masked, density, coefficient_energy, hc]
  · simp [masked, sector, h2]

theorem rays_total (p : ℕ) (hp : 0 < p) (nu t : ℝ) (hs : 0 < 1+nu*t) (k : Wave) :
    (∑ r : Fin 4, rayMask r p nu t k) = density p nu t k := by
  have h0 : (if 0 < k 1 then masked 0 p nu t k else 0)+
      (if k 1 < 0 then masked 0 p nu t k else 0) = masked 0 p nu t k := by
    by_cases hpos : 0 < k 1
    · simp [hpos, not_lt_of_ge hpos.le]
    · by_cases hneg : k 1 < 0
      · simp [hpos, hneg]
      · have hz : k 1 = 0 := by omega
        simp [hpos, hneg, masked_axis_zero p hp nu t hs k hz]
  have h1 : (if k = plus then density p nu t k else 0)+
      (if k = minus then density p nu t k else 0) = masked 1 p nu t k := by
    by_cases hplus : k = plus
    · subst k
      simp [masked, sector, plus, minus]
    · by_cases hminus : k = minus
      · subst k
        simp [masked, sector, plus, minus]
      · have hn : k ∉ ({plus,minus} : Finset Wave) := by simp [hplus,hminus]
        simp [hplus,hminus,masked_one_outside p nu t hs k hn]
  change (if 0 < k 1 then masked 0 p nu t k else 0)+
    ((if k 1 < 0 then masked 0 p nu t k else 0)+
    ((if k = plus then density p nu t k else 0)+
    ((if k = minus then density p nu t k else 0)+0))) = _
  linarith [masked_add p nu t k]

end OperatorDerivativeRewrite.Foundation.GaussianShearRayMoments
