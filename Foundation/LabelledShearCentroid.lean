import Foundation.GaussianShearRayMoments

/-! A finite-sector centroid theorem for the actual shear under explicit
four-ray label compatibility. Geometry of a specific partition remains a hypothesis. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.LabelledShearCentroid
open FiniteFourierDifferentialTrace FiniteFourierSynthesis GaussianPeriodicHeat GaussianInfiniteShear
open GaussianShearFourierTail GaussianShearSpectrum GaussianShearSectorMoments GaussianShearCentroid
open GaussianShearRayMoments
variable {ι : Type*} [Fintype ι]
set_option backward.isDefEq.respectTransparency false

def Compatible (L : Fin 4 ↪ ι) (ρ : Wave → ι) : Prop :=
  (∀ m : ℤ, 0 < m → ρ (axis m) = L 0) ∧
  (∀ m : ℤ, m < 0 → ρ (axis m) = L 1) ∧ ρ plus = L 2 ∧ ρ minus = L 3

def partitionDensity (ρ : Wave → ι) (j : ι) (p : ℕ) (nu t : ℝ) (k : Wave) : ℝ := by
  classical
  exact if ρ k = j then density p nu t k else 0
def partitionMoment (ρ : Wave → ι) (p : ℕ) (nu t : ℝ) (j : ι) : ℝ :=
  ∑' k : Wave, partitionDensity ρ j p nu t k

theorem ray_summable (r : Fin 4) (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Summable (rayMask r p nu t) := by
  fin_cases r
  · change Summable (fun k : Wave => if 0 < k 1 then masked 0 p nu t k else 0)
    exact summable_filter _ (sector_zero_summable p nu t hs) _
  · change Summable (fun k : Wave => if k 1 < 0 then masked 0 p nu t k else 0)
    exact summable_filter _ (sector_zero_summable p nu t hs) _
  · change Summable (fun k : Wave => if k = plus then density p nu t k else 0)
    exact summable_filter _ (density_summable p nu t hs) _
  · change Summable (fun k : Wave => if k = minus then density p nu t k else 0)
    exact summable_filter _ (density_summable p nu t hs) _

theorem label_on_ray (L : Fin 4 ↪ ι) (ρ : Wave → ι) (hρ : Compatible L ρ)
    (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (r : Fin 4) (k : Wave)
    (hr : rayMask r p nu t k ≠ 0) : ρ k = L r := by
  have hc : fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) k ≠ 0 := by
    intro hc
    have hd : density p nu t k = 0 := by simp [density, coefficient_energy, hc]
    have hm : masked 0 p nu t k = 0 := by simp [masked, hd]
    fin_cases r <;> simp_all [rayMask]
  have hsp := (coefficient_nonzero_iff nu t hs k).mp hc
  fin_cases r
  · change (if 0 < k 1 then masked 0 p nu t k else 0) ≠ 0 at hr
    have hp : 0 < k 1 := by by_contra hn; simp [hn] at hr
    have ha : k 0 = 0 ∧ k 2 = 0 := by rcases hsp with ha | ⟨h0,h1,h2⟩; exact ha; omega
    have hk : k = axis (k 1) := by ext i; fin_cases i <;> simp_all [axis]
    rw [hk]
    exact hρ.1 (k 1) hp
  · change (if k 1 < 0 then masked 0 p nu t k else 0) ≠ 0 at hr
    have hp : k 1 < 0 := by by_contra hn; simp [hn] at hr
    have ha : k 0 = 0 ∧ k 2 = 0 := by rcases hsp with ha | ⟨h0,h1,h2⟩; exact ha; omega
    have hk : k = axis (k 1) := by ext i; fin_cases i <;> simp_all [axis]
    rw [hk]
    exact hρ.2.1 (k 1) hp
  · change (if k = plus then density p nu t k else 0) ≠ 0 at hr
    by_cases hk : k = plus
    · simpa [hk] using hρ.2.2.1
    · simp [hk] at hr
  · change (if k = minus then density p nu t k else 0) ≠ 0 at hr
    by_cases hk : k = minus
    · simpa [hk] using hρ.2.2.2
    · simp [hk] at hr

theorem partition_density_eq (L : Fin 4 ↪ ι) (ρ : Wave → ι) (hρ : Compatible L ρ)
    (p : ℕ) (hp : 0 < p) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : ι) (k : Wave) :
    partitionDensity ρ j p nu t k = FiniteRayCentroid.spread L (fun r => rayMask r p nu t k) j := by
  classical
  have he (r : Fin 4) : (if L r = j then rayMask r p nu t k else 0) =
      if ρ k = j then rayMask r p nu t k else 0 := by
    by_cases hr : rayMask r p nu t k = 0
    · simp [hr]
    · rw [label_on_ray L ρ hρ p nu t hs r k hr]
  unfold partitionDensity FiniteRayCentroid.spread
  simp_rw [he]
  by_cases hj : ρ k = j
  · simp only [if_pos hj]
    exact (rays_total p hp nu t hs k).symm
  · simp [hj]

theorem partition_moment_eq (L : Fin 4 ↪ ι) (ρ : Wave → ι) (hρ : Compatible L ρ)
    (p : ℕ) (hp : 0 < p) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : ι) :
    partitionMoment ρ p nu t j = FiniteRayCentroid.spread L (rayMoment p nu t) j := by
  by_cases hj : j ∈ Set.range L
  · obtain ⟨r,rfl⟩ := hj
    unfold partitionMoment
    simp only [partition_density_eq L ρ hρ p hp nu t hs, FiniteRayCentroid.spread_image, rayMoment]
  · rw [FiniteRayCentroid.spread_outside L (rayMoment p nu t) j hj]
    unfold partitionMoment
    have hz : partitionDensity ρ j p nu t = fun _ => 0 := by
      funext k
      rw [partition_density_eq L ρ hρ p hp nu t hs j k,
        FiniteRayCentroid.spread_outside L _ j hj]
    rw [hz]
    simp

theorem partition_summable (L : Fin 4 ↪ ι) (ρ : Wave → ι) (hρ : Compatible L ρ)
    (p : ℕ) (hp : 0 < p) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : ι) :
    Summable (partitionDensity ρ j p nu t) := by
  by_cases hj : j ∈ Set.range L
  · obtain ⟨r,rfl⟩ := hj
    change Summable (fun k => partitionDensity ρ (L r) p nu t k)
    simp_rw [partition_density_eq L ρ hρ p hp nu t hs, FiniteRayCentroid.spread_image]
    exact ray_summable r p nu t hs
  · have hz : partitionDensity ρ j p nu t = fun _ => 0 := by
      funext k
      rw [partition_density_eq L ρ hρ p hp nu t hs j k,
        FiniteRayCentroid.spread_outside L _ j hj]
    rw [hz]
    exact summable_zero

theorem partition_table (L : Fin 4 ↪ ι) (ρ : Wave → ι) (hρ : Compatible L ρ)
    (p : ℕ) (hp : 0 < p) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    partitionMoment ρ p nu t = FiniteRayCentroid.energy L (moment 0 p nu t/2) (moment 1 p nu t/2) := by
  funext j
  rw [partition_moment_eq L ρ hρ p hp nu t hs, ray_table p hp nu t hs]
  rfl

def partitionRatio (ρ : Wave → ι) (nu t : ℝ) : ℝ :=
  let E := partitionMoment ρ 1 nu t
  let D := partitionMoment ρ 2 nu t
  let T := ∑ j, E j
  let e : ι → ℝ := fun j => E j/T-1/(Fintype.card ι : ℝ)
  (∑ j, e j*D j/T)/(((∑ j, D j)/T)*(∑ j, (e j)^2))

theorem partitionRatio_eq (L : Fin 4 ↪ ι) (ρ : Wave → ι) (hρ : Compatible L ρ)
    (nu t : ℝ) (hs : 0 < 1+nu*t) :
    partitionRatio ρ nu t = FiniteRayCentroid.ratio L
      (moment 0 1 nu t/2) (moment 1 1 nu t/2) (moment 0 2 nu t/2) := by
  have he : moment 1 2 nu t = moment 1 1 nu t := by
    rw [sector_one_exact 2 nu t hs, sector_one_exact 1 nu t hs]
  unfold partitionRatio
  rw [partition_table L ρ hρ 1 (by omega) nu t hs,
    partition_table L ρ hρ 2 (by omega) nu t hs, he]
  dsimp only
  rw [FiniteRayCentroid.sum_energy, FiniteRayCentroid.sum_energy]
  simp only [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rfl

theorem partitionRatio_gt_one (L : Fin 4 ↪ ι) (ρ : Wave → ι) (hρ : Compatible L ρ)
    (nu t : ℝ) (hs : 0 < 1+nu*t) : 1 < partitionRatio ρ nu t := by
  rw [partitionRatio_eq L ρ hρ nu t hs]
  have hb := second_sector_positive 1 nu t hs
  have hba := enstrophy_order nu t hs
  have had := dissipation_order nu t hs
  apply FiniteRayCentroid.ratio_gt_one
  · positivity
  · linarith
  · linarith

theorem zero_energy_zero_dissipation (L : Fin 4 ↪ ι) (ρ : Wave → ι)
    (hρ : Compatible L ρ) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : ι)
    (hj : partitionMoment ρ 1 nu t j = 0) : partitionMoment ρ 2 nu t j = 0 := by
  by_cases hr : j ∈ Set.range L
  · obtain ⟨r,rfl⟩ := hr
    rw [partition_table L ρ hρ 1 (by omega) nu t hs] at hj
    change FiniteRayCentroid.spread L _ (L r) = 0 at hj
    rw [FiniteRayCentroid.spread_image] at hj
    have hb := second_sector_positive 1 nu t hs
    have ha := hb.trans (enstrophy_order nu t hs)
    fin_cases r <;> simp [FiniteRayCentroid.rays] at hj <;> linarith
  · rw [partition_moment_eq L ρ hρ 2 (by omega) nu t hs,
      FiniteRayCentroid.spread_outside L _ j hr]

/- Empty-sector centroids use the explicit zero-extension convention D/0 = 0.
The manuscript's quotient at an empty sector is otherwise undefined over the reals. -/
def zeroExtendedCentroid (ρ : Wave → ι) (nu t : ℝ) : ℝ :=
  let E := partitionMoment ρ 1 nu t
  let D := partitionMoment ρ 2 nu t
  let T := ∑ j, E j
  let e : ι → ℝ := fun j => E j/T-1/(Fintype.card ι : ℝ)
  (∑ j, e j*(D j/E j)*(E j/T))/(((∑ j, D j)/T)*(∑ j, (e j)^2))

theorem zeroExtendedCentroid_eq (L : Fin 4 ↪ ι) (ρ : Wave → ι)
    (hρ : Compatible L ρ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    zeroExtendedCentroid ρ nu t = partitionRatio ρ nu t := by
  unfold zeroExtendedCentroid partitionRatio
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : partitionMoment ρ 1 nu t j = 0
  · simp [hj, zero_energy_zero_dissipation L ρ hρ nu t hs j hj]
  · field_simp

theorem zeroExtendedCentroid_gt_one (L : Fin 4 ↪ ι) (ρ : Wave → ι)
    (hρ : Compatible L ρ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    1 < zeroExtendedCentroid ρ nu t := by
  rw [zeroExtendedCentroid_eq L ρ hρ nu t hs]
  exact partitionRatio_gt_one L ρ hρ nu t hs

end OperatorDerivativeRewrite.Foundation.LabelledShearCentroid
