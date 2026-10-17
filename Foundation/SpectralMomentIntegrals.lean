import Foundation.SpectralEnergyInterpolation
import Foundation.LpProducts

/-! Proper weighted spectral moments on arbitrary measure spaces. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.SpectralMomentIntegrals
set_option backward.isDefEq.respectTransparency false
private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def moment {α : Type*} [MeasurableSpace α] (μ : Measure α) (w a : α → ℝ) (n : ℕ) : ℝ :=
  ∫ x, (w x)^n*(a x)^2 ∂μ

theorem weight_bound (r : ℝ) (hr : 0≤r) (n : ℕ) (hn : n≤3) : r^n≤1+r^3 := by
  interval_cases n
  · norm_num
    positivity
  · simp only [pow_one]
    by_cases hh : r≤1
    · linarith [pow_nonneg hr 3]
    · have hg : 1≤r := le_of_lt (lt_of_not_ge hh)
      have h2 : r≤r^2 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hg)]
      nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hg)]
  · by_cases hh : r≤1
    · nlinarith [mul_nonneg (sub_nonneg.mpr hh) (by linarith : (0:ℝ)≤1+r), pow_nonneg hr 3]
    · have hg : 1≤r := le_of_lt (lt_of_not_ge hh)
      nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hg)]
  · linarith

theorem moment_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α) {w a : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (ha : AEStronglyMeasurable a μ)
    (hnn : ∀ᵐ x ∂μ, 0≤w x) (h0 : Integrable (fun x => (a x)^2) μ)
    (h3 : Integrable (fun x => (w x)^3*(a x)^2) μ) (n : ℕ) (hn : n≤3) :
    Integrable (fun x => (w x)^n*(a x)^2) μ := by
  apply (h0.add h3).mono' ((hw.pow n).mul (ha.pow 2))
  filter_upwards [hnn] with x hx
  change ‖(w x)^n*(a x)^2‖≤(a x)^2+(w x)^3*(a x)^2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx n) (sq_nonneg _))]
  calc
    (w x)^n*(a x)^2≤(1+(w x)^3)*(a x)^2 :=
      mul_le_mul_of_nonneg_right (weight_bound _ hx n hn) (sq_nonneg _)
    _=(a x)^2+(w x)^3*(a x)^2 := by ring

theorem moment_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α) (w a : α → ℝ)
    (hnn : ∀ᵐ x ∂μ, 0≤w x) (n : ℕ) : 0≤moment μ w a n := by
  apply integral_nonneg_of_ae
  filter_upwards [hnn] with x hx
  exact mul_nonneg (pow_nonneg hx n) (sq_nonneg _)

theorem kinetic_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α) (w a : α → ℝ) :
    0≤moment μ w a 0 := by
  unfold moment
  simp only [pow_zero, one_mul]
  exact integral_nonneg (fun x => sq_nonneg (a x))

theorem l2_product_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => f x*g x) μ :=
  mul_L2_integrable hf hg

theorem toLp_inner_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g)=∫ x, f x*g x ∂μ := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp only [Real.inner_apply]

theorem integral_cauchy_squared {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2≤(∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  have hh := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [toLp_inner_integral hf hg, toLp_inner_integral hf hf, toLp_inner_integral hg hg] at hh
  simpa only [pow_two] using hh

theorem amplitude_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {a : α → ℝ}
    (ha : AEStronglyMeasurable a μ) (h0 : Integrable (fun x => (a x)^2) μ) : MemLp a 2 μ :=
  (memLp_two_iff_integrable_sq ha).mpr h0

theorem weighted_memLp {α : Type*} [MeasurableSpace α] (μ : Measure α) {w a : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (ha : AEStronglyMeasurable a μ)
    (hnn : ∀ᵐ x ∂μ, 0≤w x) (h0 : Integrable (fun x => (a x)^2) μ)
    (h3 : Integrable (fun x => (w x)^3*(a x)^2) μ) : MemLp (fun x => w x*a x) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hw.mul ha)).mpr
  convert moment_integrable μ hw ha hnn h0 h3 2 (by norm_num) using 1
  ext x
  change (w x*a x)^2=(w x)^2*(a x)^2
  ring

theorem root_memLp {α : Type*} [MeasurableSpace α] (μ : Measure α) {w a : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (ha : AEStronglyMeasurable a μ)
    (hnn : ∀ᵐ x ∂μ, 0≤w x) (h0 : Integrable (fun x => (a x)^2) μ)
    (h3 : Integrable (fun x => (w x)^3*(a x)^2) μ) :
    MemLp (fun x => Real.sqrt (w x)*a x) 2 μ := by
  apply (memLp_two_iff_integrable_sq ((Real.continuous_sqrt.comp_aestronglyMeasurable hw).mul ha)).mpr
  apply (moment_integrable μ hw ha hnn h0 h3 1 (by norm_num)).congr
  filter_upwards [hnn] with x hx
  change (w x)^1*(a x)^2=(Real.sqrt (w x)*a x)^2
  rw [mul_pow, Real.sq_sqrt hx, pow_one]

theorem weighted_root_memLp {α : Type*} [MeasurableSpace α] (μ : Measure α) {w a : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (ha : AEStronglyMeasurable a μ)
    (hnn : ∀ᵐ x ∂μ, 0≤w x) (h3 : Integrable (fun x => (w x)^3*(a x)^2) μ) :
    MemLp (fun x => w x*(Real.sqrt (w x)*a x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (hw.mul ((Real.continuous_sqrt.comp_aestronglyMeasurable hw).mul ha))).mpr
  apply h3.congr
  filter_upwards [hnn] with x hx
  change (w x)^3*(a x)^2=(w x*(Real.sqrt (w x)*a x))^2
  simp only [mul_pow, Real.sq_sqrt hx]
  ring

theorem cauchy_zero {α : Type*} [MeasurableSpace α] (μ : Measure α) {w a : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (ha : AEStronglyMeasurable a μ)
    (hnn : ∀ᵐ x ∂μ, 0≤w x) (h0 : Integrable (fun x => (a x)^2) μ)
    (h3 : Integrable (fun x => (w x)^3*(a x)^2) μ) :
    (moment μ w a 1)^2≤moment μ w a 0*moment μ w a 2 := by
  have hh := integral_cauchy_squared (amplitude_memLp ha h0) (weighted_memLp μ hw ha hnn h0 h3)
  have he : (fun x => a x*(w x*a x))=(fun x => w x*(a x)^2) := by ext x; ring
  have hq : (fun x => (w x*a x)^2)=(fun x => (w x)^2*(a x)^2) := by ext x; ring
  rw [he, hq] at hh
  simpa only [moment, pow_one, pow_zero, one_mul] using hh

theorem cauchy_one {α : Type*} [MeasurableSpace α] (μ : Measure α) {w a : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (ha : AEStronglyMeasurable a μ)
    (hnn : ∀ᵐ x ∂μ, 0≤w x) (h0 : Integrable (fun x => (a x)^2) μ)
    (h3 : Integrable (fun x => (w x)^3*(a x)^2) μ) :
    (moment μ w a 2)^2≤moment μ w a 1*moment μ w a 3 := by
  have hh := integral_cauchy_squared (root_memLp μ hw ha hnn h0 h3) (weighted_root_memLp μ hw ha hnn h3)
  have hp : (∫ x, (Real.sqrt (w x)*a x)*(w x*(Real.sqrt (w x)*a x)) ∂μ)=moment μ w a 2 := by
    apply integral_congr_ae
    filter_upwards [hnn] with x hx
    have hs := Real.sq_sqrt hx
    calc
      _=w x*(Real.sqrt (w x))^2*(a x)^2 := by ring
      _=(w x)^2*(a x)^2 := by rw [hs]; ring
  have he : (∫ x, (Real.sqrt (w x)*a x)^2 ∂μ)=moment μ w a 1 := by
    apply integral_congr_ae
    filter_upwards [hnn] with x hx
    simp only [mul_pow, Real.sq_sqrt hx, pow_one]
  have hd : (∫ x, (w x*(Real.sqrt (w x)*a x))^2 ∂μ)=moment μ w a 3 := by
    apply integral_congr_ae
    filter_upwards [hnn] with x hx
    simp only [mul_pow, Real.sq_sqrt hx]
    ring
  rw [hp, he, hd] at hh
  exact hh

theorem cubic_of_two_cauchy {K E Q D : ℝ} (hK : 0≤K) (hE : 0≤E) (hQ : 0≤Q) (hD : 0≤D)
    (h0 : E^2≤K*Q) (h1 : Q^2≤E*D) : E^3≤K^2*D := by
  by_cases hz : E=0
  · rw [hz]
    simpa using mul_nonneg (sq_nonneg K) hD
  · have hp : 0<E := lt_of_le_of_ne hE (Ne.symm hz)
    have hs := (sq_le_sq₀ (sq_nonneg E) (mul_nonneg hK hQ)).mpr h0
    have hm := mul_le_mul_of_nonneg_left h1 (sq_nonneg K)
    have hh : E*E^3≤E*(K^2*D) := by nlinarith [hs, hm]
    exact le_of_mul_le_mul_of_pos_left hh hp

theorem cubic_interpolation {α : Type*} [MeasurableSpace α] (μ : Measure α) {w a : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (ha : AEStronglyMeasurable a μ)
    (hnn : ∀ᵐ x ∂μ, 0≤w x) (h0 : Integrable (fun x => (a x)^2) μ)
    (h3 : Integrable (fun x => (w x)^3*(a x)^2) μ) :
    (moment μ w a 1)^3≤(moment μ w a 0)^2*moment μ w a 3 :=
  cubic_of_two_cauchy (kinetic_nonneg μ w a) (moment_nonneg μ w a hnn 1)
    (moment_nonneg μ w a hnn 2) (moment_nonneg μ w a hnn 3)
    (cauchy_zero μ hw ha hnn h0 h3) (cauchy_one μ hw ha hnn h0 h3)

theorem frequency_lower {α : Type*} [MeasurableSpace α] (μ : Measure α) {w a : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (ha : AEStronglyMeasurable a μ)
    (hnn : ∀ᵐ x ∂μ, 0≤w x) (h0 : Integrable (fun x => (a x)^2) μ)
    (h3 : Integrable (fun x => (w x)^3*(a x)^2) μ) (hE : 0<moment μ w a 1) :
    moment μ w a 1≤moment μ w a 0*Real.sqrt (moment μ w a 3/moment μ w a 1) :=
  SpectralEnergyInterpolation.energy_le_kinetic_mul_frequency (kinetic_nonneg μ w a) hE
    (moment_nonneg μ w a hnn 3) (cubic_interpolation μ hw ha hnn h0 h3)

theorem derivative_moment_identity {α : Type*} [MeasurableSpace α] (μ : Measure α) (w a : α → ℝ) :
    moment μ w (fun x => w x*a x) 1=moment μ w a 3 := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp only [pow_one]; ring)

theorem derivative_weight_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w a : α → ℝ} (h3 : Integrable (fun x => (w x)^3*(a x)^2) μ) :
    Integrable (fun x => w x*(w x*a x)^2) μ := by
  convert h3 using 1
  ext x
  ring

theorem energy_bound_from_caps {α : Type*} [MeasurableSpace α] (μ : Measure α) {w a : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (ha : AEStronglyMeasurable a μ)
    (hnn : ∀ᵐ x ∂μ, 0≤w x) (h0 : Integrable (fun x => (a x)^2) μ)
    (h3 : Integrable (fun x => (w x)^3*(a x)^2) μ) (hE : 0<moment μ w a 1)
    (B L : ℝ) (hK : moment μ w a 0≤B) (hL : 0≤L)
    (hfreq : Real.sqrt (moment μ w a 3/moment μ w a 1)≤L) : moment μ w a 1≤B*L :=
  SpectralEnergyInterpolation.energy_bound_from_caps (kinetic_nonneg μ w a) hE
    (moment_nonneg μ w a hnn 3) (cubic_interpolation μ hw ha hnn h0 h3) hK hL hfreq

theorem no_measure_profile_with_bounded_kinetic {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w a : ℝ → α → ℝ) (B : ℝ)
    (hw : ∀ t∈Ico (0:ℝ) 1, AEStronglyMeasurable (w t) μ)
    (ha : ∀ t∈Ico (0:ℝ) 1, AEStronglyMeasurable (a t) μ)
    (hnn : ∀ t∈Ico (0:ℝ) 1, ∀ᵐ x ∂μ, 0≤w t x)
    (h0 : ∀ t∈Ico (0:ℝ) 1, Integrable (fun x => (a t x)^2) μ)
    (h3 : ∀ t∈Ico (0:ℝ) 1, Integrable (fun x => (w t x)^3*(a t x)^2) μ)
    (hK : ∀ t∈Ico (0:ℝ) 1, moment μ (w t) (a t) 0≤B)
    (hE : ∀ t∈Ico (0:ℝ) 1, moment μ (w t) (a t) 1=CorridorFiniteTimeExit.energy t)
    (hD : ∀ t∈Ico (0:ℝ) 1, moment μ (w t) (a t) 3=CorridorFiniteTimeExit.dissipation t) : False := by
  apply SpectralEnergyInterpolation.profile_no_bounded_kinetic_interpolation
    (fun t => moment μ (w t) (a t) 0) B
  · intro t ht
    exact ⟨kinetic_nonneg μ (w t) (a t), hK t ht⟩
  · intro t ht
    have hh := cubic_interpolation μ (hw t ht) (ha t ht) (hnn t ht) (h0 t ht) (h3 t ht)
    rwa [hE t ht, hD t ht] at hh

end OperatorDerivativeRewrite.Foundation.SpectralMomentIntegrals
