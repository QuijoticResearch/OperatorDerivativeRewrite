import Foundation.IBMSpatialIncrementKernel

/-! Finite spatial increment kernels concentrate near the diagonal.
The quantitative area estimate is in the original physical Lebesgue space. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialKernelConcentration
open IBMSpatialIncrementKernel

def band (M δ : ℝ) : Set (ℝ × ℝ) := {z | z.1 ∈ Icc 0 M ∧ |z.2-z.1| ≤ δ}

theorem band_measurable (M δ : ℝ) : MeasurableSet (band M δ) :=
  (measurableSet_Icc.preimage measurable_fst).inter
    (measurableSet_le (continuous_abs.measurable.comp (measurable_snd.sub measurable_fst)) measurable_const)

theorem band_fiber (M δ x : ℝ) :
    {y | (x,y) ∈ band M δ} = if x ∈ Icc 0 M then Icc (x-δ) (x+δ) else ∅ := by
  ext y
  by_cases hx : x ∈ Icc 0 M
  · rw [if_pos hx]
    change (x ∈ Icc 0 M ∧ |y-x| ≤ δ) ↔ x-δ ≤ y ∧ y ≤ x+δ
    rw [abs_le]
    constructor <;> intro h
    · exact ⟨by linarith [h.2.1],by linarith [h.2.2]⟩
    · exact ⟨hx,by constructor <;> linarith [h.1,h.2]⟩
  · rw [if_neg hx]
    change (x ∈ Icc 0 M ∧ |y-x| ≤ δ) ↔ False
    simp only [hx,false_and]

theorem band_measure (M δ : ℝ) :
    (volume.prod volume) (band M δ) = ENNReal.ofReal M*ENNReal.ofReal (2*δ) := by
  rw [Measure.prod_apply (band_measurable M δ)]
  change (∫⁻ x, volume {y | (x,y) ∈ band M δ} ∂volume) = _
  have he : (fun x => volume {y | (x,y) ∈ band M δ}) =
      (Icc 0 M).indicator (fun _ => ENNReal.ofReal (2*δ)) := by
    funext x
    rw [band_fiber]
    by_cases hx : x ∈ Icc 0 M
    · simp only [if_pos hx,indicator_of_mem hx,Real.volume_Icc]
      congr 1
      ring
    · simp [hx]
  rw [he,lintegral_indicator measurableSet_Icc]
  simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero]
  exact mul_comm _ _

theorem band_finite (M δ : ℝ) : (volume.prod volume) (band M δ) ≠ ∞ := by
  rw [band_measure]
  finiteness

theorem band_measure_real {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ) :
    (volume.prod volume).real (band M δ) = 2*M*δ := by
  rw [Measure.real,band_measure,ENNReal.toReal_mul,ENNReal.toReal_ofReal hM,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hδ)]
  ring

theorem kernel_zero_off_band (r : ℕ → ℝ) (n : ℕ) (M δ : ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ M)
    (hm : ∀ i < n, |r (i+1)-r i| ≤ δ) {z : ℝ × ℝ} (hz : z ∉ band M δ) :
    kernel r n z = 0 := by
  unfold kernel
  apply Finset.sum_eq_zero
  intro i hi
  apply indicator_of_notMem
  intro hx
  have hin := Finset.mem_range.mp hi
  have hr0 := hr i hin.le
  have hr1 := hr (i+1) hin
  change z.1 ∈ interval r i ∧ z.2 ∈ interval r i at hx
  simp only [interval,mem_Ioc] at hx
  have hlo : 0 ≤ min (r i) (r (i+1)) := le_min hr0.1 hr1.1
  have hhi : max (r i) (r (i+1)) ≤ M := max_le hr0.2 hr1.2
  have hwidth : max (r i) (r (i+1))-min (r i) (r (i+1)) ≤ δ := by
    have he := interval_measure r i
    rw [interval,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr min_le_max)] at he
    rw [he]
    exact hm i hin
  apply hz
  exact ⟨⟨by linarith [hx.1.1],by linarith [hx.1.2]⟩,
    abs_le.mpr ⟨by linarith [hx.1.1,hx.2.2],by linarith [hx.2.1,hx.1.2]⟩⟩

theorem mass_sq_le_area_energy (r : ℕ → ℝ) (n : ℕ) (M δ : ℝ)
    (hzero : ∀ z ∉ band M δ, kernel r n z = 0) :
    (∫ z, kernel r n z ∂(volume.prod volume))^2 ≤
      (volume.prod volume).real (band M δ)*(∫ z, (kernel r n z)^2 ∂(volume.prod volume)) := by
  let f := (kernel_memLp r n).toLp (kernel r n)
  let s : Lp ℝ 2 (volume.prod volume) := indicatorConstLp 2 (band_measurable M δ) (band_finite M δ) 1
  have hf : f =ᵐ[volume.prod volume] kernel r n := (kernel_memLp r n).coeFn_toLp
  have hs : s =ᵐ[volume.prod volume] (band M δ).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  have hp : inner ℝ f s = ∫ z, kernel r n z ∂(volume.prod volume) := by
    rw [L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [hf,hs] with z hfz hsz
    rw [hfz,hsz,Real.inner_apply]
    by_cases hz : z ∈ band M δ
    · simp [hz]
    · simp [hz,hzero z hz]
  have hfn : ‖f‖^2 = ∫ z, (kernel r n z)^2 ∂(volume.prod volume) := by
    rw [← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [hf] with z hfz
    rw [hfz,Real.inner_apply,pow_two]
  have hsn : ‖s‖^2 = (volume.prod volume).real (band M δ) := by
    rw [← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
    calc
      _ = ∫ z, (band M δ).indicator (fun _ => (1:ℝ)) z ∂(volume.prod volume) := by
        apply integral_congr_ae
        filter_upwards [hs] with z hsz
        rw [hsz,Real.inner_apply]
        by_cases hz : z ∈ band M δ <;> simp [hz]
      _ = _ := by rw [integral_indicator_const 1 (band_measurable M δ)]; simp
  have hi := norm_inner_le_norm (𝕜:=ℝ) f s
  rw [hp,Real.norm_eq_abs] at hi
  have hsq := mul_self_le_mul_self (abs_nonneg _) hi
  have he : (∫ z, kernel r n z ∂(volume.prod volume))^2 ≤ ‖f‖^2*‖s‖^2 := by
    nlinarith [sq_abs (∫ z, kernel r n z ∂(volume.prod volume))]
  rw [hfn,hsn] at he
  simpa only [mul_comm] using he

theorem kernel_concentration_bound (r : ℕ → ℝ) (n : ℕ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ M)
    (hm : ∀ i < n, |r (i+1)-r i| ≤ δ) :
    (∑ i ∈ Finset.range n, (r (i+1)-r i)^2)^2 ≤
      (2*M*δ)*(∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (volume.real (interval r i ∩ interval r j))^2) := by
  have he := mass_sq_le_area_energy r n M δ (fun z hz => kernel_zero_off_band r n M δ hr hm hz)
  rw [kernel_mass,kernel_sq_integral,band_measure_real hM hδ] at he
  exact he

end OperatorDerivativeRewrite.Foundation.IBMSpatialKernelConcentration
