import Foundation.CubeBoundaryKernelL2

/-! Haar half-density factors in the actual boundary-chart kernel limit.
An identification with the full Haar operator and control of its complement remain separate. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CubeBoundaryHaarL2
open SU2GaussianConeCoordinates CubeChartAction CubeBoundaryKernelL2
open FourCubeHaarLaplaceDensity

def density (X : Boundary) : ℝ := ∏ i : Fin 5, chartDensity (X i)
def halfDensity (t : ℝ) (p : Boundary × Boundary) : ℝ :=
  Real.sqrt (density (t • p.1)*density (t • p.2))
def kernel (t : ℝ) (p : Boundary × Boundary) : ℝ := halfDensity t p*localKernel t p
def limit (p : Boundary × Boundary) : ℝ := (chartDensity 0)^5*limitKernel p

theorem density_positive (X : Boundary) : 0 < density X :=
  Finset.prod_pos (fun _ _ => chartDensity_positive _)

theorem density_bound (X : Boundary) : density X ≤ (chartDensity 0)^5 := by
  have h := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun i _ => (chartDensity_positive (X i)).le) (fun i _ => chartDensity_le_zero (X i))
  simpa only [density,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h

theorem density_continuous : Continuous density :=
  continuous_finsetProd _ (fun i _ => chartDensity_continuous.comp (continuous_apply i))

theorem density_zero : density 0=(chartDensity 0)^5 := by
  simp [density]

theorem halfDensity_continuous (t : ℝ) : Continuous (halfDensity t) := by
  exact ((density_continuous.comp (continuous_fst.const_smul t)).mul
    (density_continuous.comp (continuous_snd.const_smul t))).sqrt

theorem halfDensity_bound (t : ℝ) (p : Boundary × Boundary) :
    halfDensity t p ≤ (chartDensity 0)^5 := by
  have h := mul_le_mul (density_bound (t • p.1)) (density_bound (t • p.2))
    (density_positive _).le (pow_pos (chartDensity_positive _) 5).le
  have hs := Real.sqrt_le_sqrt h
  simpa only [halfDensity,← sq,Real.sqrt_sq (pow_pos (chartDensity_positive _) 5).le] using hs

theorem halfDensity_tendsto (p : Boundary × Boundary) :
    Tendsto (fun t : ℝ => halfDensity t p) (𝓝 (0 : ℝ)) (𝓝 ((chartDensity 0)^5)) := by
  have hc : Continuous (fun t : ℝ => halfDensity t p) :=
    ((density_continuous.comp (continuous_id.smul continuous_const)).mul
      (density_continuous.comp (continuous_id.smul continuous_const))).sqrt
  simpa only [halfDensity,zero_smul,density_zero,← sq,
    Real.sqrt_sq (pow_pos (chartDensity_positive _) 5).le] using hc.tendsto (0 : ℝ)

theorem kernel_tendsto (p : Boundary × Boundary) :
    Tendsto (fun t : ℝ => kernel t p) (𝓝[>] (0 : ℝ)) (𝓝 (limit p)) :=
  ((halfDensity_tendsto p).mono_left nhdsWithin_le_nhds).mul (localKernel_tendsto p)

theorem kernel_nonnegative (t : ℝ) (ht : 0 < t) (p : Boundary × Boundary) :
    0 ≤ kernel t p := mul_nonneg (Real.sqrt_nonneg _) (localKernel_nonnegative t ht p)

theorem kernel_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (p : Boundary × Boundary) :
    kernel t p ≤ (chartDensity 0)^5*envelope p :=
  mul_le_mul (halfDensity_bound t p) (localKernel_bound t ht h1 p)
    (localKernel_nonnegative t ht p) (pow_pos (chartDensity_positive _) 5).le

theorem limit_nonnegative (p : Boundary × Boundary) : 0 ≤ limit p :=
  mul_nonneg (pow_pos (chartDensity_positive _) 5).le (limitKernel_nonnegative p)

theorem limit_bound (p : Boundary × Boundary) : limit p ≤ (chartDensity 0)^5*envelope p :=
  mul_le_mul_of_nonneg_left (limitKernel_bound p) (pow_pos (chartDensity_positive _) 5).le

theorem kernel_measurable (t : ℝ) : Measurable (kernel t) :=
  (halfDensity_continuous t).measurable.mul (localKernel_measurable t)

theorem limit_aestronglyMeasurable : AEStronglyMeasurable limit :=
  limitKernel_aestronglyMeasurable.const_mul _

theorem envelope_sq_integrable :
    Integrable (fun p : Boundary × Boundary => ((chartDensity 0)^5*envelope p)^2) := by
  simpa only [mul_pow] using
    CubeBoundaryKernelL2.envelope_sq_integrable.const_mul (((chartDensity 0)^5)^2)

theorem kernel_memLp (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) : MemLp (kernel t) 2 volume := by
  apply (memLp_two_iff_integrable_sq (kernel_measurable t).aestronglyMeasurable).mpr
  apply envelope_sq_integrable.mono' ((kernel_measurable t).pow_const 2).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (kernel_nonnegative t ht p) (kernel_bound t ht h1 p) 2

theorem limit_memLp : MemLp limit 2 volume := by
  apply (memLp_two_iff_integrable_sq limit_aestronglyMeasurable).mpr
  apply envelope_sq_integrable.mono' (limit_aestronglyMeasurable.pow 2)
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (limit_nonnegative p) (limit_bound p) 2

/-- Squared-L2 convergence with the genuine two endpoint Haar density factors.
The t^15 Jacobian power is separated from these half-densities; combined with
the existing t^21 kernel scaling it gives the candidate t^36 operator scaling. -/
theorem integral_sq_error_tendsto :
    Tendsto (fun t : ℝ => ∫ p : Boundary × Boundary, (kernel t p-limit p)^2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => ∫ p : Boundary × Boundary, (kernel t p-limit p)^2)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ _ : Boundary × Boundary, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun p : Boundary × Boundary => 4*((chartDensity 0)^5*envelope p)^2)
    · exact Eventually.of_forall (fun t =>
        (((kernel_measurable t).aestronglyMeasurable.sub limit_aestronglyMeasurable).pow 2))
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht h1
      filter_upwards with p
      have ha := kernel_nonnegative t ht p
      have hb := limit_nonnegative p
      have hc := kernel_bound t ht h1 p
      have hd := limit_bound p
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [mul_nonneg ha hb,pow_le_pow_left₀ ha hc 2,pow_le_pow_left₀ hb hd 2]
    · exact envelope_sq_integrable.const_mul 4
    · exact ae_of_all _ (fun p => by
        have hp := ((kernel_tendsto p).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => limit p) (𝓝[>] (0:ℝ)) (𝓝 (limit p)))).pow 2
        simpa only [sub_self,zero_pow (by norm_num : (2:ℕ)≠0)] using hp)
  simpa only [integral_zero] using h

end OperatorDerivativeRewrite.Foundation.CubeBoundaryHaarL2
