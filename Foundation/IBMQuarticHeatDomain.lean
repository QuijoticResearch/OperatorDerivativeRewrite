import Foundation.IBMQuarticHeatHalfLine

/-! Absolute Bochner domains for the actual quartic heat correction and
its exact half-line boundary identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticHeatDomain
open InfiniteGaussian IBMClockGaussianTail IBMClockHeatPotential IBMClockHeatOccupation
open IBMQuarticSecondPrimitive IBMQuarticPrimitiveLimit IBMQuarticClockTerminal
open IBMQuarticHeatEndpoint IBMQuarticHeatHalfLine IBMQuarticHeatBoundary
open IBMGaussianSteinMoments IBMQuarticSecondChaos GaussianTimeSpaceHermite

theorem projected_growth (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r,
      ‖GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r)‖ ≤
        C*(1+|r|)^3 := by
  obtain ⟨A,hA,ha⟩ := cross_growth n 0 0
  obtain ⟨B,hB,hb⟩ := cross_growth n 0 1
  obtain ⟨D,hD,hd⟩ := cross_growth n 1 1
  obtain ⟨E,hE,he⟩ := cross_growth n 0 2
  let K : ℝ := IBMBoundaryClockLimit.curvatureBound n
  have hK : 0 ≤ K := (IBMBoundaryClockLimit.curvatureBound n).coe_nonneg
  refine ⟨K*A+B+D+E, by positivity, fun r => ?_⟩
  have hw₀ : ‖(wick (tripleCoefficient n r 0) 2 : GaussianL2)‖ ≤ A*(1+|r|)^2 := by
    rw [← cross_self]; exact ha r
  have hw₁ : ‖(wick (tripleCoefficient n r 1) 2 : GaussianL2)‖ ≤ D*(1+|r|)^2 := by
    rw [← cross_self]; exact hd r
  have hk : ‖IBMMollifier.kernel n r/2‖ ≤ K := by
    have hz : ‖deriv (deriv (IBMVarianceClockGeometry.variance n)) r‖ ≤ K :=
      IBMBoundaryClockLimit.curvature_bound n r
    rw [IBMVarianceClockGeometry.variance_second, norm_mul] at hz
    rw [norm_div]
    norm_num at hz ⊢
    linarith [norm_nonneg (IBMMollifier.kernel n r)]
  have hv : ‖IBMVarianceClockGeometry.variance n r/2‖ ≤ 1+|r| := by
    have hh := IBMVarianceClockGeometry.variance_bound n r
    rw [Real.norm_eq_abs] at hh
    rw [norm_div]
    norm_num
    linarith [abs_nonneg r]
  have hsum : ‖(wick (tripleCoefficient n r 1) 2 : GaussianL2) +
      cross (tripleCoefficient n r 0) (tripleCoefficient n r 2)‖ ≤ (D+E)*(1+|r|)^2 := by
    exact (norm_add_le _ _).trans (by nlinarith [he r])
  have h₁ := mul_le_mul hk hw₀ (norm_nonneg _) hK
  have h₂ := mul_le_mul (IBMVarianceClockGeometry.slope_bound n r) (hb r)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h₃ := mul_le_mul hv hsum (norm_nonneg _) (by positivity : 0 ≤ 1+|r|)
  have hq : (1+|r|)^2 ≤ (1+|r|)^3 :=
    pow_le_pow_right₀ (by linarith [abs_nonneg r]) (by norm_num)
  rw [IBMQuarticSecondGeometry.spatialQuartic_projection_two]
  calc
    _ ≤ ‖(IBMMollifier.kernel n r/2) • (wick (tripleCoefficient n r 0) 2 : GaussianL2)‖ +
        ‖deriv (IBMVarianceClockGeometry.variance n) r •
          cross (tripleCoefficient n r 0) (tripleCoefficient n r 1)‖ +
        ‖(IBMVarianceClockGeometry.variance n r/2) •
          ((wick (tripleCoefficient n r 1) 2 : GaussianL2) +
            cross (tripleCoefficient n r 0) (tripleCoefficient n r 2))‖ := norm_add₃_le
    _ ≤ (K*A+B+D+E)*(1+|r|)^3 := by
      simp only [norm_smul]
      nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ K*A+B)]

theorem polynomial_heat_integrable (T : ℝ≥0) (hT : 0 < T) (k : ℕ) :
    Integrable (fun r => heatKernel T r * (1+|r|)^k) := by
  have hm : MemLp (fun r : ℝ => 1+|r|) (k : ℝ≥0∞) (gaussianReal 0 T) :=
    (memLp_const (1 : ℝ)).add (memLp_id_gaussianReal' (μ := 0) (v := T) _ (by simp)).norm
  have hi := hm.integrable_norm_pow'
  have hp : Integrable (fun r : ℝ => (1+|r|)^k) (gaussianReal 0 T) := by
    convert hi using 1
    funext r
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1+|r|)]
  rw [gaussianReal_of_var_ne_zero 0 (ne_of_gt hT)] at hp
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hp
  simp only [toReal_gaussianPDF, smul_eq_mul] at hp
  convert hp using 1
  funext r
  rw [heatKernel_eq_pdf (NNReal.coe_pos.mpr hT)]
  rfl

theorem weighted_curvature_integrableOn (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    IntegrableOn (fun r => potential T r •
      GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r)) (Ioi 0) := by
  obtain ⟨C,hC,hc⟩ := projected_growth n
  have ha : 0 < Real.sqrt T := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hT)
  apply ((polynomial_heat_integrable T hT 3).integrableOn.const_mul
    (4*(Real.sqrt T)^2*C)).mono'
    ((potential_continuous (NNReal.coe_pos.mpr hT)).smul
      (IBMQuarticSpatialWeakLimit.projected_continuous n)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change ‖potential T r • GaussianNumberSectors.projection 2
    (IBMQuarticSecondGeometry.spatialQuartic n r)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
    (potential_nonneg (NNReal.coe_pos.mpr hT) hr.le)]
  have hb : potential T r ≤ 4*(Real.sqrt T)^2*heatKernel T r := by
    have hh := IBMHeatTailDecay.potential_le_density (T := (T : ℝ)) hr.le
    have hd : 4*(Real.sqrt T)^2*heatKernel T r =
        4*Real.sqrt T*density (r/Real.sqrt T) := by
      unfold heatKernel
      field_simp
    rwa [hd]
  have he := mul_le_mul hb (hc r) (norm_nonneg _)
    (mul_nonneg (by positivity : 0 ≤ 4*(Real.sqrt T)^2) (heatKernel_nonneg _ _))
  nlinarith

/-- A genuine absolutely Bochner-integrable half-line identity. The
random clock/time/source interchange remains a separate obligation. -/
theorem halfline_origin_cancellation (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    (∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) • slope n 0 +
      (1/2 : ℝ) • (∫ r in Ioi 0, potential T r •
        GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r)) =
      terminalMean n T-primitive n 0 := by
  have hi := intervalIntegral_tendsto_integral_Ioi 0 (weighted_curvature_integrableOn n T hT) tendsto_id
  have he := (hi.const_smul (1/2 : ℝ)).const_add
    ((∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) • slope n 0)
  have hh : Tendsto (truncatedCorrection n T) atTop
      (𝓝 ((∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) • slope n 0 +
        (1/2 : ℝ) • (∫ r in Ioi 0, potential T r •
          GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r)))) := by
    change Tendsto (fun R => _ + (1/2 : ℝ) • (∫ r in 0..R, potential T r •
      GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r))) atTop _
    simpa only [id_eq] using he
  exact tendsto_nhds_unique hh (truncatedCorrection_tendsto n T hT)

/-- Strong source-L2 convergence of the genuine half-line spatial
correction. This does not exchange the radius and mollifier limits. -/
theorem halfline_origin_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n =>
      (∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) •
        IBMQuarticSecondPrimitive.slope n 0 +
        (1/2 : ℝ) • (∫ r in Ioi 0, potential T r •
          GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r))) atTop
      (𝓝 (terminalLimit T)) := by
  simp_rw [halfline_origin_cancellation _ T hT]
  exact terminalDifference_tendsto T

end OperatorDerivativeRewrite.Foundation.IBMQuarticHeatDomain
