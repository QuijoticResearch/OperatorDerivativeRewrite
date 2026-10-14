import Foundation.GaussianPhysicalDisplacement

/-! Exact physical Gaussian coherent laws and unbounded entropy distortion under full Poisson graph transfer. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianCoherentEntropyDistortion
open GaussianCore GaussianCoherentIdentification GaussianDisplacementQuarticObstruction
open PoissonTiltHellingerGeometry PoissonTiltSourceGauge

def coherentDensity (d x : ℝ) : ℝ := Real.exp (2*d*x-2*d^2)
def coherentLaw (d : ℝ) : Measure ℝ := GaussianCore.weightedMeasure γ (coherentDensity d)
def coherentEntropy (d : ℝ) : ℝ := ∫ x, coherentDensity d x*Real.log (coherentDensity d x) ∂γ

theorem coherent_density_pdf (d x : ℝ) :
    gaussianPDF 0 1 x*ENNReal.ofReal (coherentDensity d x)=gaussianPDF (2*d) 1 x := by
  rw [gaussianPDF,gaussianPDF,← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,coherentDensity]
  rw [mul_assoc,← Real.exp_add]
  congr 1
  ring

theorem coherentLaw_eq_gaussian (d : ℝ) : coherentLaw d=gaussianReal (2*d) 1 := by
  rw [coherentLaw,GaussianCore.weightedMeasure,γ,gaussianReal_of_var_ne_zero 0 (by norm_num),
    gaussianReal_of_var_ne_zero (2*d) (by norm_num),
    ← withDensity_mul volume (measurable_gaussianPDF 0 1) (by unfold coherentDensity; fun_prop)]
  congr 1
  funext x
  exact coherent_density_pdf d x

theorem coherentDensity_mean_one (d : ℝ) : (∫ x, coherentDensity d x ∂γ)=1 := by
  have he := GaussianCore.weighted_integral (μ := γ) (w := coherentDensity d)
    (by unfold coherentDensity; fun_prop) (fun x => (Real.exp_pos _).le) (fun _ => (1 : ℝ))
  change (∫ x, (1 : ℝ) ∂coherentLaw d)=_ at he
  rw [coherentLaw_eq_gaussian] at he
  simpa only [mul_one,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using he.symm

theorem coherent_squared_density (d : ℝ) : (fun x => (gaussianRoot d x)^2) =ᵐ[γ] coherentDensity d := by
  filter_upwards [coherentTwo_coeFn d] with x hx
  rw [hx,← Real.exp_nat_mul,coherentDensity]
  congr 1
  ring

private theorem gaussian_id_integrable (d : ℝ) : Integrable (fun x : ℝ => x) (gaussianReal (2*d) 1) := by
  change Integrable id (gaussianReal (2*d) 1)
  exact (memLp_id_gaussianReal (μ := 2*d) (v := 1) 1).integrable (by norm_num)

theorem coherent_log_integrable (d : ℝ) : Integrable (fun x => Real.log (coherentDensity d x)) (coherentLaw d) := by
  rw [coherentLaw_eq_gaussian]
  simp only [coherentDensity,Real.log_exp]
  exact ((gaussian_id_integrable d).const_mul (2*d)).sub (integrable_const (2*d^2))

theorem coherent_density_log_integrable (d : ℝ) :
    Integrable (fun x => coherentDensity d x*Real.log (coherentDensity d x)) γ := by
  apply (GaussianCore.weighted_integrable_iff (by unfold coherentDensity; fun_prop : Measurable (coherentDensity d))
    (fun x => (Real.exp_pos _).le)).mp
  exact coherent_log_integrable d

theorem coherentEntropy_eq (d : ℝ) : coherentEntropy d=2*d^2 := by
  rw [coherentEntropy,← GaussianCore.weighted_integral (by unfold coherentDensity; fun_prop : Measurable (coherentDensity d))
    (fun x => (Real.exp_pos _).le) (fun x => Real.log (coherentDensity d x))]
  change (∫ x, Real.log (coherentDensity d x) ∂coherentLaw d)=_
  rw [coherentLaw_eq_gaussian]
  simp only [coherentDensity,Real.log_exp]
  rw [integral_sub ((gaussian_id_integrable d).const_mul (2*d)) (integrable_const (2*d^2)),
    integral_const_mul,integral_id_gaussianReal]
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul]
  ring

theorem coherentEntropy_eq_twice_derivative_energy (d : ℝ) : coherentEntropy d=2*‖d • gaussianRoot d‖^2 := by
  rw [coherentEntropy_eq,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,gaussianRoot_norm]
  ring

theorem coherentEntropy_displacement (rate : ℝ≥0) (θ : ℝ) :
    coherentEntropy (displacement rate θ)=2*(rate : ℝ)*(Real.exp (θ/2)-1)^2 := by
  rw [coherentEntropy_eq,displacement,← sqrtRate_eq_sqrt_tilted rate θ,sqrtRate]
  have he : Real.sqrt (rate : ℝ)*Real.exp (θ/2)-Real.sqrt rate=
      Real.sqrt rate*(Real.exp (θ/2)-1) := by ring
  rw [he,mul_pow,Real.sq_sqrt rate.coe_nonneg]
  ring

theorem unbounded_physical_entropy_distortion (rate : ℝ≥0) (hr : 0<rate) (K : ℝ) (hK : 0≤K) :
    ∃ θ : ℝ, K*coherentEntropy (displacement rate θ)<
      ∫ n, PoissonExponentialTilt.density rate θ n*Real.log (PoissonExponentialTilt.density rate θ n)
        ∂PoissonDifferenceCore.poissonLaw rate := by
  let θ := 2*K+2
  have hθ : 0≤θ := by dsimp [θ]; linarith
  have hp : 1≤Real.exp (θ/2) := Real.one_le_exp_iff.mpr (by linarith)
  have he : (Real.exp (θ/2))^2=Real.exp θ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hs : (Real.exp (θ/2)-1)^2≤Real.exp θ := by nlinarith
  have hb : coherentEntropy (displacement rate θ)≤2*(rate : ℝ)*Real.exp θ := by
    rw [coherentEntropy_displacement]
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  refine ⟨θ, ?_⟩
  calc
    _≤K*(2*(rate : ℝ)*Real.exp θ) := mul_le_mul_of_nonneg_left hb hK
    _<(rate : ℝ)*(θ*Real.exp θ-Real.exp θ+1) := by
      have hm : 0<(rate : ℝ)*Real.exp θ := mul_pos hr (Real.exp_pos _)
      dsimp [θ]
      nlinarith
    _=_ := (PoissonExponentialTilt.relative_entropy rate θ).symm

end OperatorDerivativeRewrite.Foundation.GaussianCoherentEntropyDistortion
