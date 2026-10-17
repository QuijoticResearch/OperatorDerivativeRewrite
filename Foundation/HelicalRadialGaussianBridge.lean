import Foundation.HelicalVorticityDiagnostics
import Foundation.GaussianQuadraticSourceHodge
import Foundation.GaussianRecoveryCompactnessObstruction
import Foundation.GaussianOrthonormalPolynomialLaw

/-! Corrected helical trace and its actual radial Gaussian quadratic target. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.HelicalRadialGaussianBridge
set_option backward.isDefEq.respectTransparency false
open HelicalVorticityDiagnostics InfiniteGaussian GaussianQuadraticSourceHodge
open GaussianDivergenceRecovery GaussianSourceHodge GaussianNumberSectors

def phase (x y z : ℝ) : ℝ := x*Real.sin z-y*Real.cos z
def radial (x y : ℝ) : ℝ := 2*(x^2+y^2)-1

def correctedJacobian (ε x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![deriv (fun t => corrected ε t y z 0) x, deriv (fun t => corrected ε x t z 0) y,
      deriv (fun t => corrected ε x y t 0) z;
     deriv (fun t => corrected ε t y z 1) x, deriv (fun t => corrected ε x t z 1) y,
      deriv (fun t => corrected ε x y t 1) z;
     deriv (fun t => corrected ε t y z 2) x, deriv (fun t => corrected ε x t z 2) y,
      deriv (fun t => corrected ε x y t 2) z]

theorem correctedJacobian_eq (ε x y z : ℝ) :
    correctedJacobian ε x y z=
    !![-2*ε*x*profile x y*Real.cos z, -2*ε*y*profile x y*Real.cos z, -ε*profile x y*Real.sin z;
      -2*ε*x*profile x y*Real.sin z, -2*ε*y*profile x y*Real.sin z, ε*profile x y*Real.cos z;
      -2*x*profile x y+2*ε*profile x y*(Real.sin z-2*x*phase x y z),
      -2*y*profile x y+2*ε*profile x y*(-Real.cos z-2*y*phase x y z),
      2*ε*profile x y*(x*Real.cos z+y*Real.sin z)] := by
  have hpx : HasDerivAt (fun t : ℝ => t*Real.sin z-y*Real.cos z) (Real.sin z) x := by
    simpa using ((hasDerivAt_id x).mul_const (Real.sin z)).sub_const (y*Real.cos z)
  have hpy : HasDerivAt (fun t : ℝ => x*Real.sin z-t*Real.cos z) (-Real.cos z) y := by
    simpa using ((hasDerivAt_id y).mul_const (Real.cos z)).const_sub (x*Real.sin z)
  have hx := (profile_x x y).add (((profile_x x y).const_mul (2*ε)).mul hpx)
  have hy := (profile_y x y).add (((profile_y x y).const_mul (2*ε)).mul hpy)
  have hz := ((((Real.hasDerivAt_sin z).const_mul x).sub
    ((Real.hasDerivAt_cos z).const_mul y)).const_mul (2*ε*profile x y)).const_add (profile x y)
  have hxc : HasDerivAt (fun t => corrected ε t y z 2)
      (-2*x*profile x y+2*ε*profile x y*(Real.sin z-2*x*phase x y z)) x := by
    change HasDerivAt (fun t : ℝ => profile t y+2*ε*profile t y*(t*Real.sin z-y*Real.cos z)) _ x at hx
    change HasDerivAt (fun t : ℝ => profile t y+2*ε*profile t y*(t*Real.sin z-y*Real.cos z)) _ x
    convert hx using 1 <;> simp only [phase] <;> ring
  have hyc : HasDerivAt (fun t => corrected ε x t z 2)
      (-2*y*profile x y+2*ε*profile x y*(-Real.cos z-2*y*phase x y z)) y := by
    change HasDerivAt (fun t : ℝ => profile x t+2*ε*profile x t*(x*Real.sin z-t*Real.cos z)) _ y at hy
    change HasDerivAt (fun t : ℝ => profile x t+2*ε*profile x t*(x*Real.sin z-t*Real.cos z)) _ y
    convert hy using 1 <;> simp only [phase] <;> ring
  have hzc : HasDerivAt (fun t => corrected ε x y t 2)
      (2*ε*profile x y*(x*Real.cos z+y*Real.sin z)) z := by
    change HasDerivAt (fun t : ℝ => profile x y+2*ε*profile x y*(x*Real.sin t-y*Real.cos t)) _ z at hz
    change HasDerivAt (fun t : ℝ => profile x y+2*ε*profile x y*(x*Real.sin t-y*Real.cos t)) _ z
    convert hz using 1 <;> ring
  change !![jacobian ε x y z 0 0, jacobian ε x y z 0 1, jacobian ε x y z 0 2;
    jacobian ε x y z 1 0, jacobian ε x y z 1 1, jacobian ε x y z 1 2;
    deriv (fun t => corrected ε t y z 2) x, deriv (fun t => corrected ε x t z 2) y,
    deriv (fun t => corrected ε x y t 2) z]=_
  rw [jacobian_eq, hxc.deriv, hyc.deriv, hzc.deriv]
  rfl

theorem rotation_square (x y z : ℝ) :
    (x*Real.cos z+y*Real.sin z)^2+(phase x y z)^2=x^2+y^2 := by
  have he : (x*Real.cos z+y*Real.sin z)^2+(phase x y z)^2=
      (x^2+y^2)*((Real.sin z)^2+(Real.cos z)^2) := by unfold phase; ring
  rw [he, Real.sin_sq_add_cos_sq, mul_one]

theorem corrected_trace_algebra (ε x y z : ℝ) :
    Matrix.trace (correctedJacobian ε x y z*correctedJacobian ε x y z)=
      4*ε*(profile x y)^2*phase x y z+
      8*ε^2*(profile x y)^2*((x*Real.cos z+y*Real.sin z)^2+(phase x y z)^2)-
      4*ε^2*(profile x y)^2*((Real.sin z)^2+(Real.cos z)^2) := by
  have hs : 4*ε^2*(profile x y)^2*((Real.sin z)^2+(Real.cos z)^2)=4*ε^2*(profile x y)^2 := by
    rw [Real.sin_sq_add_cos_sq, mul_one]
  rw [correctedJacobian_eq]
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three]
  unfold phase
  nlinarith [hs]

theorem corrected_trace (ε x y z : ℝ) :
    Matrix.trace (correctedJacobian ε x y z*correctedJacobian ε x y z)=
      ε*linearTrace x y z+4*ε^2*(profile x y)^2*radial x y := by
  rw [corrected_trace_algebra, rotation_square, Real.sin_sq_add_cos_sq]
  unfold linearTrace phase radial
  ring

theorem corrected_period_integral (ε x y : ℝ) :
    (∫ z in (0:ℝ)..(2*Real.pi),
      Matrix.trace (correctedJacobian ε x y z*correctedJacobian ε x y z))=
        8*Real.pi*ε^2*(profile x y)^2*radial x y := by
  simp_rw [corrected_trace]
  have hl : Continuous (linearTrace x y) := by unfold linearTrace; fun_prop
  rw [intervalIntegral.integral_add ((hl.const_mul ε).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    linearTrace_period_average, intervalIntegral.integral_const]
  simp only [mul_zero, zero_add, sub_zero, smul_eq_mul]
  ring

theorem radial_scaling (X Y : ℝ) : radial (X/2) (Y/2)=((X^2-1)+(Y^2-1))/2 := by
  unfold radial
  ring

theorem radial_signs : radial 0 0=-1 ∧ radial 1 0=1 := by norm_num [radial]

def directions (i : Fin 2) : CoefficientSpace := lp.single 2 i.val (1:ℝ)

theorem directions_orthonormal : Orthonormal ℝ directions :=
  GaussianRecoveryCompactnessObstruction.coefficient_single_orthonormal.comp
    Fin.val Fin.val_injective

def radialTarget : GaussianL2 := (1/2 : ℝ) • quadraticTarget directions (1 : Matrix (Fin 2) (Fin 2) ℝ)

theorem identity_target_expansion : quadraticTarget directions (1 : Matrix (Fin 2) (Fin 2) ℝ)=
    mixedTarget (directions 0) (directions 0)+mixedTarget (directions 1) (directions 1) := by
  simp [quadraticTarget, Fin.sum_univ_two]

theorem radialTarget_ae : radialTarget =ᵐ[gaussianProduct] fun ω =>
    radial (firstChaosEmbedding (directions 0) ω/2) (firstChaosEmbedding (directions 1) ω/2) := by
  have hi := orthonormal_iff_ite.mp directions_orthonormal
  filter_upwards [Lp.coeFn_smul (1/2 : ℝ) (quadraticTarget directions (1 : Matrix (Fin 2) (Fin 2) ℝ)),
    Lp.coeFn_add (mixedTarget (directions 0) (directions 0)) (mixedTarget (directions 1) (directions 1)),
    mixedTarget_coeFn (directions 0) (directions 0), mixedTarget_coeFn (directions 1) (directions 1)]
    with ω hs ha h0 h1
  change ((1/2 : ℝ) • quadraticTarget directions (1 : Matrix (Fin 2) (Fin 2) ℝ)) ω=_
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, identity_target_expansion, ha]
  simp only [Pi.add_apply] at *
  rw [h0, h1, hi, hi]
  simp only [ite_true]
  unfold radial
  ring

theorem radialTarget_energy : ‖radialTarget‖^2=1 := by
  have he := quadraticTarget_matrix_energy directions directions_orthonormal
    (1 : Matrix (Fin 2) (Fin 2) ℝ)
  norm_num [Fin.sum_univ_two] at he
  rw [radialTarget, norm_smul, mul_pow]
  norm_num
  nlinarith

theorem radialTarget_recovery : recovery radialTarget=
    (1/2 : ℝ) • linearField directions (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [radialTarget, recovery_smul, quadraticTarget_recovery]
  have he : symmetrize (1 : Matrix (Fin 2) (Fin 2) ℝ)=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [symmetrize]
  rw [he]

theorem radial_recovery_energy : ‖recovery radialTarget‖^2=1/2 := by
  have he := linearField_energy directions directions_orthonormal (1 : Matrix (Fin 2) (Fin 2) ℝ)
  norm_num [Fin.sum_univ_two] at he
  rw [radialTarget_recovery, norm_smul, mul_pow]
  norm_num
  nlinarith

theorem radialTarget_mean_zero : (∫ ω, radialTarget ω ∂gaussianProduct)=0 := by
  have hg := linearField_divergence_graph directions (1 : Matrix (Fin 2) (Fin 2) ℝ)
  have hi := GaussianNumberSectors.graph_duality (closedDerivative_constant_graph 1) hg
  have hc : inner ℝ gaussianOne (quadraticTarget directions (1 : Matrix (Fin 2) (Fin 2) ℝ))=0 := by
    simpa only [one_smul, inner_zero_left] using hi.symm
  rw [← gaussianOne_inner_eq_integral, radialTarget, inner_smul_right, hc, mul_zero]

def physicalGaussian : Measure (ℝ × ℝ) := (gaussianReal 0 (1/4)).prod (gaussianReal 0 (1/4))

theorem standard_pair_law : HasLaw (fun ω =>
    (firstChaosEmbedding (directions 0) ω, firstChaosEmbedding (directions 1) ω))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) gaussianProduct := by
  have hl := GaussianOrthonormalPolynomialLaw.orthonormal_firstChaosFamily_law
    directions directions_orthonormal
  exact (measurePreserving_finTwoArrow GaussianCore.γ).hasLaw.comp hl

theorem scaled_pair_law : HasLaw (fun ω =>
    (firstChaosEmbedding (directions 0) ω/2, firstChaosEmbedding (directions 1) ω/2))
      physicalGaussian gaussianProduct := by
  have hm : MeasurePreserving (fun x : ℝ => x/2) (gaussianReal 0 1) (gaussianReal 0 (1/4)) := by
    refine ⟨by fun_prop, ?_⟩
    have he := gaussianReal_map_div_const (μ := 0) (v := 1) (2:ℝ)
    norm_num at he
    exact he
  exact (hm.prod hm).hasLaw.comp standard_pair_law

theorem quarter_pdf (x : ℝ) : gaussianPDFReal 0 (1/4) x=
    (Real.sqrt (Real.pi/2))⁻¹*Real.exp (-2*x^2) := by
  unfold gaussianPDFReal
  change (Real.sqrt (2*Real.pi*((1:ℝ)/4)))⁻¹*
    Real.exp (-(x-0)^2/(2*((1:ℝ)/4)))=_
  have he : 2*Real.pi*((1:ℝ)/4)=Real.pi/2 := by ring
  rw [he]
  congr 1
  congr 1
  ring

theorem physical_pdf (x y : ℝ) : gaussianPDFReal 0 (1/4) x*gaussianPDFReal 0 (1/4) y=
    (2/Real.pi)*(profile x y)^2 := by
  rw [quarter_pdf, quarter_pdf, mul_mul_mul_comm, ← pow_two, inv_pow,
    Real.sq_sqrt (by positivity : 0 ≤ Real.pi/2), ← Real.exp_add]
  have he : Real.exp (-2*x^2+-2*y^2)=(profile x y)^2 := by
    rw [profile, pow_two (Real.exp (-(x^2+y^2))), ← Real.exp_add]
    congr 1
    ring
  rw [he]
  field_simp

theorem physicalGaussian_density : physicalGaussian=(volume.prod volume).withDensity
    (fun p : ℝ × ℝ => ENNReal.ofReal ((2/Real.pi)*(profile p.1 p.2)^2)) := by
  rw [physicalGaussian, gaussianReal_of_var_ne_zero 0 (by norm_num : (1/4 : NNReal) ≠ 0),
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
  congr 1
  funext p
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), physical_pdf]

theorem physical_density_integral :
    (∫ p : ℝ × ℝ, (2/Real.pi)*(profile p.1 p.2)^2 ∂volume.prod volume)=1 := by
  simp_rw [← physical_pdf]
  rw [integral_prod_mul (fun x : ℝ => gaussianPDFReal 0 (1/4) x)
    (fun x : ℝ => gaussianPDFReal 0 (1/4) x),
    integral_gaussianPDFReal_eq_one 0 (by norm_num : (1/4 : NNReal) ≠ 0)]
  norm_num

theorem profile_square_normalization :
    (∫ p : ℝ × ℝ, (profile p.1 p.2)^2 ∂volume.prod volume)=Real.pi/2 := by
  have hi := physical_density_integral
  rw [integral_const_mul] at hi
  calc
    _ = (Real.pi/2)*((2/Real.pi)*(∫ p : ℝ × ℝ, (profile p.1 p.2)^2 ∂volume.prod volume)) := by
      field_simp
    _ = _ := by rw [hi]; ring

theorem physical_radial_integrable : Integrable (fun p : ℝ × ℝ => radial p.1 p.2) physicalGaussian := by
  have hl := scaled_pair_law
  have hi : Integrable (fun ω => radial (firstChaosEmbedding (directions 0) ω/2)
      (firstChaosEmbedding (directions 1) ω/2)) gaussianProduct :=
    ((Lp.memLp radialTarget).integrable (by norm_num)).congr radialTarget_ae
  rw [← hl.map_eq]
  exact (integrable_map_measure (by unfold radial; fun_prop) hl.aemeasurable).mpr hi

theorem physical_radial_mean_zero : (∫ p : ℝ × ℝ, radial p.1 p.2 ∂physicalGaussian)=0 := by
  calc
    _ = ∫ ω, radial (firstChaosEmbedding (directions 0) ω/2)
        (firstChaosEmbedding (directions 1) ω/2) ∂gaussianProduct :=
      (scaled_pair_law.integral_comp (by unfold radial; fun_prop)).symm
    _ = ∫ ω, radialTarget ω ∂gaussianProduct := integral_congr_ae radialTarget_ae.symm
    _ = 0 := radialTarget_mean_zero

end OperatorDerivativeRewrite.Foundation.HelicalRadialGaussianBridge
