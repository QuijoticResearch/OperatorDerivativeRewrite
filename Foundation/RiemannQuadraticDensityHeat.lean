import Foundation.NewmanFourPointBound
import Foundation.RiemannQuadraticDensitySmoothing
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Actual Gaussian density/heat identity, with L1 domains, exact variance and normalizer, and its logarithmic four-point consequence. -/
noncomputable section
open MeasureTheory Filter Set Real ProbabilityTheory
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticDensityHeat
open RiemannQuarticKernel RiemannQuadraticDensitySmoothing
open RiemannQuarticFlow (halfLine)

theorem pdf_density_integrable (v : ℝ≥0) (x : ℝ) :
    Integrable (fun u : ℝ => gaussianPDFReal x v u*evenDensity u) := by
  obtain ⟨C,hC,hbound⟩ := evenDensity_bounded
  exact (integrable_gaussianPDFReal x v).mul_bdd evenDensity_continuous.aestronglyMeasurable
    (Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hbound u))

theorem pdf_reflection (v : ℝ≥0) (x u : ℝ) :
    gaussianPDFReal x v (-u) = gaussianPDFReal (-x) v u := by
  unfold gaussianPDFReal
  congr 2
  ring

theorem even_density_gaussian_halfLine (v : ℝ≥0) (x : ℝ) (hv : v ≠ 0) :
    (∫ u : ℝ, evenDensity u ∂gaussianReal x v) =
      ∫ u : ℝ, (gaussianPDFReal x v u+gaussianPDFReal (-x) v u)*kernel u ∂halfLine := by
  let F : ℝ → ℝ := fun u => gaussianPDFReal x v u*evenDensity u
  have hF : Integrable F := pdf_density_integrable v x
  have hFn : Integrable (fun u => F (-u)) := by
    have he : (fun u => F (-u)) = (fun u => gaussianPDFReal (-x) v u*evenDensity u) := by
      funext u
      simp only [F,pdf_reflection,evenDensity,abs_neg]
    rw [he]
    exact pdf_density_integrable v (-x)
  rw [integral_gaussianReal_eq_integral_smul hv]
  change (∫ u : ℝ, F u) = _
  have hs := integral_add_compl (s := Iic (0:ℝ)) measurableSet_Iic hF
  simp only [compl_Iic] at hs
  have hneg : (∫ u in Iic (0:ℝ), F u) = ∫ u in Ioi (0:ℝ), F (-u) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 F).symm
  rw [← hs,hneg]
  rw [← integral_add hFn.integrableOn hF.integrableOn, ← integral_Ici_eq_integral_Ioi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  have hu0 : (0:ℝ) ≤ u := hu
  simp only [F,pdf_reflection,evenDensity,abs_neg,abs_of_nonneg hu0]
  ring

theorem completed_square_cosh (s x u : ℝ) :
    exp (-s*(u-x)^2)+exp (-s*(u+x)^2) =
      2*exp (-s*x^2)*exp (-s*u^2)*cosh ((2*s*x)*u) := by
  rw [show -s*(u-x)^2=(-s*x^2+-s*u^2)+(2*s*x)*u by ring,
    show -s*(u+x)^2=(-s*x^2+-s*u^2)+-((2*s*x)*u) by ring]
  simp only [Real.exp_add,Real.cosh_eq]
  ring

theorem pdf_pair_heat (v : ℝ≥0) (x u : ℝ) :
    (gaussianPDFReal x v u+gaussianPDFReal (-x) v u)*kernel u =
      (2*(sqrt (2*Real.pi*(v:ℝ)))⁻¹*exp (-(2*(v:ℝ))⁻¹*x^2))*
        (RiemannEvenDomain.weighted 1 0 (-(2*(v:ℝ))⁻¹) 0 u*cosh ((2*(2*(v:ℝ))⁻¹*x)*u)) := by
  simp only [gaussianPDFReal,RiemannEvenDomain.weighted,pow_zero,one_mul,zero_mul,
    add_zero,show 2*(1:ℕ)=2 by norm_num]
  have he (a : ℝ) : -a^2/(2*(v:ℝ)) = -(2*(v:ℝ))⁻¹*a^2 := by ring
  rw [he,he]
  rw [show u- -x=u+x by ring,← mul_add,completed_square_cosh]
  ring

theorem imaginary_integrand (t y u : ℝ) :
    (RiemannEvenDomain.weighted 1 0 t 0 u:ℂ)*Complex.cos ((u:ℂ)*(Complex.I*(y:ℂ))) =
      ((RiemannEvenDomain.weighted 1 0 t 0 u*cosh (u*y):ℝ):ℂ) := by
  rw [show (u:ℂ)*(Complex.I*(y:ℂ))=((u*y:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.cos_mul_I,← Complex.ofReal_cosh,← Complex.ofReal_mul]

theorem imaginary_integrable (t y : ℝ) :
    Integrable (fun u : ℝ => RiemannEvenDomain.weighted 1 0 t 0 u*cosh (u*y)) halfLine := by
  have h := (RiemannEvenEvolution.cosine_integrable 1 t (Complex.I*(y:ℂ))).re
  simpa only [imaginary_integrand,RCLike.re_eq_complex_re,Complex.ofReal_re] using h

theorem flow_imaginary_integral (t y : ℝ) :
    RiemannEvenFlow.flow 1 t (Complex.I*(y:ℂ)) =
      ((∫ u : ℝ, RiemannEvenDomain.weighted 1 0 t 0 u*cosh (u*y) ∂halfLine):ℝ) := by
  rw [RiemannEvenEvolution.flow_eq_cosine_integral]
  simp_rw [imaginary_integrand]
  exact integral_ofReal

theorem gaussian_heat_identity (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    Complex.ofReal (∫ u : ℝ, evenDensity u ∂gaussianReal x v) =
      ((2*(sqrt (2*Real.pi*(v:ℝ)))⁻¹*exp (-(2*(v:ℝ))⁻¹*x^2):ℝ):ℂ)*
        RiemannEvenFlow.flow 1 (-(2*(v:ℝ))⁻¹) (Complex.I*((2*(2*(v:ℝ))⁻¹*x:ℝ):ℂ)) := by
  rw [even_density_gaussian_halfLine v x hv]
  simp_rw [pdf_pair_heat]
  rw [integral_const_mul,flow_imaginary_integral,← Complex.ofReal_mul]
  congr 2
  apply integral_congr_ae
  filter_upwards with u
  rw [mul_comm (2*(2*(v:ℝ))⁻¹*x) u]

theorem smoothing_log_heat (epsilon : ℝ) (hne : epsilon ≠ 0) (x : ℝ) :
    let v : ℝ≥0 := ⟨epsilon^2,sq_nonneg epsilon⟩*2
    log (smoothing epsilon x) = log (2*(sqrt (2*Real.pi*(v:ℝ)))⁻¹) -
      (2*(v:ℝ))⁻¹*x^2 +
        log ‖RiemannEvenFlow.flow 1 (-(2*(v:ℝ))⁻¹)
          (Complex.I*((2*(2*(v:ℝ))⁻¹*x:ℝ):ℂ))‖ := by
  let v : ℝ≥0 := ⟨epsilon^2,sq_nonneg epsilon⟩*2
  have hvp : (0:ℝ) < (v:ℝ) := by
    change 0 < epsilon^2*2
    exact mul_pos (sq_pos_of_ne_zero hne) (by norm_num)
  have hv : v ≠ 0 := ne_of_gt (NNReal.coe_pos.mp hvp)
  let K : ℝ := 2*(sqrt (2*Real.pi*(v:ℝ)))⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  let H : ℂ := RiemannEvenFlow.flow 1 (-(2*(v:ℝ))⁻¹)
    (Complex.I*((2*(2*(v:ℝ))⁻¹*x:ℝ):ℂ))
  have he := gaussian_heat_identity v hv x
  rw [← smoothing_distribution] at he
  have hn := congrArg norm he
  have hc : 0 < K*exp (-(2*(v:ℝ))⁻¹*x^2) := mul_pos hK (exp_pos _)
  have heq : smoothing epsilon x = K*exp (-(2*(v:ℝ))⁻¹*x^2)*‖H‖ := by
    change ‖(smoothing epsilon x:ℂ)‖ = ‖((K*exp (-(2*(v:ℝ))⁻¹*x^2):ℝ):ℂ)*H‖ at hn
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (smoothing_pos epsilon x),abs_of_pos hc] at hn
    exact hn
  have hH : 0 < ‖H‖ := by
    have hp := smoothing_pos epsilon x
    rw [heq] at hp
    exact (mul_pos_iff_of_pos_left hc).mp hp
  change log (smoothing epsilon x) = log K-(2*(v:ℝ))⁻¹*x^2+log ‖H‖
  rw [heq,Real.log_mul (ne_of_gt hc) (ne_of_gt hH),
    Real.log_mul (ne_of_gt hK) (exp_ne_zero _),Real.log_exp]
  ring

theorem smoothing_four_point
    (hall : ∀ t : ℝ, ∀ z : ℂ, RiemannEvenFlow.flow 1 t z = 0 → z.im = 0)
    (epsilon : ℝ) (hne : epsilon ≠ 0) (y : ℝ) (hy : 1 ≤ y) :
    let q : ℝ → ℝ := fun v => log (smoothing epsilon (sqrt v))
    q 1+(y-1)*(q 2-q 1)-2*(y-1)^2*(2*q (1/2)-q 0-q 1) ≤ q y := by
  let v : ℝ≥0 := ⟨epsilon^2,sq_nonneg epsilon⟩*2
  let A : ℝ := log (2*(sqrt (2*Real.pi*(v:ℝ)))⁻¹)
  let B : ℝ := (2*(v:ℝ))⁻¹
  let C : ℝ := 2*B
  have he (w : ℝ) (hw : 0 ≤ w) : log (smoothing epsilon (sqrt w)) =
      A-B*w+log ‖RiemannEvenFlow.flow 1 (-B) (Complex.I*((C*sqrt w:ℝ):ℂ))‖ := by
    have h := smoothing_log_heat epsilon hne (sqrt w)
    simpa only [Real.sq_sqrt hw] using h
  have hbound := NewmanFourPointBound.actual_flow_four_point 1 (-B) (hall (-B)) A B C y hy
  dsimp only at hbound ⊢
  rw [he 1 (by norm_num),he 2 (by norm_num),he (1/2) (by norm_num),he 0 le_rfl,
    he y (by linarith)]
  exact hbound

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticDensityHeat
