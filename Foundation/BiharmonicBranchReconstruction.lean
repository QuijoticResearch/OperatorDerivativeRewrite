import Foundation.GaussianComplexPolynomialIto
import Foundation.GaussianPolynomialMartingale
/-! Actual branch-conditional polynomial Clark--Ocone with the necessary phase residual.
Uses the existing closed Gaussian derivative and original predictable integral. -/
noncomputable section
open MeasureTheory Polynomial Complex Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BiharmonicBranchReconstruction
open OperatorDerivativeRewrite.Foundation InfiniteGaussian GaussianComplexPolynomialIto
open GaussianScalarPolynomialIto GaussianPredictableAdjoint GaussianConditionalClarkOcone
open GaussianConditionalIto GaussianBrownianPRP ComplexL2Isometry

def representer (T : ℝ≥0) (Q : ℂ[X]) : Native :=
 (predictableAdjoint (polynomialValue T (realPolynomial Q)),
  predictableAdjoint (polynomialValue T (imagPolynomial Q)))

def average (T : ℝ≥0) (Q : ℂ[X]) : ℂ :=
 (∫ w, polynomialValue T (realPolynomial Q) w ∂gaussianProduct)+
   I*(∫ w, polynomialValue T (imagPolynomial Q) w ∂gaussianProduct)

theorem polynomial_past (T : ℝ≥0) (P : ℝ[X]) : polynomialValue T P∈pastL2 T :=
 GaussianPolynomialMartingale.valueL2_mem_past _ T

theorem native_integral_injective : Function.Injective GaussianComplexPolynomialIto.integral := by
 intro U V h
 apply Prod.ext
 · apply GaussianPredictableFull.itoIntegral.injective
   have he:=congrArg (realPart gaussianProduct) h
   simpa only [GaussianComplexPolynomialIto.integral,realPart_combine] using he
 · apply GaussianPredictableFull.itoIntegral.injective
   have he:=congrArg (imagPart gaussianProduct) h
   simpa only [GaussianComplexPolynomialIto.integral,imagPart_combine] using he

theorem constant_parts (a b : ℝ) :
 constant ((a:ℂ)+I*(b:ℂ))=complexify (a • gaussianOne,b • gaussianOne) := by
 simp [constant,Complex.mul_re,Complex.mul_im,complexify_apply]

theorem polynomial_reconstruction (T : ℝ≥0) (Q : ℂ[X]) :
 GaussianComplexPolynomialIto.integral (representer T Q)=value T Q-constant (average T Q) := by
 have hr:=brownian_representation (polynomialValue T (realPolynomial Q))
   (past_mem_brownian T (polynomial_past T _))
 have hi:=brownian_representation (polynomialValue T (imagPolynomial Q))
   (past_mem_brownian T (polynomial_past T _))
 change complexify (GaussianPredictableFull.itoIntegral (predictableAdjoint (polynomialValue T (realPolynomial Q))),
   GaussianPredictableFull.itoIntegral (predictableAdjoint (polynomialValue T (imagPolynomial Q))))=_
 rw [hr,hi]
 change complexify ((polynomialValue T (realPolynomial Q),polynomialValue T (imagPolynomial Q))-
   ((∫ w, polynomialValue T (realPolynomial Q) w ∂gaussianProduct) • gaussianOne,
    (∫ w, polynomialValue T (imagPolynomial Q) w ∂gaussianProduct) • gaussianOne))=_
 rw [map_sub]
 rw [average,constant_parts]
 rfl

theorem unique_reconstruction (T : ℝ≥0) (Q : ℂ[X]) : ∃! U : Native,
 GaussianComplexPolynomialIto.integral U=value T Q-constant (average T Q) := by
 exact ⟨representer T Q,polynomial_reconstruction T Q,fun U h =>
   native_integral_injective (h.trans (polynomial_reconstruction T Q).symm)⟩

theorem average_eq_integral (T : ℝ≥0) (Q : ℂ[X]) :
 average T Q=∫ w, value T Q w ∂gaussianProduct := by
 have hv : Integrable (value T Q) gaussianProduct := (Lp.memLp (value T Q)).integrable (by norm_num)
 have hr : (fun w => (value T Q w).re)=ᵐ[gaussianProduct] polynomialValue T (realPolynomial Q) := by
  filter_upwards [combine_ae gaussianProduct (polynomialValue T (realPolynomial Q))
    (polynomialValue T (imagPolynomial Q))] with w hw
  change (combine gaussianProduct _ _ w).re=_
  rw [hw]
  simp
 have hi : (fun w => (value T Q w).im)=ᵐ[gaussianProduct] polynomialValue T (imagPolynomial Q) := by
  filter_upwards [combine_ae gaussianProduct (polynomialValue T (realPolynomial Q))
    (polynomialValue T (imagPolynomial Q))] with w hw
  change (combine gaussianProduct _ _ w).im=_
  rw [hw]
  simp
 symm
 apply Complex.ext
 · calc
    _ = ∫ w, (value T Q w).re ∂gaussianProduct := (Complex.reCLM.integral_comp_comm hv).symm
    _ = ∫ w, polynomialValue T (realPolynomial Q) w ∂gaussianProduct := integral_congr_ae hr
    _ = _ := by simp [average]
 · calc
    _ = ∫ w, (value T Q w).im ∂gaussianProduct := (Complex.imCLM.integral_comp_comm hv).symm
    _ = ∫ w, polynomialValue T (imagPolynomial Q) w ∂gaussianProduct := integral_congr_ae hi
    _ = _ := by simp [average]

theorem branch_average (T : ℝ≥0) (b : Bool) (P : ℝ[X]) :
 average T (branchPolynomial b P)=BiharmonicGaussianBranches.mean T P+
  (BiharmonicGaussianBranches.sign b:ℂ)*BiharmonicGaussianBranches.contrast T P := by
 rw [average_eq_integral]
 change (∫ w, branchValue T b P w ∂gaussianProduct)=_
 rw [integral_congr_ae (branchValue_coeFn T b P)]
 have he:=BiharmonicGaussianBranches.branch_integral T b P
 change (∫ w, (P.map (algebraMap ℝ ℂ)).eval
   (BiharmonicGaussianBranches.phase b*(IBMConstructedSources.clockPath w T:ℂ)) ∂gaussianProduct)=_ at he
 simp only [BiharmonicGaussianBranches.value_eq]
 rw [he,BiharmonicGaussianBranches.mean_apply,BiharmonicGaussianBranches.contrast_apply]
 cases b <;> simp only [BiharmonicGaussianBranches.phase,BiharmonicGaussianBranches.sign,
   Bool.false_eq_true,ite_false,ite_true,Complex.ofReal_neg,Complex.ofReal_one]
 · change BiharmonicGaussianBranches.minus T P=_
   ring
 · change BiharmonicGaussianBranches.plus T P=_
   ring

theorem branch_reconstruction (T : ℝ≥0) (b : Bool) (P : ℝ[X]) :
 ∃! U : Native, GaussianComplexPolynomialIto.integral U=branchValue T b P-
   constant (BiharmonicGaussianBranches.mean T P+
    (BiharmonicGaussianBranches.sign b:ℂ)*BiharmonicGaussianBranches.contrast T P) := by
 simpa only [branch_average,branchValue] using unique_reconstruction T (branchPolynomial b P)

def polynomialDomain (T : ℝ≥0) (P : ℝ[X]) : closedCylindricalDerivative.domain :=
 ⟨polynomialValue T P,closedCylindricalDerivative_core_mem
   (GaussianTimeDivergence.pastCoefficient (fun _ : Unit => T)
    (GaussianPolynomialHeat.specialize T (GaussianPolynomialDifferentiation.spatialPolynomial P)))⟩

theorem representer_projected_derivative (T : ℝ≥0) (Q : ℂ[X]) : representer T Q=
 (predictableProjection (closedCylindricalDerivative (polynomialDomain T (realPolynomial Q))),
  predictableProjection (closedCylindricalDerivative (polynomialDomain T (imagPolynomial Q)))) := by
 apply Prod.ext
 · exact predictableAdjoint_eq_projected_derivative (polynomialDomain T (realPolynomial Q))
 · exact predictableAdjoint_eq_projected_derivative (polynomialDomain T (imagPolynomial Q))

theorem representer_supported (T : ℝ≥0) (Q : ℂ[X]) :
 (GaussianPredictableCutoff.predictableCut T (representer T Q).1,
  GaussianPredictableCutoff.predictableCut T (representer T Q).2)=representer T Q := by
 apply Prod.ext
 · exact past_representer_supported T _ (polynomial_past T _)
 · exact past_representer_supported T _ (polynomial_past T _)

theorem constant_add (a b : ℂ) : constant (a+b)=constant a+constant b := by
 change complexify ((a+b).re • gaussianOne,(a+b).im • gaussianOne)=
   complexify (a.re • gaussianOne,a.im • gaussianOne)+complexify (b.re • gaussianOne,b.im • gaussianOne)
 rw [←map_add]
 congr 1
 ext <;> simp [add_smul]

theorem branch_residual_reconstruction (T : ℝ≥0) (b : Bool) (P : ℝ[X]) :
 branchValue T b P-constant (BiharmonicGaussianBranches.mean T P)=
 constant ((BiharmonicGaussianBranches.sign b:ℂ)*BiharmonicGaussianBranches.contrast T P)+
  GaussianComplexPolynomialIto.integral (representer T (branchPolynomial b P)) := by
 have h:=polynomial_reconstruction T (branchPolynomial b P)
 rw [branch_average,constant_add] at h
 change GaussianComplexPolynomialIto.integral (representer T (branchPolynomial b P))=
  branchValue T b P-_ at h
 rw [h]
 abel

theorem reconstruction_energy (T : ℝ≥0) (Q : ℂ[X]) :
 ‖value T Q-constant (average T Q)‖^2=‖field (representer T Q)‖^2 := by
 rw [←polynomial_reconstruction,integral_norm_sq]

theorem constant_coeFn (z : ℂ) : constant z=ᵐ[gaussianProduct] fun _ => z := by
 filter_upwards [combine_ae gaussianProduct (z.re • gaussianOne) (z.im • gaussianOne),
   Lp.coeFn_smul z.re gaussianOne,Lp.coeFn_smul z.im gaussianOne,gaussianOne_coeFn]
   with w hc hr hi h1
 change combine gaussianProduct _ _ w=_
 rw [hc,hr,hi,Pi.smul_apply,Pi.smul_apply,h1]
 simp only [smul_eq_mul,mul_one]
 simpa only [mul_comm] using Complex.re_add_im z

theorem constant_integral (z : ℂ) : (∫ w, constant z w ∂gaussianProduct)=z := by
 rw [integral_congr_ae (constant_coeFn z),integral_const]
 simp

theorem value_sub_constant_integral (T : ℝ≥0) (Q : ℂ[X]) (z : ℂ) :
 (∫ w, (value T Q-constant z) w ∂gaussianProduct)=average T Q-z := by
 have hF : Integrable (value T Q) gaussianProduct := (Lp.memLp _).integrable (by norm_num)
 have hc : Integrable (constant z) gaussianProduct := (Lp.memLp _).integrable (by norm_num)
 rw [integral_congr_ae (Lp.coeFn_sub (value T Q) (constant z))]
 simp only [Pi.sub_apply]
 rw [integral_sub hF hc,
   constant_integral,←average_eq_integral]

theorem branch_centered_native_iff (T : ℝ≥0) (b : Bool) (P : ℝ[X]) :
 (∃ U : Native, GaussianComplexPolynomialIto.integral U=
   branchValue T b P-constant (BiharmonicGaussianBranches.mean T P)) ↔
 BiharmonicGaussianBranches.contrast T P=0 := by
 constructor
 · rintro ⟨U,hU⟩
   have hz:=integral_centered U
   rw [hU] at hz
   change (∫ w, (value T (branchPolynomial b P)-constant (BiharmonicGaussianBranches.mean T P)) w
     ∂gaussianProduct)=0 at hz
   rw [value_sub_constant_integral,branch_average,add_sub_cancel_left] at hz
   have hb : (BiharmonicGaussianBranches.sign b:ℂ)≠0 := by
     cases b <;> norm_num [BiharmonicGaussianBranches.sign]
   exact (mul_eq_zero.mp hz).resolve_left hb
 · intro hC
   refine ⟨representer T (branchPolynomial b P),?_⟩
   have h:=polynomial_reconstruction T (branchPolynomial b P)
   simpa only [branch_average,hC,mul_zero,add_zero,branchValue] using h

theorem branch_clark_ocone (T : ℝ≥0) (b : Bool) (P : ℝ[X]) :
 branchValue T b P-constant (BiharmonicGaussianBranches.mean T P)=
 constant ((BiharmonicGaussianBranches.sign b:ℂ)*BiharmonicGaussianBranches.contrast T P)+
 GaussianComplexPolynomialIto.integral
 (predictableProjection (closedCylindricalDerivative
    (polynomialDomain T (realPolynomial (branchPolynomial b P)))),
  predictableProjection (closedCylindricalDerivative
    (polynomialDomain T (imagPolynomial (branchPolynomial b P))))) := by
 rw [←representer_projected_derivative]
 exact branch_residual_reconstruction T b P

theorem contrast_fourfold (T : ℝ≥0) (n : ℕ) : BiharmonicGaussianBranches.contrast T (X^(4*n))=0 := by
 rw [BiharmonicGaussianBranches.contrast_apply]
 change (ComplexGaussianPolynomialTransport.average (T/2) 0 (1+I) (X^(4*n))-
   ComplexGaussianPolynomialTransport.average (T/2) 0 (1-I) (X^(4*n)))/2=0
 rw [BiharmonicGaussianBranches.branch_power,BiharmonicGaussianBranches.branch_power,
   pow_mul,pow_mul,BiharmonicGaussianBranches.phase_fourth_plus,BiharmonicGaussianBranches.phase_fourth_minus]
 ring

theorem fourfold_centered_reconstruction (T : ℝ≥0) (b : Bool) (n : ℕ) :
 ∃! U : Native, GaussianComplexPolynomialIto.integral U=branchValue T b (X^(4*n))-
  constant (BiharmonicGaussianBranches.mean T (X^(4*n))) := by
 simpa only [contrast_fourfold,mul_zero,add_zero] using branch_reconstruction T b (X^(4*n))
end OperatorDerivativeRewrite.Foundation.BiharmonicBranchReconstruction
