import Foundation.CubeGaussianSquareChannel

/-! Genuine common-root squared mass, before the original-coordinate Schur bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianSquareRoot
open CubeGaussianModes CubeGaussianChannelGround CubeGaussianSquareChannel CubeChartAction
open SU2GaussianConeCoordinates SU2HemisphereJets QuaternionSU2Representation
attribute [local irreducible] channel SU2RootAdjoint.rotate

def fixedKernel (c : SU2) (p : Boundary × Boundary) : ℝ :=
  ∏ i : Fin 5,Real.exp (-channel i (p.1 i) (p.2 i) c)

def density (c : SU2) (p : Boundary × Boundary) : ℝ := (fixedKernel c p)^2

def factorBound : ℝ := ∏ i : Fin 5,((precision i+width i)/(2*width i))^3

def squareMass : ℝ := stateMass^2*factorBound

theorem density_product (c : SU2) (p : Boundary × Boundary) :
    density c p=∏ i : Fin 5,(Real.exp (-channel i (p.1 i) (p.2 i) c))^2 := by
  simp only [density,fixedKernel,Finset.prod_pow]

theorem fixedKernel_continuous :
    Continuous (fun p : SU2 × (Boundary × Boundary) => fixedKernel p.1 p.2) := by
  unfold fixedKernel
  apply continuous_finset_prod
  intro i _
  have hx : Continuous (fun p : SU2 × (Boundary × Boundary) => p.2.1 i) := by fun_prop
  have hy : Continuous (fun p : SU2 × (Boundary × Boundary) => p.2.2 i) := by fun_prop
  have hr := SU2RootEuclideanMeasure.rotate_joint_continuous.comp (continuous_fst.prodMk hy)
  have hs : Continuous sizeSq := by unfold sizeSq; fun_prop
  have hd := hs.comp (hx.sub hr)
  have hxs := hs.comp hx
  have hys := hs.comp hy
  unfold channel
  exact Real.continuous_exp.comp (continuous_const.mul
    ((continuous_const.mul (hxs.add hys)).add (continuous_const.mul hd))).neg

theorem density_continuous :
    Continuous (fun p : SU2 × (Boundary × Boundary) => density p.1 p.2) :=
  fixedKernel_continuous.pow 2

theorem fixed_row_integrable (c : SU2) (x : Boundary) :
    Integrable (fun y : Boundary => density c (x,y)) := by
  simp_rw [density_product]
  rw [volume_pi]
  exact Integrable.fintype_prod (fun i => squared_row_integrable i (x i) c)

theorem fixed_row_integral (c : SU2) (x : Boundary) :
    (∫ y : Boundary,density c (x,y))=
      ∏ i : Fin 5,Real.exp (-residualPrecision i*sizeSq (x i))*gaussianMass (2*precision i) := by
  simp_rw [density_product]
  rw [integral_fintype_prod_volume_eq_prod
    (fun (i : Fin 5) (y : Triple) => (Real.exp (-channel i (x i) y c))^2)]
  simp_rw [squared_row_integral]

theorem fixed_integrable (c : SU2) : Integrable (density c) := by
  have hc : Continuous (density c) :=
    density_continuous.comp ((continuous_const (y := c)).prodMk continuous_id)
  apply (integrable_prod_iff hc.measurable.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fixed_row_integrable c)
  · have he : (fun x : Boundary => ∫ y : Boundary,‖density c (x,y)‖)=
        (fun x : Boundary => ∏ i : Fin 5,
          Real.exp (-residualPrecision i*sizeSq (x i))*gaussianMass (2*precision i)) := by
      funext x
      have hn (y : Boundary) : ‖density c (x,y)‖=density c (x,y) :=
        by rw [Real.norm_eq_abs]; exact abs_of_nonneg (sq_nonneg _)
      simp_rw [hn]
      exact fixed_row_integral c x
    rw [he,volume_pi]
    exact Integrable.fintype_prod (fun i =>
      (gaussian_integrable _ (residualPrecision_positive i)).mul_const _)

theorem fixed_integral (c : SU2) : (∫ p : Boundary × Boundary,density c p)=squareMass := by
  change (∫ p : Boundary × Boundary,density c p ∂(volume.prod volume))=_
  rw [integral_prod _ (fixed_integrable c)]
  simp_rw [fixed_row_integral]
  rw [integral_fintype_prod_volume_eq_prod (fun (i : Fin 5) (x : Triple) =>
    Real.exp (-residualPrecision i*sizeSq x)*gaussianMass (2*precision i))]
  have hi (i : Fin 5) :
      (∫ x : Triple,Real.exp (-residualPrecision i*sizeSq x)*gaussianMass (2*precision i))=
        (gaussianMass (precision i+width i))^2*((precision i+width i)/(2*width i))^3 := by
    rw [integral_mul_const]
    exact (mul_comm _ _).trans (gaussianMass_pair i)
  simp_rw [hi]
  rw [Finset.prod_mul_distrib,Finset.prod_pow]
  rfl

theorem joint_integrable :
    Integrable (fun p : SU2 × (Boundary × Boundary) => density p.1 p.2)
      (law.prod (volume : Measure (Boundary × Boundary))) := by
  apply (integrable_prod_iff density_continuous.measurable.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all law fixed_integrable
  · have he : (fun c : SU2 => ∫ p : Boundary × Boundary,‖density c p‖)=
        (fun _ : SU2 => squareMass) := by
      funext c
      have hn (p : Boundary × Boundary) : ‖density c p‖=density c p := by rw [Real.norm_eq_abs]; exact abs_of_nonneg (sq_nonneg _)
      simp_rw [hn]
      exact fixed_integral c
    rw [he]
    exact integrable_const _

def averageSquare (p : Boundary × Boundary) : ℝ := ∫ c : SU2,density c p ∂law

theorem averageSquare_integrable : Integrable averageSquare := joint_integrable.integral_prod_right

theorem averageSquare_integral : (∫ p : Boundary × Boundary,averageSquare p)=squareMass := by
  unfold averageSquare
  rw [← integral_integral_swap joint_integrable]
  simp_rw [fixed_integral]
  simp

theorem fixedKernel_bound (c : SU2) (p : Boundary × Boundary) : |fixedKernel c p| ≤ 1 := by
  unfold fixedKernel
  rw [abs_of_pos (Finset.prod_pos (fun i _ => Real.exp_pos _))]
  apply Finset.prod_le_one₀
  · intro i _
    exact (Real.exp_pos _).le
  · intro i _
    apply Real.exp_le_one_iff.mpr
    apply neg_nonpos.mpr
    unfold channel
    have hw := weights_positive i
    have hm := orders_positive i
    have hx := sizeSq_nonneg (p.1 i)
    have hy := sizeSq_nonneg (p.2 i)
    have hd := sizeSq_nonneg (p.1 i-SU2RootAdjoint.rotate c (p.2 i))
    positivity

theorem root_jensen (p : Boundary × Boundary) :
    (∫ c : SU2,fixedKernel c p ∂law)^2 ≤ averageSquare p := by
  have hc : Continuous (fun c : SU2 => fixedKernel c p) :=
    fixedKernel_continuous.comp (continuous_id.prodMk (continuous_const (y := p)))
  have hm : MemLp (fun c : SU2 => fixedKernel c p) 2 law :=
    MemLp.of_bound hc.measurable.aestronglyMeasurable 1
      (ae_of_all law (fun c => by simpa only [Real.norm_eq_abs] using fixedKernel_bound c p))
  have h := variance_nonneg (fun c : SU2 => fixedKernel c p) law
  rw [variance_eq_sub hm] at h
  change 0 ≤ averageSquare p-(∫ c : SU2,fixedKernel c p ∂law)^2 at h
  linarith

end OperatorDerivativeRewrite.Foundation.CubeGaussianSquareRoot
