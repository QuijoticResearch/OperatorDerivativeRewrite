import Foundation.BurgersPhaseProductIntegral

/-! Actual mixed pressure derivatives and the full Hessian contraction with
the prescribed unit-core repaired vorticity. No induced perturbed pressure assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.BurgersRepairedHessian
open GaussianSwirlVelocity GaussianSwirlPressureDomain HelicalRadialGaussianBridge
open HelicalVorticityDiagnostics HelicalWeightedPressureIBP
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure physicalGaussian := by unfold physicalGaussian; infer_instance

def mixed (ν γ : ℝ) (q : ℝ × ℝ) : ℝ :=
  4*γ^2*q.1*q.2*angularProfile (radiusSq q)*angularDerivative (radiusSq q)

theorem hessian_xy (ν γ x y z : ℝ) : BurgersAxialPressureFlux.hessian ν γ x y z 0 1 =
    mixed ν γ (x,y) := by
  simp only [BurgersAxialPressureFlux.hessian, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]
  simp_rw [StrainedBurgersVortex.pressureGradient_eq]
  have hd := (((GaussianSwirlVelocity.profile_y x y).pow 2).const_mul (γ^2*x)).sub_const (4*ν^2*x)
  have hh : HasDerivAt
      (fun t => γ^2*x*angularProfile (x^2+t^2)^2-4*ν^2*x) (mixed ν γ (x,y)) y := by
    convert hd using 1 <;> (try funext t) <;> (try dsimp [mixed, radiusSq]) <;> ring
  exact hh.deriv

theorem hessian_yx (ν γ x y z : ℝ) : BurgersAxialPressureFlux.hessian ν γ x y z 1 0 =
    mixed ν γ (x,y) := by
  simp only [BurgersAxialPressureFlux.hessian, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]
  simp_rw [StrainedBurgersVortex.pressureGradient_eq]
  have hd := (((GaussianSwirlVelocity.profile_x x y).pow 2).const_mul (γ^2*y)).sub_const (4*ν^2*y)
  have hh : HasDerivAt
      (fun t => γ^2*y*angularProfile (t^2+y^2)^2-4*ν^2*y) (mixed ν γ (x,y)) x := by
    convert hd using 1 <;> (try funext t) <;> (try dsimp [mixed, radiusSq]) <;> ring
  exact hh.deriv

theorem hessian_eq (ν γ x y z : ℝ) : BurgersAxialPressureFlux.hessian ν γ x y z =
    ![![BurgersGaussianPressureResponse.Dxx ν γ (x,y), mixed ν γ (x,y), 0],
      ![mixed ν γ (x,y), BurgersGaussianPressureResponse.Dyy ν γ (x,y), 0],
      ![0,0,-16*ν^2] ] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change BurgersAxialPressureFlux.hessian ν γ x y z 0 0 =
      BurgersGaussianPressureResponse.Dxx ν γ (x,y)
    simpa [BurgersGaussianPressureResponse.Dxx, GaussianSwirlPressureDomain.Dxx, radiusSq]
      using BurgersAxialPressureFlux.hessian_xx ν γ x y z
  · exact hessian_xy ν γ x y z
  · simp [BurgersAxialPressureFlux.hessian, StrainedBurgersVortex.pressureGradient_eq]
  · exact hessian_yx ν γ x y z
  · change BurgersAxialPressureFlux.hessian ν γ x y z 1 1 =
      BurgersGaussianPressureResponse.Dyy ν γ (x,y)
    simpa [BurgersGaussianPressureResponse.Dyy, GaussianSwirlPressureDomain.Dyy, radiusSq]
      using BurgersAxialPressureFlux.hessian_yy ν γ x y z
  · simp [BurgersAxialPressureFlux.hessian, StrainedBurgersVortex.pressureGradient_eq]
  · simp [BurgersAxialPressureFlux.hessian, StrainedBurgersVortex.pressureGradient_eq]
  · simp [BurgersAxialPressureFlux.hessian, StrainedBurgersVortex.pressureGradient_eq]
  · exact BurgersAxialPressureFlux.hessian_zz ν γ x y z

theorem mixed_measurable (ν γ : ℝ) : Measurable (mixed ν γ) := by
  have hr : Measurable radiusSq := by unfold radiusSq; fun_prop
  exact (((measurable_const.mul measurable_fst).mul measurable_snd).mul
    (angularProfile_continuous.measurable.comp hr)).mul (angularDerivative_measurable.comp hr)

theorem mixed_bound (ν γ : ℝ) (q : ℝ × ℝ) :
    ‖mixed ν γ q‖ ≤ (γ^2/4)*radiusSq q := by
  have hr := radiusSq_nonneg q
  have hh := angular_bounds hr
  have hp := angular_pos hr
  have hd := angularDerivative_abs hr
  have hxy : |q.1*q.2| ≤ radiusSq q/2 := by
    rw [abs_le]
    dsimp [radiusSq]
    constructor <;> nlinarith [sq_nonneg (q.1-q.2), sq_nonneg (q.1+q.2)]
  have hb : ‖mixed ν γ q‖ ≤ (γ^2/2)* |q.1*q.2| := by
    rw [mixed, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (show 0 ≤ 4*γ^2 by positivity), abs_of_pos hp]
    calc
      _ ≤ (4*γ^2) * |q.1| * |q.2| * (1/2)*(1/4) := by
        gcongr
        exact hh.2
      _ = (γ^2/2)* |q.1*q.2| := by rw [abs_mul]; ring
  calc
    _ ≤ (γ^2/2)* |q.1*q.2| := hb
    _ ≤ (γ^2/2)*(radiusSq q/2) := mul_le_mul_of_nonneg_left hxy (by positivity)
    _ = _ := by ring

theorem mixed_integrable (ν γ : ℝ) : Integrable (mixed ν γ) physicalGaussian := by
  have hr := PressureDomainLinearCalculus.radius_domain.pressure_memLp.integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply (hr.const_mul (γ^2/4)).mono' (mixed_measurable ν γ).aestronglyMeasurable
  exact Eventually.of_forall (mixed_bound ν γ)

def pairing (ε ν γ : ℝ) (q : ℝ × ℝ) (θ : ℝ) : ℝ :=
  dotProduct (corrected ε q.1 q.2 θ)
    ((BurgersAxialPressureFlux.hessian ν γ q.1 q.2 θ).mulVec (corrected ε q.1 q.2 θ))

theorem pairing_expansion (ε ν γ : ℝ) (q : ℝ × ℝ) (θ : ℝ) : pairing ε ν γ q θ =
    (profile q.1 q.2)^2 *
      (ε^2*(Real.cos θ)^2*BurgersGaussianPressureResponse.Dxx ν γ q +
        2*ε^2*Real.sin θ*Real.cos θ*mixed ν γ q +
          ε^2*(Real.sin θ)^2*BurgersGaussianPressureResponse.Dyy ν γ q -
            16*ν^2*(1+2*ε*phase q.1 q.2 θ)^2) := by
  rw [pairing, hessian_eq]
  simp [corrected, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, phase]
  ring

end OperatorDerivativeRewrite.Foundation.BurgersRepairedHessian
