import Foundation.GaussianSwirlPressureDomain

/-! Linear closure of the actual weighted pressure domain, with its L2
representatives and elementary quadratic observations kept explicit. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.PressureDomainLinearCalculus
open HelicalRadialGaussianBridge HelicalPressureProjection HelicalWeightedPressureIBP
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure physicalGaussian := by unfold physicalGaussian; infer_instance

theorem linearCombination {P Px Py Pxx Pyy Q Qx Qy Qxx Qyy : ℝ × ℝ → ℝ}
    (a b : ℝ) (hP : PressureDomain P Px Py Pxx Pyy) (hQ : PressureDomain Q Qx Qy Qxx Qyy) :
    PressureDomain (fun x => a*P x+b*Q x) (fun x => a*Px x+b*Qx x)
      (fun x => a*Py x+b*Qy x) (fun x => a*Pxx x+b*Qxx x) (fun x => a*Pyy x+b*Qyy x) :=
  ⟨fun x y => ((hP.dx x y).const_mul a).add ((hQ.dx x y).const_mul b),
    fun x y => ((hP.dy x y).const_mul a).add ((hQ.dy x y).const_mul b),
    fun x y => ((hP.dxx x y).const_mul a).add ((hQ.dxx x y).const_mul b),
    fun x y => ((hP.dyy x y).const_mul a).add ((hQ.dyy x y).const_mul b),
    (hP.pressure_memLp.const_mul a).add (hQ.pressure_memLp.const_mul b),
    (hP.dx_memLp.const_mul a).add (hQ.dx_memLp.const_mul b),
    (hP.dy_memLp.const_mul a).add (hQ.dy_memLp.const_mul b),
    (hP.dxx_integrable.const_mul a).add (hQ.dxx_integrable.const_mul b),
    (hP.dyy_integrable.const_mul a).add (hQ.dyy_integrable.const_mul b)⟩

theorem pressureL2_linear {P Px Py Pxx Pyy Q Qx Qy Qxx Qyy : ℝ × ℝ → ℝ}
    (a b : ℝ) (hP : PressureDomain P Px Py Pxx Pyy) (hQ : PressureDomain Q Qx Qy Qxx Qyy) :
    pressureL2 (linearCombination a b hP hQ) = a • pressureL2 hP + b • pressureL2 hQ := by
  apply Lp.ext
  filter_upwards [pressureL2_ae (linearCombination a b hP hQ),
    Lp.coeFn_add (a • pressureL2 hP) (b • pressureL2 hQ),
    Lp.coeFn_smul a (pressureL2 hP), Lp.coeFn_smul b (pressureL2 hQ),
    pressureL2_ae hP, pressureL2_ae hQ] with x hc ha hs ht hp hq
  rw [hc, ha]
  simp only [Pi.add_apply, hs, ht, Pi.smul_apply, smul_eq_mul, hp, hq]

theorem constant_domain (c : ℝ) : PressureDomain (fun _ => c)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨fun x _ => hasDerivAt_const x c, fun _ y => hasDerivAt_const y c,
    fun x _ => hasDerivAt_const x 0, fun _ y => hasDerivAt_const y 0,
    memLp_const c, memLp_const 0, memLp_const 0, integrable_const 0, integrable_const 0⟩

theorem constant_response (c : ℝ) : physicalResponse (pressureL2 (constant_domain c)) = 0 := by
  rw [pressure_response]
  simp

theorem radius_domain : PressureDomain GaussianSwirlPressureDomain.radiusSq
    (fun x => 2*x.1) (fun x => 2*x.2) (fun _ => 2) (fun _ => 2) := by
  have hr : MemLp GaussianSwirlPressureDomain.radiusSq 2 physicalGaussian := by
    change MemLp (fun x : ℝ × ℝ => x.1^2+x.2^2) 2 physicalGaussian
    simpa only [GaussianSwirlPressureDomain.radiusSq, MvPolynomial.eval_add,
      MvPolynomial.eval_pow, MvPolynomial.eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] using
        HelicalPolynomialPressureIBP.polynomial_memLp
          (((MvPolynomial.X (0 : Fin 2) : HelicalPolynomialPressureIBP.PlanePolynomial)^(2 : ℕ))+
            ((MvPolynomial.X (1 : Fin 2) : HelicalPolynomialPressureIBP.PlanePolynomial)^(2 : ℕ)))
          2 (by simp)
  have hx : MemLp (fun x : ℝ × ℝ => x.1) 2 physicalGaussian := by
    simpa using HelicalPolynomialPressureIBP.polynomial_memLp (MvPolynomial.X (0 : Fin 2)) 2
      (by simp)
  have hy : MemLp (fun x : ℝ × ℝ => x.2) 2 physicalGaussian := by
    simpa using HelicalPolynomialPressureIBP.polynomial_memLp (MvPolynomial.X (1 : Fin 2)) 2
      (by simp)
  refine ⟨?_, ?_, ?_, ?_, hr, hx.const_mul 2, hy.const_mul 2,
    integrable_const 2, integrable_const 2⟩
  · intro x y
    simpa [GaussianSwirlPressureDomain.radiusSq] using (hasDerivAt_pow 2 x).add_const (y^2)
  · intro x y
    simpa [GaussianSwirlPressureDomain.radiusSq] using (hasDerivAt_pow 2 y).const_add (x^2)
  · intro x y
    simpa using (hasDerivAt_id x).const_mul 2
  · intro x y
    simpa using (hasDerivAt_id y).const_mul 2

theorem radius_response : physicalResponse (pressureL2 radius_domain) = 1/2 := by
  rw [pressure_response]
  simp
  norm_num

end OperatorDerivativeRewrite.Foundation.PressureDomainLinearCalculus
