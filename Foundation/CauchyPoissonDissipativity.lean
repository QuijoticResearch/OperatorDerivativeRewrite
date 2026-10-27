import Foundation.CauchyPoissonNonSymmetry
/-! Actual weighted finite-core energy identity and dissipativity for the
Cauchy generator with sine drift under its Poisson-kernel law. No reversibility,
closed generator domain or semigroup construction is assumed or asserted. -/
noncomputable section
open MeasureTheory Complex
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonDissipativity
open OperatorDerivativeRewrite.Foundation
open CauchyPoissonCoreInvariant CauchyPoissonNonSymmetry
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierReality
open FiniteStableGamma.Core CauchySineDrift BrownianEnergyRepair.Torus

theorem single_drift_axis (r : ℝ) (k : Wave) (c : ℂ) (θ : ℝ) :
    synthesis ![θ,0,0] (drift r (AddMonoidAlgebra.single k c)) =
      synthesis ![θ,0,0] (drift r (AddMonoidAlgebra.single (axisWave (k 0)) c)) := by
  simp [drift,generator_single,transport_single,map_add,map_sub,synthesis_single,
    character,phase,Fin.sum_univ_three,stableSymbol,axisWave,unitWave,Matrix.vecHead]

theorem actual_core_balance (q : ℝ) (hq : |q| < 1) (f : Fourier) :
    (∫ θ, synthesis ![θ,0,0] (drift (2*q/(1-q^2)) f) ∂law q) = 0 := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [drift,transport]
  | add f g hf hg =>
    have he : drift (2*q/(1-q^2)) (f+g) = drift (2*q/(1-q^2)) f+drift (2*q/(1-q^2)) g := by
      simp [drift,transport_add,smul_add]; abel
    simp_rw [he,map_add]
    rw [integral_add (synthesis_law_integrable q hq _) (synthesis_law_integrable q hq _),hf,hg,add_zero]
  | single k c =>
    calc
      _ = ∫ θ, synthesis ![θ,0,0]
        (drift (2*q/(1-q^2)) (AddMonoidAlgebra.single (axisWave (k 0)) c)) ∂law q :=
          integral_congr_ae (Filter.Eventually.of_forall (fun θ => single_drift_axis _ k c θ))
      _ = 0 := actual_integer_coefficient_balance q hq (k 0) c

theorem drift_gamma (r : ℝ) (f g : Fourier) :
    firstGamma (drift r) f g = gammaIter (stableSymbol 1) 1 f g := by
  unfold drift
  simp only [complex_real_smul]
  exact (firstGamma_scaled_transport r (generator (stableSymbol 1)) f g).trans
    (firstGamma_generator (stableSymbol 1) f g)

theorem finite_representation (f : Fourier) :
    (∑ k : f.coeff.support, AddMonoidAlgebra.single k.val (f.coeff k.val)) = f := by
  exact (Finset.sum_attach f.coeff.support (fun k => AddMonoidAlgebra.single k (f.coeff k))).trans
    (AddMonoidAlgebra.sum_coeff_single f)

theorem gamma_nonnegative (f : Fourier) (x : Space) :
    (synthesis x (gammaIter (stableSymbol 1) 1 f f)).im = 0 ∧
      0 ≤ (synthesis x (gammaIter (stableSymbol 1) 1 f f)).re := by
  have h := FiniteStableGamma.Bridge.stable_gamma_nonnegative
    1 (by norm_num) (by norm_num) 1 (fun k : f.coeff.support => k.val)
    (fun k => f.coeff k.val) x
  simpa only [finite_representation] using h

def lawFunctional (q : ℝ) (hq : |q| < 1) : Fourier →ₗ[ℂ] ℂ where
  toFun f := ∫ θ, synthesis ![θ,0,0] f ∂law q
  map_add' f g := by
    simp only [map_add]
    exact integral_add (synthesis_law_integrable q hq f) (synthesis_law_integrable q hq g)
  map_smul' c f := by
    simp only [map_smul]
    exact integral_smul c _

theorem weighted_gamma_pairing (q : ℝ) (hq : |q| < 1) (f g : Fourier) :
    lawFunctional q hq (gammaIter (stableSymbol 1) 1 f g) =
      -(1/2:ℂ) * (lawFunctional q hq (reflection (drift (2*q/(1-q^2)) f)*g) +
        lawFunctional q hq (reflection f*drift (2*q/(1-q^2)) g)) := by
  rw [← drift_gamma (2*q/(1-q^2)),firstGamma,map_smul,map_sub,map_sub]
  have hz : lawFunctional q hq (drift (2*q/(1-q^2)) (reflection f*g)) = 0 :=
    actual_core_balance q hq (reflection f*g)
  rw [hz]
  simp only [smul_eq_mul]
  ring

theorem weighted_conjugate_pairing (q : ℝ) (hq : |q| < 1) (f g : Fourier) :
    lawFunctional q hq (reflection g*f) = starRingEnd ℂ (lawFunctional q hq (reflection f*g)) := by
  change (∫ θ, synthesis ![θ,0,0] (reflection g*f) ∂law q) =
    starRingEnd ℂ (∫ θ, synthesis ![θ,0,0] (reflection f*g) ∂law q)
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun θ => by
    simp [synthesis_mul,synthesis_reflection,mul_comm])

theorem weighted_energy_identity (q : ℝ) (hq : |q| < 1) (f : Fourier) :
    (lawFunctional q hq (gammaIter (stableSymbol 1) 1 f f)).re =
      -(lawFunctional q hq (reflection f*drift (2*q/(1-q^2)) f)).re := by
  have h := weighted_gamma_pairing q hq f f
  rw [weighted_conjugate_pairing] at h
  have hr := congrArg Complex.re h
  simp only [Complex.mul_re,Complex.add_re,Complex.add_im,Complex.conj_re,Complex.conj_im] at hr
  norm_num at hr
  linear_combination hr

theorem weighted_dissipativity (q : ℝ) (hq : |q| < 1) (f : Fourier) :
    (lawFunctional q hq (reflection f*drift (2*q/(1-q^2)) f)).re ≤ 0 := by
  have hn : 0 ≤ (lawFunctional q hq (gammaIter (stableSymbol 1) 1 f f)).re := by
    change 0 ≤ (∫ θ, synthesis ![θ,0,0] (gammaIter (stableSymbol 1) 1 f f) ∂law q).re
    have hp : 0 ≤ ∫ θ, (synthesis ![θ,0,0] (gammaIter (stableSymbol 1) 1 f f)).re ∂law q :=
      integral_nonneg (fun θ => (gamma_nonnegative f ![θ,0,0]).2)
    exact hp.trans_eq (integral_re (synthesis_law_integrable q hq (gammaIter (stableSymbol 1) 1 f f)))
  rw [weighted_energy_identity] at hn
  linarith
end OperatorDerivativeRewrite.Foundation.CauchyPoissonDissipativity
