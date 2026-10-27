import Foundation.WaveDiagonalSemigroup
import Foundation.FiniteFourierTorusAverage
import Foundation.FiniteStableGamma
/-! Exact normalized physical-torus Parseval, generator energy, and integrated
Gamma-one identity for every finite three-coordinate Fourier polynomial.
This is a finite core theorem, not a completed Haar-L2 or Markov realization. -/
open scoped ComplexConjugate
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.WavePhysicalFourierBridge
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
open FiniteFourierTorusAverage FiniteStableGamma.Core FiniteFourierReality
open WaveDiagonalSemigroup AnisotropicStableGamma

def polynomial {ι : Type*} [Fintype ι] (k : ι → Wave) (c : ι → ℂ) : Fourier :=
  ∑ i, AddMonoidAlgebra.single (k i) (c i)

theorem box_inner {ι : Type*} [Fintype ι] (k : ι → Wave) (hk : Function.Injective k)
    (c d : ι → ℂ) :
    boxAverage (fun x => conj (synthesis x (polynomial k c)) *
      synthesis x (polynomial k d)) = ∑ i, conj (c i)*d i := by
  classical
  have he : (fun x => conj (synthesis x (polynomial k c)) *
      synthesis x (polynomial k d)) =
      fun x => synthesis x (gammaIter (fun _ : Wave => 0) 0
        (polynomial k c) (polynomial k d)) := by
    funext x
    simp [gammaIter,synthesis_mul,synthesis_reflection]
  rw [he, boxAverage_synthesis]
  unfold polynomial
  rw [gammaIter_finite]
  simp [map_sum,constantTrace_apply,Finsupp.single_apply,sub_eq_zero,hk.eq_iff]

theorem box_parseval {ι : Type*} [Fintype ι] (k : ι → Wave) (hk : Function.Injective k)
    (c : ι → ℂ) :
    boxAverage (fun x => conj (synthesis x (polynomial k c)) *
      synthesis x (polynomial k c)) = ∑ i, conj (c i)*c i :=
  box_inner k hk c c

theorem generator_polynomial {ι : Type*} [Fintype ι] (a : Wave → ℝ)
    (k : ι → Wave) (c : ι → ℂ) :
    generator a (polynomial k c) =
      polynomial k (fun i => -(a (k i) : ℂ)*c i) := by
  simp [polynomial,map_sum,generator_single]

theorem box_generator_energy {ι : Type*} [Fintype ι] (a : Wave → ℝ)
    (k : ι → Wave) (hk : Function.Injective k) (c : ι → ℂ) :
    -boxAverage (fun x => conj (synthesis x (polynomial k c)) *
      synthesis x (generator a (polynomial k c))) =
      ∑ i, (a (k i) : ℂ)*(conj (c i)*c i) := by
  rw [generator_polynomial, box_inner k hk]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem box_energy_nonnegative {ι : Type*} [Fintype ι] (a : Wave → ℝ)
    (ha : ∀ w, 0 ≤ a w) (k : ι → Wave) (hk : Function.Injective k)
    (c : ι → ℂ) :
    0 ≤ (-boxAverage (fun x => conj (synthesis x (polynomial k c)) *
      synthesis x (generator a (polynomial k c)))).re := by
  rw [box_generator_energy a k hk c]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im,zero_mul,sub_zero]
  apply Finset.sum_nonneg
  intro i hi
  have h0 := ha (k i)
  have hs : 0 ≤ (c i).re^2+(c i).im^2 := by positivity
  nlinarith [mul_nonneg h0 hs]

theorem polynomial_support (f : Fourier) :
    polynomial (fun i : f.coeff.support => i.val)
      (fun i => f.coeff i.val) = f := by
  classical
  change (∑ i : f.coeff.support,
    AddMonoidAlgebra.single i.val (f.coeff i.val)) = f
  exact (Finset.sum_attach f.coeff.support
    (fun k => AddMonoidAlgebra.single k (f.coeff k))).trans
    (AddMonoidAlgebra.sum_coeff_single f)

theorem box_parseval_all (f : Fourier) :
    boxAverage (fun x => conj (synthesis x f)*synthesis x f) =
      ∑ k ∈ f.coeff.support, conj (f.coeff k)*f.coeff k := by
  classical
  have h := box_parseval (fun i : f.coeff.support => i.val)
    Subtype.val_injective (fun i => f.coeff i.val)
  rw [polynomial_support] at h
  exact h.trans (Finset.sum_attach f.coeff.support
    (fun k => conj (f.coeff k)*f.coeff k))

theorem box_generator_energy_all (a : Wave → ℝ) (f : Fourier) :
    -boxAverage (fun x => conj (synthesis x f)*synthesis x (generator a f)) =
      ∑ k ∈ f.coeff.support, (a k : ℂ)*(conj (f.coeff k)*f.coeff k) := by
  classical
  have h := box_generator_energy a (fun i : f.coeff.support => i.val)
    Subtype.val_injective (fun i => f.coeff i.val)
  rw [polynomial_support] at h
  exact h.trans (Finset.sum_attach f.coeff.support
    (fun k => (a k : ℂ)*(conj (f.coeff k)*f.coeff k)))

theorem box_energy_nonnegative_all (a : Wave → ℝ) (ha : ∀ w, 0 ≤ a w)
    (f : Fourier) :
    0 ≤ (-boxAverage (fun x => conj (synthesis x f)*
      synthesis x (generator a f))).re := by
  classical
  have h := box_energy_nonnegative a ha
    (fun i : f.coeff.support => i.val) Subtype.val_injective
    (fun i => f.coeff i.val)
  rw [polynomial_support] at h
  exact h

theorem box_gamma1_finite {ι : Type*} [Fintype ι] (a : Wave → ℝ)
    (ha0 : a 0 = 0) (k : ι → Wave) (hk : Function.Injective k)
    (c : ι → ℂ) :
    boxAverage (fun x => synthesis x (gammaIter a 1
      (polynomial k c) (polynomial k c))) =
      ∑ i, (a (k i) : ℂ)*(conj (c i)*c i) := by
  classical
  rw [boxAverage_synthesis]
  unfold polynomial
  rw [gammaIter_finite]
  simp [map_sum,constantTrace_apply,Finsupp.single_apply,
    sub_eq_zero,hk.eq_iff,kernel,ha0]
  simp [mul_assoc]

theorem box_gamma1_energy (a : Wave → ℝ) (ha0 : a 0 = 0)
    (f : Fourier) :
    boxAverage (fun x => synthesis x (gammaIter a 1 f f)) =
      -boxAverage (fun x => conj (synthesis x f)*
        synthesis x (generator a f)) := by
  classical
  have h := box_gamma1_finite a ha0
    (fun i : f.coeff.support => i.val) Subtype.val_injective
    (fun i => f.coeff i.val)
  rw [polynomial_support] at h
  rw [box_generator_energy_all]
  exact h.trans (Finset.sum_attach f.coeff.support
    (fun k => (a k : ℂ)*(conj (f.coeff k)*f.coeff k)))

theorem anisotropic_box_gamma1_energy (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j) (f : Fourier) :
    boxAverage (fun x => synthesis x
      (gammaIter (anisotropicSymbol a γ) 1 f f)) =
      -boxAverage (fun x => conj (synthesis x f)*
        synthesis x (generator (anisotropicSymbol a γ) f)) ∧
    0 ≤ (-boxAverage (fun x => conj (synthesis x f)*
        synthesis x (generator (anisotropicSymbol a γ) f))).re := by
  constructor
  · exact box_gamma1_energy _ (AnisotropicStableGamma.anisotropic_zero a γ hγ0) f
  · apply box_energy_nonnegative_all
    intro w
    exact (rate a γ ha w).property

end OperatorDerivativeRewrite.Foundation.WavePhysicalFourierBridge
