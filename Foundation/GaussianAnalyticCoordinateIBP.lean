import Foundation.IBMReflectedGaussianSobolev
import Foundation.FiniteGaussianAdjoints
import Mathlib.MeasureTheory.Integral.Pi

/-! Analytic coordinate integration by parts for nonlinear Gaussian cylinders.
This is the finite-dimensional weak-gradient bridge needed for IBM F3 closure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianAnalyticCoordinateIBP
open FiniteGaussian
set_option backward.isDefEq.respectTransparency false

theorem coordinate_insert_hasDerivAt {n : ℕ} (i j : Fin (n + 1))
    (r : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (fun a : ℝ => (i.insertNth a r : Fin (n + 1) → ℝ) j)
      (if i = j then 1 else 0) x := by
  by_cases hj : j = i
  · subst j
    simp only [Fin.insertNth_apply_same, ↓reduceIte]
    exact hasDerivAt_id' x
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
    subst j
    simpa [Ne.symm (Fin.succAbove_ne i k)] using hasDerivAt_const x (r k)

theorem polynomial_insert_hasDerivAt {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) (r : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (fun a => MvPolynomial.eval (i.insertNth a r) p)
      (MvPolynomial.eval (i.insertNth x r) (MvPolynomial.pderiv i p)) x := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const x a
  | add p q hp hq =>
    simp only [map_add]
    convert hp.add hq using 1
  | mul_X p j hp =>
    convert hp.mul (coordinate_insert_hasDerivAt i j r x) using 1
    · funext a
      simp
    · simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_add, map_mul,
        MvPolynomial.eval_X, Pi.single_apply]
      by_cases hj : i = j
      · subst j
        simp only [ite_eq_left, Fin.insertNth_apply_same, map_one, mul_one]
      · simp only [ite_eq_right hj, ite_eq_right (Ne.symm hj), map_zero, mul_zero, add_zero]

/-- Gaussian Stein from actual coordinate derivatives and genuine global
integrability, proved by a measure-preserving coordinate split and 1D IBP. -/
theorem coordinate_stein_integrable {n : ℕ} (i : Fin (n + 1)) (f h : (Fin (n + 1) → ℝ) → ℝ)
    (hd : ∀ r x, HasDerivAt (fun a => f (i.insertNth a r)) (h (i.insertNth x r)) x)
    (hf : Integrable f (productGaussian (Fin (n + 1))))
    (hh : Integrable h (productGaussian (Fin (n + 1))))
    (hxf : Integrable (fun z => f z * z i) (productGaussian (Fin (n + 1)))) :
    (∫ z, h z ∂productGaussian (Fin (n + 1))) =
      ∫ z, f z * z i ∂productGaussian (Fin (n + 1)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e (productGaussian (Fin (n + 1)))
      (GaussianCore.γ.prod (productGaussian (Fin n))) :=
    measurePreserving_piFinSuccAbove (fun _ => GaussianCore.γ) i
  have hf' : Integrable (fun z => f (e.symm z)) (GaussianCore.γ.prod (productGaussian (Fin n))) :=
    (he.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
  have hh' : Integrable (fun z => h (e.symm z)) (GaussianCore.γ.prod (productGaussian (Fin n))) :=
    (he.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hh
  have hx' : Integrable (fun z => f (e.symm z) * z.1)
      (GaussianCore.γ.prod (productGaussian (Fin n))) := by
    have ht := (he.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hxf
    simpa [Function.comp_def, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using ht
  rw [← he.symm.integral_comp' h, ← he.symm.integral_comp' (fun z => f z * z i)]
  change (∫ z, h (e.symm z) ∂GaussianCore.γ.prod (productGaussian (Fin n))) = _
  have heq : (fun z : ℝ × (Fin n → ℝ) => f (e.symm z) * (e.symm z) i) =
      fun z => f (e.symm z) * z.1 := by
    funext z
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rw [heq, integral_prod_symm _ hh', integral_prod_symm _ hx']
  apply integral_congr_ae
  filter_upwards [hf'.prod_left_ae, hh'.prod_left_ae, hx'.prod_left_ae] with r hfr hhr hxr
  apply IBMReflectedGaussianSobolev.stein_of_integrable _ hfr hhr hxr
  intro x
  exact hd r x

theorem coordinate_test_ibp {n : ℕ} (i : Fin (n + 1))
    (f h : (Fin (n + 1) → ℝ) → ℝ)
    (hd : ∀ r x, HasDerivAt (fun a => f (i.insertNth a r)) (h (i.insertNth x r)) x)
    (hf : MemLp f 2 (productGaussian (Fin (n + 1))))
    (hh : MemLp h 2 (productGaussian (Fin (n + 1))))
    (q : MvPolynomial (Fin (n + 1)) ℝ) :
    (∫ z, h z * MvPolynomial.eval z q ∂productGaussian (Fin (n + 1))) =
      ∫ z, f z * MvPolynomial.eval z (coordinateDivergencePolynomial i q)
        ∂productGaussian (Fin (n + 1)) := by
  have hq (p : MvPolynomial (Fin (n + 1)) ℝ) := productPolynomial_memLp p 2 (by norm_num)
  have hi (p : MvPolynomial (Fin (n + 1)) ℝ) :
      Integrable (fun z => f z * MvPolynomial.eval z p) (productGaussian (Fin (n + 1))) :=
    hf.integrable_mul (hq p)
  have hj : Integrable (fun z => h z * MvPolynomial.eval z q) (productGaussian (Fin (n + 1))) :=
    hh.integrable_mul (hq q)
  have hx : Integrable (fun z => (f z * MvPolynomial.eval z q) * z i)
      (productGaussian (Fin (n + 1))) := by
    convert hi (q * MvPolynomial.X i) using 1
    funext z
    simp [mul_assoc]
  have he := coordinate_stein_integrable i
    (fun z => f z * MvPolynomial.eval z q)
    (fun z => h z * MvPolynomial.eval z q + f z * MvPolynomial.eval z (MvPolynomial.pderiv i q))
    (fun r x => (hd r x).mul (polynomial_insert_hasDerivAt q i r x))
    (hi q) (hj.add (hi (MvPolynomial.pderiv i q))) hx
  rw [integral_add hj (hi (MvPolynomial.pderiv i q))] at he
  have hxi : Integrable (fun z => f z * (z i * MvPolynomial.eval z q))
      (productGaussian (Fin (n + 1))) := by
    convert hi (MvPolynomial.X i * q) using 1
    simp
  simp only [coordinateDivergencePolynomial, map_sub, map_mul, MvPolynomial.eval_X, mul_sub]
  rw [integral_sub hxi (hi (MvPolynomial.pderiv i q))]
  have heq : (∫ z, f z * (z i * MvPolynomial.eval z q) ∂productGaussian (Fin (n + 1))) =
      ∫ z, (f z * MvPolynomial.eval z q) * z i ∂productGaussian (Fin (n + 1)) := by
    congr 1
    funext z
    ring
  rw [heq]
  linarith

theorem scalar_polynomial_inner {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : MemLp f 2 (productGaussian (Fin (n + 1))))
    (q : MvPolynomial (Fin (n + 1)) ℝ) :
    inner ℝ (hf.toLp f) (productPolynomialL2 q) =
      ∫ z, f z * MvPolynomial.eval z q ∂productGaussian (Fin (n + 1)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, productPolynomialL2_coeFn q] with z hf hq
  rw [hf, hq, Real.inner_apply]

/-- Actual classical coordinate derivatives in Gaussian L2 belong to the
existing finite closed gradient. The weak graph is proved, not stipulated. -/
theorem classical_closed_gradient {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (g : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)))
    (hd : ∀ i r x, HasDerivAt (fun a => f (i.insertNth a r)) (g (i.insertNth x r) i) x)
    (hf : MemLp f 2 (productGaussian (Fin (n + 1))))
    (hg : MemLp g 2 (productGaussian (Fin (n + 1)))) :
    (hf.toLp f, hg.toLp g) ∈ (closedGradient (ι := Fin (n + 1))).graph := by
  rw [closedGradient_eq_divergence_adjoint,
    LinearPMap.adjoint_graph_eq_graph_adjoint polynomialDivergence_dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro a b hab
  rw [polynomialDivergence_graph] at hab
  obtain ⟨q, hq⟩ := hab
  have ha := congrArg Prod.fst hq
  have hb := congrArg Prod.snd hq
  change vectorPolynomialL2 q = a at ha
  change productPolynomialL2 (divergencePolynomial q) = b at hb
  subst a
  subst b
  simp only [sub_eq_zero]
  conv_lhs => rw [real_inner_comm]
  conv_rhs => rw [real_inner_comm]
  rw [scalar_polynomial_inner, vectorPolynomialL2_inner]
  have hi (i : Fin (n + 1)) : Integrable
      (fun z => f z * MvPolynomial.eval z (coordinateDivergencePolynomial i (q i)))
      (productGaussian (Fin (n + 1))) :=
    hf.integrable_mul (productPolynomial_memLp _ 2 (by norm_num))
  simp only [divergencePolynomial, LinearMap.coe_mk, AddHom.coe_mk, map_sum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hi
  have hgi : MemLp (fun z => g z i) 2 (productGaussian (Fin (n + 1))) := hg.eval_piLp i
  have hc : vectorL2Component i (hg.toLp g) = hgi.toLp (fun z => g z i) := by
    apply Lp.ext
    filter_upwards [vectorL2Component_coeFn i (hg.toLp g), hg.coeFn_toLp,
      hgi.coeFn_toLp] with z hc hg hgi
    rw [hc, hg, hgi]
  rw [hc, scalar_polynomial_inner]
  exact (coordinate_test_ibp i f (fun z => g z i) (hd i) hf hgi (q i)).symm

/-- Bounded nonlinear functions of polynomial Gaussian cylinders have their
actual analytic chain derivative in the pre-existing closed gradient graph. -/
theorem bounded_polynomial_chain_graph {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ (hf : MemLp (fun z => φ (MvPolynomial.eval z p)) 2 (productGaussian (Fin (n + 1))))
      (hg : MemLp (fun z => dφ (MvPolynomial.eval z p) •
        vectorPolynomialFunction (gradientPolynomial p) z) 2 (productGaussian (Fin (n + 1)))),
      (hf.toLp _, hg.toLp _) ∈ (closedGradient (ι := Fin (n + 1))).graph := by
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hm : Measurable (fun z : Fin (n + 1) → ℝ => MvPolynomial.eval z p) :=
    (MvPolynomial.continuous_eval (p := p)).measurable
  have hf : MemLp (fun z => φ (MvPolynomial.eval z p)) 2 (productGaussian (Fin (n + 1))) :=
    MemLp.of_bound (hφ.measurable.comp hm).aestronglyMeasurable A (ae_of_all _ fun z => hA _)
  have hdm : MemLp (fun z => dφ (MvPolynomial.eval z p)) ∞ (productGaussian (Fin (n + 1))) :=
    MemLp.of_bound (hc.measurable.comp hm).aestronglyMeasurable B (ae_of_all _ fun z => hB _)
  have hg : MemLp (fun z => dφ (MvPolynomial.eval z p) •
      vectorPolynomialFunction (gradientPolynomial p) z) 2 (productGaussian (Fin (n + 1))) :=
    smul_memLp (p := ∞) (q := 2) (r := 2) hdm (vectorPolynomial_memLp _ 2 (by norm_num))
  refine ⟨hf, hg, classical_closed_gradient _ _ ?_ hf hg⟩
  intro i r x
  change HasDerivAt (fun a => φ (MvPolynomial.eval (i.insertNth a r) p))
    (dφ (MvPolynomial.eval (i.insertNth x r) p) *
      MvPolynomial.eval (i.insertNth x r) (MvPolynomial.pderiv i p)) x
  exact (hd _).comp x (polynomial_insert_hasDerivAt p i r x)

end OperatorDerivativeRewrite.Foundation.GaussianAnalyticCoordinateIBP
