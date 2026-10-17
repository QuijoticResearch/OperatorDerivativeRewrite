import Foundation.TriadGaussianHodge
import Foundation.GaussianTwoSourceQuadraticMoments

/-! The full nonlinear triad as an actual quadratic Gaussian source field.
All products use the proved polynomial L2 domain, not unrestricted L2 multiplication. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.QuadraticTriadGaussian
open InfiniteGaussian GaussianTimePolynomialPairing GaussianTimeFieldNorm
open GaussianTwoSourceQuadraticMoments TriadGaussianHodge
open GaussianSourceHodge GaussianNumberSectors GaussianDivergenceRecovery
set_option backward.isDefEq.respectTransparency false

def product (n m : ℕ) : polynomialCylindricalDomain := rawProduct (direction n) (direction m)

theorem product_coeFn (n m : ℕ) : (product n m : GaussianL2) =ᵐ[gaussianProduct]
    fun ω => TriadGaussianHodge.coordinate n ω*TriadGaussianHodge.coordinate m ω :=
  rawProduct_coeFn _ _

theorem product_derivative_coeFn (n m : ℕ) :
    polynomialDerivative (product n m) =ᵐ[gaussianProduct] fun ω =>
      TriadGaussianHodge.coordinate n ω • direction m+
        TriadGaussianHodge.coordinate m ω • direction n := by
  filter_upwards [polynomialDerivative_product_ae (firstChaosPolynomial (direction n))
      (firstChaosPolynomial (direction m)),
    firstChaosPolynomial_coeFn (direction n),firstChaosPolynomial_coeFn (direction m),
    firstChaosPolynomial_derivative_coeFn (direction n),
    firstChaosPolynomial_derivative_coeFn (direction m)] with ω hd hn hm hdn hdm
  change polynomialDerivative
    (polynomialProduct (firstChaosPolynomial (direction n)) (firstChaosPolynomial (direction m))) ω=_
  rw [hd,hn,hm,hdn,hdm]
  rfl

theorem product_norm_sq (n m : ℕ) (hnm : n ≠ m) : ‖(product n m : GaussianL2)‖^2=1 := by
  rw [product,rawProduct_variance,direction_norm_sq,direction_norm_sq,direction_inner]
  simp [hnm]

theorem product_second_chaos (n m : ℕ) (hnm : n ≠ m) :
    (product n m : GaussianL2) ∈ sector 2 := by
  apply orthogonal_rawProduct_second_chaos
  simp [direction_inner,hnm]

def field : GaussianVectorL2 :=
  scalarTensor (direction 0) (product 1 2)-scalarTensor (direction 1) (product 0 2)

theorem field_polynomial : field ∈ cylindricalVectorDomain :=
  cylindricalVectorDomain.sub_mem (scalarTensor_mem_domain (product 1 2) (direction 0))
    (scalarTensor_mem_domain (product 0 2) (direction 1))

theorem field_coeFn : field =ᵐ[gaussianProduct] fun ω =>
    (TriadGaussianHodge.coordinate 1 ω*TriadGaussianHodge.coordinate 2 ω) • direction 0-
      (TriadGaussianHodge.coordinate 0 ω*TriadGaussianHodge.coordinate 2 ω) • direction 1 := by
  filter_upwards [Lp.coeFn_sub (scalarTensor (direction 0) (product 1 2))
      (scalarTensor (direction 1) (product 0 2)),
    scalarTensor_coeFn (direction 0) (product 1 2),
    scalarTensor_coeFn (direction 1) (product 0 2),product_coeFn 1 2,product_coeFn 0 2]
    with ω hs h0 h1 hp hq
  change (scalarTensor (direction 0) (product 1 2)-
    scalarTensor (direction 1) (product 0 2)) ω=_
  rw [hs]
  simp only [Pi.sub_apply]
  rw [h0,h1,hp,hq]

theorem component_zero : component 0 field=(product 1 2 : GaussianL2) := by
  rw [field,map_sub,component_tensor,component_tensor]
  simp [direction_inner,direction_norm_sq]

theorem component_one : component 1 field= -(product 0 2 : GaussianL2) := by
  rw [field,map_sub,component_tensor,component_tensor]
  simp [direction_inner,direction_norm_sq]

theorem component_other (n : ℕ) (hn0 : n ≠ 0) (hn1 : n ≠ 1) : component n field=0 := by
  rw [field,map_sub,component_tensor,component_tensor]
  simp [direction_inner,hn0,hn1]

theorem component_second_chaos (n : ℕ) : component n field ∈ sector 2 := by
  by_cases h0 : n=0
  · subst n
    rw [component_zero]
    exact product_second_chaos 1 2 (by norm_num)
  by_cases h1 : n=1
  · subst n
    rw [component_one]
    exact (sector 2).neg_mem (product_second_chaos 0 2 (by norm_num))
  rw [component_other n h0 h1]
  exact (sector 2).zero_mem

theorem components_equal_triad : ∀ᵐ ω ∂gaussianProduct, ∀ i : Fin 3,
    component (i : ℕ) field ω=DictionaryTriadPotential.drift 0
      ![TriadGaussianHodge.coordinate 0 ω,TriadGaussianHodge.coordinate 1 ω,
        TriadGaussianHodge.coordinate 2 ω] i := by
  have h2 : component 2 field=0 := component_other 2 (by norm_num) (by norm_num)
  filter_upwards [product_coeFn 1 2,product_coeFn 0 2,
    Lp.coeFn_neg (product 0 2 : GaussianL2),
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := gaussianProduct)] with ω hp hq hn hz
  intro i
  fin_cases i
  · rw [component_zero,hp]
    simp [DictionaryTriadPotential.drift]
  · rw [component_one,hn]
    simp only [Pi.neg_apply]
    rw [hq]
    simp [DictionaryTriadPotential.drift]
  · rw [h2,hz]
    simp [DictionaryTriadPotential.drift]

/-- The two cubic divergence expressions cancel on actual polynomial representatives. -/
theorem rank_divergences_equal :
    rankDivergence (product 1 2) (direction 0)=rankDivergence (product 0 2) (direction 1) := by
  apply Lp.ext
  filter_upwards [rankDivergence_coeFn (product 1 2) (direction 0),
    rankDivergence_coeFn (product 0 2) (direction 1),
    product_coeFn 1 2,product_coeFn 0 2,
    product_derivative_coeFn 1 2,product_derivative_coeFn 0 2]
    with ω h0 h1 hp hq hdp hdq
  rw [h0,h1,hp,hq,hdp,hdq]
  simp [inner_add_left,real_inner_smul_left,direction_inner,TriadGaussianHodge.coordinate]
  ring

theorem field_divergence_zero : (field,0) ∈ hilbertDivergence.graph := by
  have h0 := LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (cylindricalDivergence_rank_graph (product 1 2) (direction 0))
  have h1 := LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (cylindricalDivergence_rank_graph (product 0 2) (direction 1))
  have hs := hilbertDivergence.graph.sub_mem h0 h1
  simpa only [Prod.mk_sub_mk,rank_divergences_equal,sub_self,field] using hs

theorem field_norm_sq : ‖field‖^2=2 := by
  have ht (h : CoefficientSpace) (f : GaussianL2) :
      ‖scalarTensor h f‖^2=‖f‖^2*‖h‖^2 := by
    rw [← real_inner_self_eq_norm_sq,scalarTensor_pair_inner,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  rw [field,norm_sub_sq_real,ht,ht,scalarTensor_pair_inner,direction_inner]
  norm_num [product_norm_sq,direction_norm_sq]

theorem field_nonzero : field ≠ 0 := by
  intro hz
  have h := field_norm_sq
  rw [hz,norm_zero] at h
  norm_num at h

theorem field_orthogonal : field ∈ gradientRangeᗮ :=
  (gradientRange_orthogonal_iff_divergence_zero _).mpr field_divergence_zero

theorem field_gradientProjection_zero : gradientProjection field=0 := by
  change gradientRange.starProjection field=0
  apply gradientRange.eq_starProjection_of_mem_orthogonal gradientRange.zero_mem
  simpa only [sub_zero] using field_orthogonal

theorem field_recovery_adjoint_zero : recoveryOperator.adjoint field=0 :=
  recovery_adjoint_kernel_zero _ field_divergence_zero

theorem no_closed_gradient_potential :
    ¬ ∃ f : GaussianL2, (f,field) ∈ closedCylindricalDerivative.graph := by
  intro h
  have hs := Submodule.starProjection_eq_self_iff.mpr ((mem_gradientRange_iff _).mpr h)
  change gradientProjection field=field at hs
  rw [field_gradientProjection_zero] at hs
  exact field_nonzero hs.symm

theorem gradient_pairing_zero {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f,g) ∈ closedCylindricalDerivative.graph) : inner ℝ g field=0 := by
  simpa only [inner_zero_right] using graph_duality hf field_divergence_zero

/-- The actual polynomial transport pairing is skew-symmetric. -/
theorem transport_skew (f g : polynomialCylindricalDomain) :
    inner ℝ (polynomialTimesDerivative f g) field=
      -inner ℝ (polynomialTimesDerivative g f) field := by
  have h := gradient_pairing_zero (closedCylindricalDerivative_core_graph (polynomialProduct f g))
  rw [polynomialDerivative_product,inner_add_left] at h
  linarith

theorem transport_pairing_integral (f g : polynomialCylindricalDomain) :
    inner ℝ (polynomialTimesDerivative f g) field=
      ∫ ω, (f : GaussianL2) ω*inner ℝ (polynomialDerivative g ω) (field ω) ∂gaussianProduct := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [polynomialTimesDerivative_coeFn f g] with ω hω
  rw [hω,real_inner_smul_left]

theorem transport_integral_skew (f g : polynomialCylindricalDomain) :
    (∫ ω, (f : GaussianL2) ω*inner ℝ (polynomialDerivative g ω) (field ω) ∂gaussianProduct)=
      -(∫ ω, (g : GaussianL2) ω*inner ℝ (polynomialDerivative f ω) (field ω) ∂gaussianProduct) := by
  rw [← transport_pairing_integral,← transport_pairing_integral]
  exact transport_skew f g

theorem transport_energy_zero (f : polynomialCylindricalDomain) :
    (∫ ω, (f : GaussianL2) ω*inner ℝ (polynomialDerivative f ω) (field ω) ∂gaussianProduct)=0 := by
  have h := transport_integral_skew f f
  linarith

theorem weak_integral_zero {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f,g) ∈ closedCylindricalDerivative.graph) :
    (∫ ω, inner ℝ (g ω) (field ω) ∂gaussianProduct)=0 := by
  rw [← L2_inner_eq_integral]
  exact gradient_pairing_zero hf

theorem gradient_error_identity {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f,g) ∈ closedCylindricalDerivative.graph) : ‖field-g‖^2=2+‖g‖^2 := by
  have ho : inner ℝ field g=0 := by rw [real_inner_comm]; exact gradient_pairing_zero hf
  simp only [norm_sub_sq_real,ho,field_norm_sq,mul_zero,sub_zero]

theorem weighted_radial_cancellation (α β : ℝ) : ∀ᵐ ω ∂gaussianProduct,
    α*TriadGaussianHodge.coordinate 0 ω*component 0 field ω+
      α*TriadGaussianHodge.coordinate 1 ω*component 1 field ω+
      β*TriadGaussianHodge.coordinate 2 ω*component 2 field ω=0 := by
  filter_upwards [components_equal_triad] with ω h
  have h0 : component 0 field ω=
      TriadGaussianHodge.coordinate 1 ω*TriadGaussianHodge.coordinate 2 ω := by
    simpa [DictionaryTriadPotential.drift] using h (0 : Fin 3)
  have h1 : component 1 field ω=
      -TriadGaussianHodge.coordinate 0 ω*TriadGaussianHodge.coordinate 2 ω := by
    simpa [DictionaryTriadPotential.drift] using h (1 : Fin 3)
  have h2 : component 2 field ω=0 := by
    simpa [DictionaryTriadPotential.drift] using h (2 : Fin 3)
  rw [h0,h1,h2]
  ring

end OperatorDerivativeRewrite.Foundation.QuadraticTriadGaussian
