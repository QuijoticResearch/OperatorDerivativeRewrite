import Foundation.FiniteGaussianIBP
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Funext

/-! Actual Euclidean-valued polynomial L² fields and their dense core. -/
noncomputable section
open MeasureTheory Polynomial Module
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

abbrev ScalarGaussianL2 (ι : Type*) [Fintype ι] := Lp ℝ 2 (productGaussian ι)
abbrev VectorGaussianL2 (ι : Type*) [Fintype ι] :=
  Lp (EuclideanSpace ℝ ι) 2 (productGaussian ι)

/-- Independent Gaussian measure has full support, including in dimension zero. -/
instance productGaussian_openPos : (productGaussian ι).IsOpenPosMeasure := by
  have : GaussianCore.γ.IsOpenPosMeasure :=
    (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0
      (by norm_num : (1 : NNReal) ≠ 0)).isOpenPosMeasure
  infer_instance

/-- Actual polynomial evaluation into L² is injective.
Equality is not a representation assumption. -/
theorem productPolynomialEmbedding_injective :
    Function.Injective (productPolynomialEmbedding (ι := ι)) := by
  intro p q h
  change productPolynomialL2 p = productPolynomialL2 q at h
  have ha : (fun x => MvPolynomial.eval x p) =ᵐ[productGaussian ι]
      fun x => MvPolynomial.eval x q :=
    (productPolynomialL2_coeFn p).symm.trans (h ▸ productPolynomialL2_coeFn q)
  have he := Measure.eq_of_ae_eq ha
    (MvPolynomial.continuous_eval (p := p)) (MvPolynomial.continuous_eval (p := q))
  exact MvPolynomial.funext (congrFun he)

/-- A polynomial vector field has actual Euclidean values, with the ℓ² fiber norm. -/
def vectorPolynomialFunction (u : ι → MvPolynomial ι ℝ) (x : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => MvPolynomial.eval x (u i))

/-- Every polynomial vector field has every finite moment. -/
theorem vectorPolynomial_memLp (u : ι → MvPolynomial ι ℝ)
    (r : ℝ≥0∞) (hr : r ≠ ∞) : MemLp (vectorPolynomialFunction u) r (productGaussian ι) := by
  apply memLp_piLp_iff.mpr
  intro i
  exact productPolynomial_memLp (u i) r hr

/-- Actual vector-valued L² evaluation, with integrability proved. -/
def vectorPolynomialL2 (u : ι → MvPolynomial ι ℝ) : VectorGaussianL2 ι :=
  (vectorPolynomial_memLp u 2 (by simp)).toLp (vectorPolynomialFunction u)

theorem vectorPolynomialL2_coeFn (u : ι → MvPolynomial ι ℝ) :
    vectorPolynomialL2 u =ᵐ[productGaussian ι] vectorPolynomialFunction u := MemLp.coeFn_toLp _

/-- Linear embedding of actual polynomial vector fields. -/
def vectorPolynomialEmbedding : (ι → MvPolynomial ι ℝ) →ₗ[ℝ] VectorGaussianL2 ι where
  toFun := vectorPolynomialL2
  map_add' u v := by
    apply Lp.ext
    filter_upwards [vectorPolynomialL2_coeFn (u + v), vectorPolynomialL2_coeFn u,
      vectorPolynomialL2_coeFn v, Lp.coeFn_add (vectorPolynomialL2 u) (vectorPolynomialL2 v)]
      with x h1 h2 h3 h4
    rw [h1, h4]
    simp only [Pi.add_apply, h2, h3]
    ext i; simp [vectorPolynomialFunction]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [vectorPolynomialL2_coeFn (c • u), vectorPolynomialL2_coeFn u,
      Lp.coeFn_smul c (vectorPolynomialL2 u)] with x h1 h2 h3
    change vectorPolynomialL2 (c • u) x = (c • vectorPolynomialL2 u) x
    rw [h1, h3]
    simp only [Pi.smul_apply, h2]
    ext i; simp [vectorPolynomialFunction, MvPolynomial.smul_eval]

/-- Coordinate projection of an actual vector L² class. -/
def vectorL2Component (i : ι) (f : VectorGaussianL2 ι) : ScalarGaussianL2 ι :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).compLp f

theorem vectorL2Component_coeFn (i : ι) (f : VectorGaussianL2 ι) :
    vectorL2Component i f =ᵐ[productGaussian ι] fun x => f x i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLp f

theorem vectorPolynomialL2_component (u : ι → MvPolynomial ι ℝ) (i : ι) :
    vectorL2Component i (vectorPolynomialL2 u) = productPolynomialL2 (u i) := by
  apply Lp.ext
  filter_upwards [vectorL2Component_coeFn i (vectorPolynomialL2 u),
    vectorPolynomialL2_coeFn u, productPolynomialL2_coeFn (u i)] with x hc hu hp
  rw [hc, hu, hp]; rfl

theorem vectorPolynomialEmbedding_injective :
    Function.Injective (vectorPolynomialEmbedding (ι := ι)) := by
  intro u v h
  funext i
  apply productPolynomialEmbedding_injective
  exact (vectorPolynomialL2_component u i).symm.trans
    ((congrArg (vectorL2Component i) h).trans (vectorPolynomialL2_component v i))

/-- The Hilbert pairing splits into the scalar coordinate pairings, with integrability verified. -/
theorem vectorPolynomialL2_inner (f : VectorGaussianL2 ι) (u : ι → MvPolynomial ι ℝ) :
    inner ℝ f (vectorPolynomialL2 u) =
      ∑ i, inner ℝ (vectorL2Component i f) (productPolynomialL2 (u i)) := by
  have hi (i : ι) : Integrable (fun x => f x i * MvPolynomial.eval x (u i))
      (productGaussian ι) :=
    mul_L2_integrable ((Lp.memLp f).eval_piLp i)
      (productPolynomial_memLp (u i) 2 (by simp))
  rw [L2_inner_eq_integral]
  have he : (fun x => inner ℝ (f x) (vectorPolynomialL2 u x)) =ᵐ[productGaussian ι]
      fun x => ∑ i, f x i * MvPolynomial.eval x (u i) := by
    filter_upwards [vectorPolynomialL2_coeFn u] with x hu
    rw [hu, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _; rw [Real.inner_apply]; rfl
  rw [integral_congr_ae he, integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [vectorL2Component_coeFn i f, productPolynomialL2_coeFn (u i)] with x hc hp
  rw [hc, hp, Real.inner_apply]

/-- Orthogonality to polynomial vector fields forces every component,
hence the vector, to vanish. -/
theorem eq_zero_of_vectorPolynomial_orthogonal (f : VectorGaussianL2 ι)
    (hf : ∀ u : ι → MvPolynomial ι ℝ, inner ℝ f (vectorPolynomialL2 u) = 0) : f = 0 := by
  classical
  have hc (i : ι) : vectorL2Component i f = 0 := by
    apply eq_zero_of_productPolynomial_orthogonal
    intro p
    have hzero : productPolynomialL2 (0 : MvPolynomial ι ℝ) = 0 :=
      productPolynomialEmbedding.map_zero
    have hh := hf (Pi.single i p)
    rw [vectorPolynomialL2_inner] at hh
    simpa [Pi.single_apply, apply_ite, hzero] using hh
  apply Lp.ext
  have ha : ∀ᵐ x ∂productGaussian ι, ∀ i,
      vectorL2Component i f x = f x i := ae_all_iff.mpr (fun i => vectorL2Component_coeFn i f)
  have hz : ∀ᵐ x ∂productGaussian ι, ∀ i : ι,
      (0 : ScalarGaussianL2 ι) x = 0 := by
    exact ae_all_iff.mpr (fun _ => Lp.coeFn_zero (E := ℝ) (p := 2) (μ := productGaussian ι))
  filter_upwards [ha, hz, Lp.coeFn_zero (E := EuclideanSpace ℝ ι)
    (p := 2) (μ := productGaussian ι)] with x hx hz hv
  rw [hv]
  ext i
  rw [← hx i, hc i, hz i]; rfl

/-- Polynomial vector fields are dense in the full Euclidean-valued Gaussian L² space. -/
theorem vectorPolynomialEmbedding_dense :
    Dense ((vectorPolynomialEmbedding (ι := ι)).range : Set (VectorGaussianL2 ι)) := by
  have hb : (vectorPolynomialEmbedding (ι := ι)).range.topologicalClosureᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    apply eq_zero_of_vectorPolynomial_orthogonal
    intro u
    exact (vectorPolynomialEmbedding (ι := ι)).range.topologicalClosure
      |>.inner_left_of_mem_orthogonal
        ((vectorPolynomialEmbedding (ι := ι)).range.le_topologicalClosure ⟨u, rfl⟩) hf
  have ht := Submodule.orthogonal_eq_bot_iff.mp hb
  rw [dense_iff_closure_eq]
  change ((vectorPolynomialEmbedding (ι := ι)).range.topologicalClosure :
    Set (VectorGaussianL2 ι)) = Set.univ
  rw [ht]; rfl

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
