import Foundation.FractionalGaussianProcess
import Foundation.GaussianGeneratedGraphCore
import Foundation.AdjointBidual

/-! The full closed source-gradient restriction on the fractional observable
L² space, and its genuine adjoint. Vector fields here retain the ambient source
coefficient space: this is not yet an intrinsic Cameron--Martin-field transport. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalGaussianOperators
open InfiniteGaussian FractionalGaussianProcess GaussianConditionalGraph GaussianGeneratedGraphCore
open FractionalSpectralKernel
attribute [local instance] spectralSpace_secondCountable
variable (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)

abbrev scalarSpace := generated (direction H hH0 hH1)

def derivative : scalarSpace H hH0 hH1 →ₗ.[ℝ] GaussianVectorL2 where
  domain := closedCylindricalDerivative.domain.comap (scalarSpace H hH0 hH1).subtype
  toFun :=
    { toFun := fun f => closedCylindricalDerivative ⟨f.val.val, f.property⟩
      map_add' := fun f g => by
        calc
          _ = closedCylindricalDerivative (⟨f.val.val,f.property⟩ + ⟨g.val.val,g.property⟩) :=
            congrArg closedCylindricalDerivative (Subtype.ext rfl)
          _ = _ := closedCylindricalDerivative.map_add _ _
      map_smul' := fun a f => by
        calc
          _ = closedCylindricalDerivative (a • ⟨f.val.val,f.property⟩) :=
            congrArg closedCylindricalDerivative (Subtype.ext rfl)
          _ = _ := closedCylindricalDerivative.map_smul a _ }
theorem derivative_domain (f : scalarSpace H hH0 hH1) :
    f ∈ (derivative H hH0 hH1).domain ↔ (f : GaussianL2) ∈ closedCylindricalDerivative.domain := Iff.rfl

theorem derivative_graph (f : scalarSpace H hH0 hH1) (g : GaussianVectorL2) :
    (f,g) ∈ (derivative H hH0 hH1).graph ↔ ((f:GaussianL2),g) ∈ closedCylindricalDerivative.graph := by
  constructor
  · intro hz
    obtain ⟨a, ha, hg⟩ := (derivative H hH0 hH1).mem_graph_iff.mp hz
    exact closedCylindricalDerivative.mem_graph_iff.mpr
      ⟨⟨a.val.val,a.property⟩, congrArg Subtype.val ha, hg⟩
  · intro hz
    obtain ⟨a, ha, hg⟩ := closedCylindricalDerivative.mem_graph_iff.mp hz
    change (a:GaussianL2) = (f:GaussianL2) at ha
    have hf : (f:GaussianL2) ∈ closedCylindricalDerivative.domain := by rw [← ha]; exact a.property
    refine (derivative H hH0 hH1).mem_graph_iff.mpr ⟨⟨f,hf⟩, rfl, ?_⟩
    change closedCylindricalDerivative ⟨f.val,hf⟩ = g
    simpa only [show (⟨f.val,hf⟩ : closedCylindricalDerivative.domain) = a from Subtype.ext ha.symm] using hg

theorem derivative_isClosed : (derivative H hH0 hH1).IsClosed := by
  have he : ((derivative H hH0 hH1).graph : Set (scalarSpace H hH0 hH1 × GaussianVectorL2)) =
      (fun z : scalarSpace H hH0 hH1 × GaussianVectorL2 => ((z.1:GaussianL2),z.2)) ⁻¹'
        (closedCylindricalDerivative.graph : Set (GaussianL2 × GaussianVectorL2)) := by
    ext z
    exact derivative_graph H hH0 hH1 z.1 z.2
  change IsClosed ((derivative H hH0 hH1).graph : Set (scalarSpace H hH0 hH1 × GaussianVectorL2))
  rw [he]
  exact closedCylindricalDerivative_isClosed.preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

def polynomial (p : MvPolynomial ℝ≥0 ℝ) : scalarSpace H hH0 hH1 :=
  ⟨familyPolynomialEmbedding (direction H hH0 hH1) p, familyPolynomial_aestronglyMeasurable _ _⟩

theorem polynomial_graph (p : MvPolynomial ℝ≥0 ℝ) :
    (polynomial H hH0 hH1 p, polynomialDerivative (familyCore (direction H hH0 hH1) p)) ∈
      (derivative H hH0 hH1).graph := by
  rw [derivative_graph]
  exact closedCylindricalDerivative_core_graph (familyCore (direction H hH0 hH1) p)

theorem derivative_dense_domain : Dense ((derivative H hH0 hH1).domain : Set (scalarSpace H hH0 hH1)) := by
  apply Metric.dense_iff.mpr
  intro f ε hε
  have hf : (f:GaussianL2) ∈ (familyPolynomialEmbedding (direction H hH0 hH1)).range.topologicalClosure := by
    rw [familyPolynomial_closure]
    exact f.property
  obtain ⟨g, ⟨p,rfl⟩, hp⟩ := Metric.mem_closure_iff.mp hf ε hε
  refine ⟨polynomial H hH0 hH1 p, ?_, ?_⟩
  · change dist (familyPolynomialEmbedding _ p) (f:GaussianL2) < ε
    rwa [dist_comm]
  · exact ((derivative H hH0 hH1).mem_domain_iff).mpr ⟨_, polynomial_graph H hH0 hH1 p⟩

theorem polynomial_graph_core {f : scalarSpace H hH0 hH1} {g : GaussianVectorL2}
    (hg : (f,g) ∈ (derivative H hH0 hH1).graph) :
    ∃ p : ℕ → MvPolynomial ℝ≥0 ℝ,
      Tendsto (fun n => ((polynomial H hH0 hH1 (p n):GaussianL2),
        polynomialDerivative (familyCore (direction H hH0 hH1) (p n)))) atTop (𝓝 ((f:GaussianL2),g)) :=
  exists_polynomial_graph_sequence (direction H hH0 hH1) f.property
    ((derivative_graph H hH0 hH1 f g).mp hg)

def divergence : GaussianVectorL2 →ₗ.[ℝ] scalarSpace H hH0 hH1 := (derivative H hH0 hH1).adjoint

theorem divergence_domain (u : GaussianVectorL2) :
    u ∈ (divergence H hH0 hH1).domain ↔ ∃ v : scalarSpace H hH0 hH1,
      ∀ f : (derivative H hH0 hH1).domain,
        inner ℝ v (f:scalarSpace H hH0 hH1) = inner ℝ u (derivative H hH0 hH1 f) :=
  mem_adjoint_domain_iff_representable _ (derivative_dense_domain H hH0 hH1) u

def projectedSourceDivergence (u : hilbertDivergence.domain) : scalarSpace H hH0 hH1 :=
  ⟨conditionalProjection (direction H hH0 hH1) (hilbertDivergence u),
    (scalarSpace H hH0 hH1).starProjection_apply_mem _⟩

theorem source_divergence_pairing (u : hilbertDivergence.domain)
    (f : (derivative H hH0 hH1).domain) :
    inner ℝ (projectedSourceDivergence H hH0 hH1 u) (f:scalarSpace H hH0 hH1) =
      inner ℝ (u:GaussianVectorL2) (derivative H hH0 hH1 f) := by
  have hp := (scalarSpace H hH0 hH1).starProjection_inner_eq_zero (hilbertDivergence u)
    f.val.val f.val.property
  rw [inner_sub_left] at hp
  have hi := closedCylindricalDerivative.adjoint_isFormalAdjoint
    closedCylindricalDerivative_dense_domain u ⟨f.val.val,f.property⟩
  change inner ℝ _ _ = inner ℝ _ _
  change inner ℝ (hilbertDivergence u) f.val.val =
    inner ℝ (u:GaussianVectorL2) (closedCylindricalDerivative ⟨f.val.val,f.property⟩) at hi
  change inner ℝ ((scalarSpace H hH0 hH1).starProjection (hilbertDivergence u)) f.val.val =
    inner ℝ (u:GaussianVectorL2) (closedCylindricalDerivative ⟨f.val.val,f.property⟩)
  linarith

theorem source_divergence_mem (u : hilbertDivergence.domain) :
    (u:GaussianVectorL2) ∈ (divergence H hH0 hH1).domain :=
  (divergence_domain H hH0 hH1 u).mpr
    ⟨projectedSourceDivergence H hH0 hH1 u, source_divergence_pairing H hH0 hH1 u⟩

theorem divergence_source_value (u : hilbertDivergence.domain) :
    divergence H hH0 hH1 ⟨u,source_divergence_mem H hH0 hH1 u⟩ =
      projectedSourceDivergence H hH0 hH1 u :=
  (derivative H hH0 hH1).adjoint_apply_eq (derivative_dense_domain H hH0 hH1)
    ⟨u,source_divergence_mem H hH0 hH1 u⟩
    (source_divergence_pairing H hH0 hH1 u)

theorem divergence_dense_domain : Dense ((divergence H hH0 hH1).domain : Set GaussianVectorL2) :=
  hilbertDivergence_dense_domain.mono (fun u hu => source_divergence_mem H hH0 hH1 ⟨u,hu⟩)

theorem divergence_isClosed : (divergence H hH0 hH1).IsClosed :=
  (derivative H hH0 hH1).adjoint_isClosed (derivative_dense_domain H hH0 hH1)

/-- An equality of actual partial operators, with all domains included. -/
theorem divergence_adjoint_eq_derivative : (divergence H hH0 hH1).adjoint = derivative H hH0 hH1 :=
  closedOperator_adjoint_adjoint_eq (derivative_isClosed H hH0 hH1)
    (derivative_dense_domain H hH0 hH1) (divergence_dense_domain H hH0 hH1)

end OperatorDerivativeRewrite.Foundation.FractionalGaussianOperators
