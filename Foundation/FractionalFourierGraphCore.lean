import Mathlib.Analysis.Fourier.AddCircle
open MeasureTheory Filter Set AddCircle
open scoped Topology
/-! Maximal diagonal graphs on actual normalized Haar L2 of AddCircle 1.
Finite Fourier truncations converge in both graph components. The fractional
symbol is -|n|^gamma, corresponding to angular coordinate theta=2*pi*x.
This identifies the Fourier-multiplier graph, not a semigroup time derivative,
pointwise curvature limit, or the drifted Cauchy generator domain. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FractionalFourierGraphCore
abbrev E := Lp ℂ 2 (@haarAddCircle (1:ℝ) (by infer_instance))
def basis : HilbertBasis ℤ ℂ E := fourierBasis
def graph (a : ℤ → ℂ) : Set (E × E) :=
  {p | ∀ n, basis.repr p.2 n = a n * basis.repr p.1 n}
def truncation (s : Finset ℤ) (f : E) : E :=
  ∑ n ∈ s, basis.repr f n • basis n
theorem truncation_tendsto (f : E) :
    Tendsto (fun s : Finset ℤ => truncation s f) atTop (𝓝 f) :=
  basis.hasSum_repr f
theorem truncation_coefficient (s : Finset ℤ) (f : E) (n : ℤ) :
    basis.repr (truncation s f) n = if n ∈ s then basis.repr f n else 0 := by
  classical
  rw [HilbertBasis.repr_apply_apply]
  simp [truncation, inner_sum, inner_smul_right, orthonormal_iff_ite.mp basis.orthonormal]
theorem truncation_graph (a : ℤ → ℂ) (f g : E) (h : (f,g) ∈ graph a)
    (s : Finset ℤ) : (truncation s f,truncation s g) ∈ graph a := by
  intro n
  simp only [truncation_coefficient]
  split_ifs with hn
  · exact h n
  · simp
theorem graph_closed (a : ℤ → ℂ) : IsClosed (graph a) := by
  have hc (n : ℤ) : Continuous (fun f : E => basis.repr f n) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp basis.repr.continuous
  have he : graph a = ⋂ n : ℤ, {p : E × E | basis.repr p.2 n = a n * basis.repr p.1 n} := by
    ext p
    simp [graph]
  rw [he]
  exact isClosed_iInter fun n => isClosed_eq ((hc n).comp continuous_snd)
    (continuous_const.mul ((hc n).comp continuous_fst))
def finiteCore : Submodule ℂ E := Submodule.span ℂ (range basis)
def finiteGraph (a : ℤ → ℂ) : Set (E × E) :=
  {p | p ∈ graph a ∧ p.1 ∈ finiteCore}
theorem truncation_mem_core (s : Finset ℤ) (f : E) : truncation s f ∈ finiteCore := by
  classical
  apply Submodule.sum_mem
  intro n hn
  exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self n))
theorem finite_graph_closure (a : ℤ → ℂ) : closure (finiteGraph a) = graph a := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun p hp => hp.1) (graph_closed a)
  · rintro ⟨f,g⟩ h
    apply isClosed_closure.mem_of_tendsto
      ((truncation_tendsto f).prodMk_nhds (truncation_tendsto g))
    exact Eventually.of_forall fun s => subset_closure
      ⟨truncation_graph a f g h s,truncation_mem_core s f⟩
def fractionalSymbol (γ : ℝ) (n : ℤ) : ℂ := -((|(n : ℝ)| ^ γ : ℝ) : ℂ)
theorem fractional_graph_core (γ : ℝ) :
    closure (finiteGraph (fractionalSymbol γ)) = graph (fractionalSymbol γ) :=
  finite_graph_closure _
theorem actual_fourier_graph (γ : ℝ) (f g : E) :
    (f,g) ∈ graph (fractionalSymbol γ) ↔
      ∀ n : ℤ, fourierCoeff g n = -((|(n : ℝ)| ^ γ : ℝ) : ℂ) * fourierCoeff f n := by
  simp only [graph, mem_ofPred_eq, basis, fourierBasis_repr, fractionalSymbol]

theorem graph_unique (a : ℤ → ℂ) (f g h : E)
    (hg : (f,g) ∈ graph a) (hh : (f,h) ∈ graph a) : g = h := by
  apply basis.repr.injective
  ext n
  exact (hg n).trans (hh n).symm
theorem graph_domain_iff (a : ℤ → ℂ) (f : E) :
    (∃ g : E, (f,g) ∈ graph a) ↔ Memℓp (fun n => a n * basis.repr f n) 2 := by
  constructor
  · rintro ⟨g,hg⟩
    have he : (fun n => a n * basis.repr f n) = (basis.repr g : ℤ → ℂ) :=
      funext fun n => (hg n).symm
    rw [he]
    exact (basis.repr g).property
  · intro h
    let u : lp (fun _ : ℤ => ℂ) 2 := ⟨_,h⟩
    refine ⟨basis.repr.symm u, ?_⟩
    intro n
    simp only [LinearIsometryEquiv.apply_symm_apply]
    rfl
theorem mode_graph (a : ℤ → ℂ) (n : ℤ) : (basis n,a n • basis n) ∈ graph a := by
  classical
  intro m
  simp only [map_smul, HilbertBasis.repr_self, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, smul_eq_mul]
  split_ifs with h
  · subst m
    simp
  · simp

end OperatorDerivativeRewrite.Foundation.FractionalFourierGraphCore
