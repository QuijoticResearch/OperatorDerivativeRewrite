import Foundation.InfiniteGaussianFiniteSectors

/-! Finite-coordinate polynomial vector fields inside the genuine divergence domain.
The density here is in the ambient vector L² norm, not the divergence graph norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian

set_option backward.isDefEq.respectTransparency false

/-- Linear span of polynomial fields with finitely many sample coordinates and one
coordinate direction in `ℓ²`. -/
def coordinatePolynomialVectorDomain : Submodule ℝ GaussianVectorL2 :=
  Submodule.span ℝ {u | ∃ (s : Finset ℕ) (p : MvPolynomial s ℝ) (n : ℕ),
    scalarTensor (lp.single 2 n (1 : ℝ)) (polynomialCylinderEmbedding s p) = u}

/-- Each generator is an actual polynomial divergence test field. -/
theorem coordinatePolynomialVectorDomain_le :
    coordinatePolynomialVectorDomain ≤ cylindricalDivergence.domain := by
  rw [cylindricalDivergence_domain]
  apply Submodule.span_le.mpr
  rintro u ⟨s, p, n, rfl⟩
  exact scalarTensor_mem_domain (coordinatePolynomialDomain s p)
    (lp.single 2 n (1 : ℝ))

/-- Orthogonality to finite-coordinate polynomial fields forces every `ℓ²` component
of a vector-valued random variable to vanish. -/
theorem eq_zero_of_coordinatePolynomialVector_orthogonal (u : GaussianVectorL2)
    (hu : ∀ (s : Finset ℕ) (p : MvPolynomial s ℝ) (n : ℕ),
      inner ℝ (scalarTensor (lp.single 2 n (1 : ℝ))
        (polynomialCylinderEmbedding s p)) u = 0) : u = 0 := by
  have hc (n : ℕ) :
      (innerSL ℝ (lp.single 2 n (1 : ℝ))).compLpL 2 gaussianProduct u = 0 := by
    let v := (innerSL ℝ (lp.single 2 n (1 : ℝ))).compLpL 2 gaussianProduct u
    have he : (fun f : GaussianL2 => inner ℝ f v) = fun _ => (0 : ℝ) := by
      apply Continuous.ext_on coordinatePolynomialEmbedding_dense
        (continuous_id.inner continuous_const) continuous_const
      rintro f ⟨p, rfl⟩
      obtain ⟨s, q, rfl⟩ := MvPolynomial.exists_finset_rename p
      change inner ℝ (coordinatePolynomialL2 (MvPolynomial.rename Subtype.val q)) v = 0
      rw [coordinatePolynomialL2_rename]
      exact (scalarTensor_inner (lp.single 2 n (1 : ℝ))
        (polynomialCylinderEmbedding s q) u).symm.trans (hu s q n)
    exact inner_self_eq_zero.mp (congrFun he v)
  have ha (n : ℕ) :
      (fun ω => inner ℝ (lp.single 2 n (1 : ℝ)) (u ω)) =ᵐ[gaussianProduct]
        fun _ => (0 : ℝ) := by
    have he := (innerSL ℝ (lp.single 2 n (1 : ℝ))).coeFn_compLpL u
    rw [hc] at he
    exact he.symm.trans (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := gaussianProduct))
  apply Lp.ext
  filter_upwards [ae_all_iff.2 ha,
    Lp.coeFn_zero (E := CoefficientSpace) (p := 2) (μ := gaussianProduct)] with ω hω hz
  rw [hz]
  apply Subtype.ext
  funext n
  have hn := hω n
  simpa [lp.inner_single_left, Real.inner_apply] using hn

/-- Finite-coordinate polynomial fields are dense in vector Gaussian `L²`.
This does not assert density in the graph norm of the divergence. -/
theorem coordinatePolynomialVectorDomain_dense :
    Dense (coordinatePolynomialVectorDomain : Set GaussianVectorL2) := by
  have hb : coordinatePolynomialVectorDomain.topologicalClosureᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    apply eq_zero_of_coordinatePolynomialVector_orthogonal u
    intro s p n
    exact coordinatePolynomialVectorDomain.topologicalClosure.inner_right_of_mem_orthogonal
      (coordinatePolynomialVectorDomain.le_topologicalClosure
        (Submodule.subset_span ⟨s, p, n, rfl⟩)) hu
  have ht := Submodule.orthogonal_eq_bot_iff.mp hb
  rw [dense_iff_closure_eq]
  change (coordinatePolynomialVectorDomain.topologicalClosure : Set GaussianVectorL2) = Set.univ
  rw [ht]
  rfl

/-- Every square-integrable `ℓ²` field has arbitrarily close finite sums of
finite-coordinate polynomial rank-one fields in the ambient `L²` norm. -/
theorem exists_coordinatePolynomialVector_approx (u : GaussianVectorL2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v : coordinatePolynomialVectorDomain, ‖u - (v : GaussianVectorL2)‖ < ε := by
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp
    (coordinatePolynomialVectorDomain_dense u) ε hε
  exact ⟨⟨v, hv⟩, by simpa [dist_eq_norm] using hdist⟩

/-- The finite vector lift sends a single finite coordinate component to the
corresponding genuine `ℓ²` rank-one field. -/
theorem finiteVectorPullback_insert (s : Finset ℕ) (i : s)
    (f : FiniteGaussian.ScalarGaussianL2 s) :
    finiteVectorPullback s (FiniteGaussian.vectorL2Insert i f) =
      scalarTensor (lp.single 2 i.val (1 : ℝ)) (finitePullback s f) := by
  classical
  rw [finiteVectorPullback_apply]
  simp only [FiniteGaussian.vectorL2Component_insert, apply_ite, map_zero]
  simp

/-- Every finite-coordinate polynomial rank-one field lies in an actual finite
Gaussian vector sector, after adding its output coordinate to the sample coordinates. -/
theorem coordinatePolynomialVector_mem_finite_sector (s : Finset ℕ)
    (p : MvPolynomial s ℝ) (n : ℕ) :
    ∃ (t : Finset ℕ) (v : FiniteGaussian.VectorGaussianL2 t),
      finiteVectorPullback t v =
        scalarTensor (lp.single 2 n (1 : ℝ)) (polynomialCylinderEmbedding s p) := by
  classical
  let t : Finset ℕ := insert n s
  let i : t := ⟨n, Finset.mem_insert_self n s⟩
  let j : s → t := fun k => ⟨k.val, Finset.mem_insert_of_mem k.property⟩
  let q : MvPolynomial t ℝ := MvPolynomial.rename j p
  have hp : finitePullback t (FiniteGaussian.productPolynomialL2 q) =
      polynomialCylinderEmbedding s p := by
    apply Lp.ext
    filter_upwards [finitePullback_coeFn t (FiniteGaussian.productPolynomialL2 q),
      (finiteProjection_measurePreserving t).quasiMeasurePreserving.ae_eq_comp
        (FiniteGaussian.productPolynomialL2_coeFn q),
      polynomialCylinderEmbedding_coeFn s p] with ω h₁ h₂ h₃
    rw [h₁, h₃]
    simp only [Function.comp_apply] at h₂
    rw [h₂]
    simp [q, j, polynomialCylinder, finiteProjection, Finset.restrict_def,
      MvPolynomial.eval_rename]
    congr 1
  refine ⟨t, FiniteGaussian.vectorL2Insert i (FiniteGaussian.productPolynomialL2 q), ?_⟩
  rw [finiteVectorPullback_insert, hp]

/-- The ranges of the actual finite Gaussian vector lifts jointly detect all
vector-valued Gaussian `L²` classes. -/
theorem eq_zero_of_finiteVectorPullback_orthogonal (u : GaussianVectorL2)
    (hu : ∀ (s : Finset ℕ) (v : FiniteGaussian.VectorGaussianL2 s),
      inner ℝ (finiteVectorPullback s v) u = 0) : u = 0 := by
  apply eq_zero_of_coordinatePolynomialVector_orthogonal u
  intro s p n
  obtain ⟨t, v, hv⟩ := coordinatePolynomialVector_mem_finite_sector s p n
  rw [← hv]
  exact hu t v

/-- Every element of the adjoint of the polynomial divergence has a genuine
finite-dimensional weak gradient after taking adjoints of both bounded lifts.
No graph convergence is claimed here. -/
theorem finiteSector_weak_gradient_graph (s : Finset ℕ)
    (f : GaussianL2) (g : GaussianVectorL2)
    (h : (f, g) ∈ cylindricalDivergence.adjoint.graph) :
    (((finitePullback s).toContinuousLinearMap.adjoint f),
      (finiteVectorPullback s).adjoint g) ∈
        (FiniteGaussian.polynomialDivergence (ι := s)).adjoint.graph := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (FiniteGaussian.polynomialDivergence_dense_domain (ι := s))]
  rw [Submodule.mem_adjoint_iff]
  intro a b hab
  rw [FiniteGaussian.polynomialDivergence_graph] at hab
  obtain ⟨v, hv⟩ := hab
  have hv₁ := congrArg Prod.fst hv
  have hv₂ := congrArg Prod.snd hv
  change FiniteGaussian.vectorPolynomialL2 v = a at hv₁
  change FiniteGaussian.productPolynomialL2 (FiniteGaussian.divergencePolynomial v) = b at hv₂
  have hlift : (finiteVectorPullback s a, finitePullback s b) ∈
      cylindricalDivergence.graph := by
    rw [← hv₁, ← hv₂]
    exact finitePolynomialDivergence_lift_graph s v
  have hpair : inner ℝ (finitePullback s b) f -
      inner ℝ (finiteVectorPullback s a) g = 0 :=
    (Submodule.mem_adjoint_iff cylindricalDivergence.graph (f, g)).mp
      ((cylindricalDivergence.adjoint_graph_eq_graph_adjoint
        cylindricalDivergence_dense_domain) ▸ h) _ _ hlift
  simpa only [ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap] using hpair

/-- The weak gradient of any vector in `Dom(δ₀*)` produces a concrete graph
pair of the already constructed closed infinite-dimensional derivative in each
finite sector. This is the exact local-to-global graph bridge before convergence. -/
theorem finiteSector_weak_gradient_lift_graph (s : Finset ℕ)
    (f : GaussianL2) (g : GaussianVectorL2)
    (h : (f, g) ∈ cylindricalDivergence.adjoint.graph) :
    (finitePullback s ((finitePullback s).toContinuousLinearMap.adjoint f),
      finiteVectorPullback s ((finiteVectorPullback s).adjoint g)) ∈
        closedCylindricalDerivative.graph :=
  finiteGradient_lift_closed_graph s _ _ (finiteSector_weak_gradient_graph s f g h)

/-- Orthogonal projection onto one finite scalar coordinate sector. -/
def finiteScalarProjection (s : Finset ℕ) : GaussianL2 →L[ℝ] GaussianL2 :=
  (finitePullback s).toContinuousLinearMap.comp
    (finitePullback s).toContinuousLinearMap.adjoint

theorem finiteScalarProjection_fix (s : Finset ℕ)
    (f : FiniteGaussian.ScalarGaussianL2 s) :
    finiteScalarProjection s (finitePullback s f) = finitePullback s f := by
  change (finitePullback s).toContinuousLinearMap
      ((finitePullback s).toContinuousLinearMap.adjoint
        ((finitePullback s).toContinuousLinearMap f)) =
      (finitePullback s).toContinuousLinearMap f
  have h := congrArg (fun T : FiniteGaussian.ScalarGaussianL2 s →L[ℝ]
      FiniteGaussian.ScalarGaussianL2 s => T f)
    (LinearIsometry.adjoint_comp_self (finitePullback s))
  change (finitePullback s).toContinuousLinearMap.adjoint
      ((finitePullback s).toContinuousLinearMap f) = f at h
  exact congrArg (finitePullback s).toContinuousLinearMap h

theorem finiteScalarProjection_norm_le (s : Finset ℕ) (f : GaussianL2) :
    ‖finiteScalarProjection s f‖ ≤ ‖f‖ := by
  let I := (finitePullback s).toContinuousLinearMap
  have hI : ‖I‖ ≤ 1 := (finitePullback s).norm_toContinuousLinearMap_le
  have hadj : ‖I.adjoint‖ = ‖I‖ := LinearIsometryEquiv.norm_map _ _
  calc
    ‖finiteScalarProjection s f‖ = ‖I (I.adjoint f)‖ := rfl
    _ ≤ ‖I‖ * ‖I.adjoint f‖ := I.le_opNorm _
    _ ≤ ‖I‖ * (‖I.adjoint‖ * ‖f‖) := by
      gcongr
      exact I.adjoint.le_opNorm _
    _ ≤ ‖f‖ := by
      rw [hadj]
      have hsq : ‖I‖ * ‖I‖ ≤ 1 := by nlinarith [norm_nonneg I]
      nlinarith [mul_le_mul_of_nonneg_right hsq (norm_nonneg f)]

/-- Finite-coordinate scalar orthogonal projections approximate arbitrary Gaussian
`L²` classes in norm. No derivative commutation is claimed. -/
theorem exists_finiteScalarProjection_approx (f : GaussianL2) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ s : Finset ℕ, ‖f - finiteScalarProjection s f‖ < ε := by
  obtain ⟨s, p, hp⟩ := exists_polynomialCylinder_approx f (ε / 2) (by positivity)
  let x := polynomialCylinderEmbedding s p
  have hfix : finiteScalarProjection s x = x :=
    finiteScalarProjection_fix s (FiniteGaussian.productPolynomialL2 p)
  refine ⟨s, ?_⟩
  have he : f - finiteScalarProjection s f =
      (f - x) - finiteScalarProjection s (f - x) := by
    simp [map_sub, hfix]
  rw [he]
  calc
    ‖(f - x) - finiteScalarProjection s (f - x)‖
        ≤ ‖f - x‖ + ‖finiteScalarProjection s (f - x)‖ := norm_sub_le _ _
    _ ≤ 2 * ‖f - x‖ := by nlinarith [finiteScalarProjection_norm_le s (f - x)]
    _ < ε := by linarith

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
