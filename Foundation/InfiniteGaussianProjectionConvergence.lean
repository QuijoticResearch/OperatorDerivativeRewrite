import Foundation.InfiniteGaussianCoordinateFields

/-! Directed finite-coordinate projections in the countable Gaussian product. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian

set_option backward.isDefEq.respectTransparency false

/-- Zero-extend a finite Euclidean coordinate vector into the ambient `ℓ²` fiber. -/
def finiteFiberMap (s : Finset ℕ) :
    EuclideanSpace ℝ s →L[ℝ] CoefficientSpace :=
  ∑ i : s, (ContinuousLinearMap.toSpanSingleton ℝ
    (lp.single 2 i.val (1 : ℝ))).comp (EuclideanSpace.proj i)

theorem finiteFiberMap_apply (s : Finset ℕ) (x : EuclideanSpace ℝ s) :
    finiteFiberMap s x = ∑ i : s, x i • lp.single 2 i.val (1 : ℝ) := by
  simp [finiteFiberMap]

theorem finiteFiberMap_basis (s : Finset ℕ) (i : s) :
    finiteFiberMap s (EuclideanSpace.single i (1 : ℝ)) =
      lp.single 2 i.val (1 : ℝ) := by
  rw [finiteFiberMap_apply]
  simp [Finset.sum_ite_eq']

theorem finiteFiberMap_orthonormal (s : Finset ℕ) :
    Orthonormal ℝ (fun i : s => (lp.single 2 i.val (1 : ℝ) : CoefficientSpace)) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases h : i = j
  · subst j
    simp
  · have hval : i.val ≠ j.val := fun he => h (Subtype.ext he)
    simp [lp.inner_single_left, hval, h]

/-- The finite-coordinate fiber inclusion preserves the Euclidean/`ℓ²` norm. -/
def finiteFiberIsometry (s : Finset ℕ) :
    EuclideanSpace ℝ s →ₗᵢ[ℝ] CoefficientSpace := by
  classical
  let b := EuclideanSpace.basisFun s ℝ
  have h : Orthonormal ℝ ((finiteFiberMap s).toLinearMap ∘ b.toBasis) := by
    change Orthonormal ℝ (fun i => finiteFiberMap s (b i))
    convert finiteFiberMap_orthonormal s using 1
    funext i
    simpa [b] using (finiteFiberMap_basis s i)
  exact (finiteFiberMap s).toLinearMap.isometryOfOrthonormal
    (v := b.toBasis) b.orthonormal h

theorem finiteFiberIsometry_apply (s : Finset ℕ) (x : EuclideanSpace ℝ s) :
    finiteFiberIsometry s x = ∑ i : s, x i • (lp.single 2 i.val (1 : ℝ) : CoefficientSpace) := by
  exact finiteFiberMap_apply s x

theorem finiteFiberIsometry_compLp_norm (s : Finset ℕ)
    (u : FiniteGaussian.VectorGaussianL2 s) :
    ‖(finiteFiberIsometry s).toContinuousLinearMap.compLpL 2
        (FiniteGaussian.productGaussian s) u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
    (Lp.aestronglyMeasurable _)
    (Lp.aestronglyMeasurable _)
  filter_upwards [(finiteFiberIsometry s).toContinuousLinearMap.coeFn_compLpL u] with x hx
  rw [hx]
  exact (finiteFiberIsometry s).norm_map (u x)

/-- Applying the finite fiber inclusion pointwise is an `L²` isometry. -/
def finiteFiberLpIsometry (s : Finset ℕ) :
    FiniteGaussian.VectorGaussianL2 s →ₗᵢ[ℝ]
      Lp CoefficientSpace 2 (FiniteGaussian.productGaussian s) where
  toLinearMap := ((finiteFiberIsometry s).toContinuousLinearMap.compLpL 2
    (FiniteGaussian.productGaussian s)).toLinearMap
  norm_map' := finiteFiberIsometry_compLp_norm s

/-- Pulling back a finite vector field and then including its fibers is isometric. -/
def finiteVectorIsometry (s : Finset ℕ) :
    FiniteGaussian.VectorGaussianL2 s →ₗᵢ[ℝ] GaussianVectorL2 :=
  (Lp.compMeasurePreservingₗᵢ ℝ (finiteProjection s)
    (finiteProjection_measurePreserving s)).comp (finiteFiberLpIsometry s)

theorem finiteVectorIsometry_coeFn (s : Finset ℕ)
    (u : FiniteGaussian.VectorGaussianL2 s) :
    finiteVectorIsometry s u =ᵐ[gaussianProduct]
      fun ω => finiteFiberIsometry s (u (finiteProjection s ω)) := by
  have h₁ := Lp.coeFn_compMeasurePreserving (finiteFiberLpIsometry s u)
    (finiteProjection_measurePreserving s)
  have h₂ := (finiteProjection_measurePreserving s).quasiMeasurePreserving.ae_eq_comp
    ((finiteFiberIsometry s).toContinuousLinearMap.coeFn_compLpL u)
  filter_upwards [h₁, h₂] with ω h₁ h₂
  exact h₁.trans h₂

theorem finiteVectorPullback_coeFn (s : Finset ℕ)
    (u : FiniteGaussian.VectorGaussianL2 s) :
    finiteVectorPullback s u =ᵐ[gaussianProduct]
      fun ω => finiteFiberIsometry s (u (finiteProjection s ω)) := by
  have hc (i : s) :
      scalarTensor (lp.single 2 i.val (1 : ℝ))
          (finitePullback s (FiniteGaussian.vectorL2Component i u)) =ᵐ[gaussianProduct]
        fun ω => u (finiteProjection s ω) i •
          (lp.single 2 i.val (1 : ℝ) : CoefficientSpace) := by
    have hi := (finiteProjection_measurePreserving s).quasiMeasurePreserving.ae_eq_comp
      (FiniteGaussian.vectorL2Component_coeFn i u)
    filter_upwards [scalarTensor_coeFn (lp.single 2 i.val (1 : ℝ))
        (finitePullback s (FiniteGaussian.vectorL2Component i u)),
      finitePullback_coeFn s (FiniteGaussian.vectorL2Component i u), hi]
      with ω ht hp hi
    rw [ht, hp]
    simpa only [Function.comp_apply] using congrArg
      (fun a : ℝ => a • (lp.single 2 i.val (1 : ℝ) : CoefficientSpace)) hi
  rw [finiteVectorPullback_apply]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i : s => scalarTensor (lp.single 2 i.val (1 : ℝ))
        (finitePullback s (FiniteGaussian.vectorL2Component i u))),
    ae_all_iff.mpr hc] with ω hsum hi
  rw [hsum, finiteFiberIsometry_apply]
  exact Finset.sum_congr rfl (fun i _ => hi i)

theorem finiteVectorPullback_eq_isometry (s : Finset ℕ) :
    finiteVectorPullback s = (finiteVectorIsometry s).toContinuousLinearMap := by
  ext u
  exact (finiteVectorPullback_coeFn s u).trans (finiteVectorIsometry_coeFn s u).symm

/-- Orthogonal projection onto the finite Gaussian sample and fiber-coordinate sector. -/
def finiteVectorProjection (s : Finset ℕ) :
    GaussianVectorL2 →L[ℝ] GaussianVectorL2 :=
  (finiteVectorPullback s).comp (finiteVectorPullback s).adjoint

theorem finiteVectorProjection_fix (s : Finset ℕ)
    (u : FiniteGaussian.VectorGaussianL2 s) :
    finiteVectorProjection s (finiteVectorPullback s u) = finiteVectorPullback s u := by
  change finiteVectorPullback s ((finiteVectorPullback s).adjoint (finiteVectorPullback s u)) =
    finiteVectorPullback s u
  rw [finiteVectorPullback_eq_isometry]
  change (finiteVectorIsometry s).toContinuousLinearMap
    ((finiteVectorIsometry s).toContinuousLinearMap.adjoint
      ((finiteVectorIsometry s).toContinuousLinearMap u)) =
      (finiteVectorIsometry s).toContinuousLinearMap u
  have h := congrArg (fun T : FiniteGaussian.VectorGaussianL2 s →L[ℝ]
      FiniteGaussian.VectorGaussianL2 s => T u)
    (LinearIsometry.adjoint_comp_self (finiteVectorIsometry s))
  change (finiteVectorIsometry s).toContinuousLinearMap.adjoint
      ((finiteVectorIsometry s).toContinuousLinearMap u) = u at h
  exact congrArg (finiteVectorIsometry s).toContinuousLinearMap h

theorem finiteVectorProjection_norm_le (s : Finset ℕ) (u : GaussianVectorL2) :
    ‖finiteVectorProjection s u‖ ≤ ‖u‖ := by
  let J := finiteVectorPullback s
  have hJ : ‖J‖ ≤ 1 := by
    change ‖finiteVectorPullback s‖ ≤ 1
    rw [finiteVectorPullback_eq_isometry]
    exact (finiteVectorIsometry s).norm_toContinuousLinearMap_le
  have hadj : ‖J.adjoint‖ = ‖J‖ := LinearIsometryEquiv.norm_map _ _
  calc
    ‖finiteVectorProjection s u‖ = ‖J (J.adjoint u)‖ := rfl
    _ ≤ ‖J‖ * ‖J.adjoint u‖ := J.le_opNorm _
    _ ≤ ‖J‖ * (‖J.adjoint‖ * ‖u‖) := by
      gcongr
      exact J.adjoint.le_opNorm _
    _ ≤ ‖u‖ := by
      rw [hadj]
      have hsq : ‖J‖ * ‖J‖ ≤ 1 := by nlinarith [norm_nonneg J]
      nlinarith [mul_le_mul_of_nonneg_right hsq (norm_nonneg u)]

/-- A polynomial depending on coordinates in `s` belongs to every larger scalar sector. -/
theorem finiteScalarProjection_fix_polynomial_of_subset (s t : Finset ℕ)
    (hst : s ⊆ t) (p : MvPolynomial s ℝ) :
    finiteScalarProjection t (polynomialCylinderEmbedding s p) =
      polynomialCylinderEmbedding s p := by
  classical
  let j : s → t := fun i => ⟨i.val, hst i.property⟩
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
  rw [← hp]
  exact finiteScalarProjection_fix t (FiniteGaussian.productPolynomialL2 q)

/-- A coordinate polynomial rank field is fixed by every vector projection
containing both its sample coordinates and its output coordinate. -/
theorem finiteVectorProjection_fix_coordinate_of_subset (s t : Finset ℕ)
    (hst : s ⊆ t) (p : MvPolynomial s ℝ) (n : ℕ) (hn : n ∈ t) :
    finiteVectorProjection t
        (scalarTensor (lp.single 2 n (1 : ℝ)) (polynomialCylinderEmbedding s p)) =
      scalarTensor (lp.single 2 n (1 : ℝ)) (polynomialCylinderEmbedding s p) := by
  let f := (finitePullback t).toContinuousLinearMap.adjoint
    (polynomialCylinderEmbedding s p)
  have hp : finitePullback t f = polynomialCylinderEmbedding s p := by
    change finiteScalarProjection t (polynomialCylinderEmbedding s p) = _
    exact finiteScalarProjection_fix_polynomial_of_subset s t hst p
  have hfield := finiteVectorPullback_insert t ⟨n, hn⟩ f
  rw [hp] at hfield
  let v := FiniteGaussian.vectorL2Insert (⟨n, hn⟩ : t) f
  have hv : finiteVectorPullback t v =
      scalarTensor (lp.single 2 n (1 : ℝ)) (polynomialCylinderEmbedding s p) := hfield
  calc
    finiteVectorProjection t
        (scalarTensor (lp.single 2 n (1 : ℝ)) (polynomialCylinderEmbedding s p)) =
      finiteVectorProjection t (finiteVectorPullback t v) := congrArg _ hv.symm
    _ = finiteVectorPullback t v := finiteVectorProjection_fix t v
    _ = _ := hv

/-- Every finite polynomial coordinate field is eventually fixed by the
increasing vector projections. The same cutoff handles sample and fiber indices. -/
theorem finiteVectorProjection_eventually_fix_core (u : GaussianVectorL2)
    (hu : u ∈ coordinatePolynomialVectorDomain) :
    ∀ᶠ N : ℕ in atTop, finiteVectorProjection (Finset.range N) u = u := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨s, p, n, rfl⟩ := hx
      obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range (insert n s)
      filter_upwards [eventually_ge_atTop N] with k hk
      have hs : s ⊆ Finset.range k :=
        (Finset.subset_insert n s).trans (hN.trans (Finset.range_mono hk))
      have hn : n ∈ Finset.range k :=
        hN.trans (Finset.range_mono hk) (Finset.mem_insert_self n s)
      exact finiteVectorProjection_fix_coordinate_of_subset s (Finset.range k)
        hs p n hn
  | zero =>
      exact Filter.Eventually.of_forall (fun N => map_zero _)
  | add x y hx hy ihx ihy =>
      filter_upwards [ihx, ihy] with N h₁ h₂
      rw [map_add, h₁, h₂]
  | smul a x hx ih =>
      filter_upwards [ih] with N h
      rw [map_smul, h]

/-- The genuine finite-sector vector projections converge strongly along the
same increasing coordinate exhaustion as the scalar projections. -/
theorem finiteVectorProjection_range_tendsto (u : GaussianVectorL2) :
    Tendsto (fun N : ℕ => finiteVectorProjection (Finset.range N) u) atTop (𝓝 u) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨v, hv⟩ := exists_coordinatePolynomialVector_approx u (ε / 2) (by positivity)
  have hfix := finiteVectorProjection_eventually_fix_core v.1 v.2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hfix
  refine ⟨N, ?_⟩
  intro n hn
  have hfixn := hN n hn
  have he : finiteVectorProjection (Finset.range n) u - u =
      finiteVectorProjection (Finset.range n) (u - v.1) - (u - v.1) := by
    rw [map_sub, hfixn]
    abel
  have hc := finiteVectorProjection_norm_le (Finset.range n) (u - v.1)
  have ht := norm_sub_le (finiteVectorProjection (Finset.range n) (u - v.1)) (u - v.1)
  rw [dist_eq_norm, he]
  linarith

/-- Scalar conditional-coordinate projections converge along the canonical
increasing exhaustion, not merely along an unspecified finite subnet. -/
theorem finiteScalarProjection_range_tendsto (f : GaussianL2) :
    Tendsto (fun N : ℕ => finiteScalarProjection (Finset.range N) f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨s, p, hp⟩ := exists_polynomialCylinder_approx f (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s
  refine ⟨N, ?_⟩
  intro n hn
  let x := polynomialCylinderEmbedding s p
  have hs : s ⊆ Finset.range n := hN.trans (Finset.range_mono hn)
  have hfix : finiteScalarProjection (Finset.range n) x = x :=
    finiteScalarProjection_fix_polynomial_of_subset s (Finset.range n) hs p
  have he : f - finiteScalarProjection (Finset.range n) f =
      (f - x) - finiteScalarProjection (Finset.range n) (f - x) := by
    rw [map_sub, hfix]
    abel
  have hc := finiteScalarProjection_norm_le (Finset.range n) (f - x)
  have ht := norm_sub_le (f - x) (finiteScalarProjection (Finset.range n) (f - x))
  rw [dist_eq_norm, ← norm_neg, neg_sub, he]
  have hpx : ‖f - x‖ < ε / 2 := hp
  linarith

/-- Both coordinates of a weak gradient pair are projected by the same finite
coordinate cutoff, and each pair lies in the closed derivative graph. -/
theorem finiteSector_weak_gradient_range_graph (f : GaussianL2)
    (g : GaussianVectorL2)
    (h : (f, g) ∈ cylindricalDivergence.adjoint.graph) (N : ℕ) :
    (finiteScalarProjection (Finset.range N) f,
      finiteVectorProjection (Finset.range N) g) ∈
        closedCylindricalDerivative.graph := by
  exact finiteSector_weak_gradient_lift_graph (Finset.range N) f g h

/-- Scalar and vector finite-sector projections converge simultaneously in the
product Hilbert space, with no componentwise divergence assumption. -/
theorem finiteSector_projections_range_tendsto (f : GaussianL2) (g : GaussianVectorL2) :
    Tendsto (fun N : ℕ =>
      (finiteScalarProjection (Finset.range N) f,
        finiteVectorProjection (Finset.range N) g)) atTop (𝓝 (f, g)) :=
  (finiteScalarProjection_range_tendsto f).prodMk_nhds
    (finiteVectorProjection_range_tendsto g)

/-- Every weak gradient of the polynomial divergence belongs to the graph of
the closed genuine derivative. This is the missing essential-adjointness step. -/
theorem cylindricalDivergence_adjoint_le_closedDerivative :
    cylindricalDivergence.adjoint ≤ closedCylindricalDerivative := by
  apply LinearPMap.le_of_le_graph
  rintro ⟨f, g⟩ h
  exact closedCylindricalDerivative_isClosed.mem_of_tendsto
    (finiteSector_projections_range_tendsto f g)
    (Eventually.of_forall (finiteSector_weak_gradient_range_graph f g h))

/-- The closed infinite-dimensional Malliavin derivative is exactly the
Hilbert adjoint of the genuine polynomial cylindrical divergence. -/
theorem cylindricalDivergence_adjoint_eq_closedDerivative :
    cylindricalDivergence.adjoint = closedCylindricalDerivative :=
  le_antisymm cylindricalDivergence_adjoint_le_closedDerivative
    closedCylindricalDerivative_le_cylindricalDivergence_adjoint

/-- Finite-rank polynomial cylindrical vector fields form a graph core for
the full Hilbert-space divergence `D*`. -/
theorem closedPolynomialDivergence_eq_hilbertDivergence :
    closedPolynomialDivergence = hilbertDivergence :=
  polynomialDivergence_core_iff_adjoint_identification.mpr
    cylindricalDivergence_adjoint_eq_closedDerivative

/-- Every vector in the maximal divergence graph has a sequence of genuine
finite-rank polynomial cylindrical fields converging in the divergence graph norm. -/
theorem hilbertDivergence_polynomial_graph_core_sequence
    (u : GaussianVectorL2) (g : GaussianL2)
    (h : (u, g) ∈ hilbertDivergence.graph) :
    ∃ v : ℕ → cylindricalDivergence.domain,
      Tendsto (fun N => ((v N : GaussianVectorL2), cylindricalDivergence (v N)))
        atTop (𝓝 (u, g)) := by
  have hc : (u, g) ∈ closure (cylindricalDivergence.graph :
      Set (GaussianVectorL2 × GaussianL2)) := by
    change (u, g) ∈ cylindricalDivergence.graph.topologicalClosure
    rw [cylindricalDivergence_isClosable.graph_closure_eq_closure_graph]
    change (u, g) ∈ closedPolynomialDivergence.graph
    rw [closedPolynomialDivergence_eq_hilbertDivergence]
    exact h
  obtain ⟨z, hz, ht⟩ := mem_closure_iff_seq_limit.mp hc
  let v : ℕ → cylindricalDivergence.domain := fun N =>
    ⟨(z N).1, LinearPMap.mem_domain_of_mem_graph (hz N)⟩
  refine ⟨v, ?_⟩
  have he (N : ℕ) : ((v N : GaussianVectorL2), cylindricalDivergence (v N)) = z N := by
    apply Prod.ext
    · rfl
    · exact ((cylindricalDivergence.image_iff (v N).2).mpr (hz N)).symm
  simpa only [he] using ht

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
