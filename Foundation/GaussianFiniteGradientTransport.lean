import Foundation.GaussianAnalyticCoordinateIBP
import Foundation.GaussianOrthonormalPolynomialLaw
import Foundation.BochnerLinearIsometry

/-! Actual finite Gaussian closed-gradient transport along orthonormal
observations of the constructed infinite Gaussian product. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianFiniteGradientTransport
open InfiniteGaussian
variable {I : Type*} [Fintype I]
set_option backward.isDefEq.respectTransparency false

def directionMap (v : I → CoefficientSpace) : EuclideanSpace ℝ I →L[ℝ] CoefficientSpace :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (v i)).comp (EuclideanSpace.proj i)

theorem directionMap_apply (v : I → CoefficientSpace) (x : EuclideanSpace ℝ I) :
    directionMap v x = ∑ i, x i • v i := by simp [directionMap]

open scoped Classical in
theorem directionMap_basis (v : I → CoefficientSpace) (i : I) :
    directionMap v (EuclideanSpace.single i (1 : ℝ)) = v i := by
  classical
  rw [directionMap_apply]
  simp [Finset.sum_ite_eq']

def directionIsometry (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) :
    EuclideanSpace ℝ I →ₗᵢ[ℝ] CoefficientSpace := by
  classical
  let b := EuclideanSpace.basisFun I ℝ
  have he : Orthonormal ℝ ((directionMap v).toLinearMap ∘ b.toBasis) := by
    change Orthonormal ℝ (fun i => directionMap v (b i))
    convert hv using 1
    funext i
    exact directionMap_basis v i
  exact (directionMap v).toLinearMap.isometryOfOrthonormal (v := b.toBasis) b.orthonormal he

theorem directionIsometry_apply (v : I → CoefficientSpace) (hv : Orthonormal ℝ v)
    (x : EuclideanSpace ℝ I) : directionIsometry v hv x = ∑ i, x i • v i :=
  directionMap_apply v x

theorem observations_measurePreserving (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) :
    MeasurePreserving (firstChaosFamily v) gaussianProduct (FiniteGaussian.productGaussian I) :=
  ⟨Measurable.of_eval (fun i => (Lp.stronglyMeasurable (firstChaosEmbedding (v i))).measurable),
    (GaussianOrthonormalPolynomialLaw.orthonormal_firstChaosFamily_law v hv).map_eq⟩

def scalarPullback (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) :
    FiniteGaussian.ScalarGaussianL2 I →ₗᵢ[ℝ] GaussianL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (firstChaosFamily v) (observations_measurePreserving v hv)

def vectorPullback (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) :
    FiniteGaussian.VectorGaussianL2 I →ₗᵢ[ℝ] GaussianVectorL2 :=
  (Lp.compMeasurePreservingₗᵢ ℝ (firstChaosFamily v) (observations_measurePreserving v hv)).comp
    (BochnerLinearIsometry.lift (FiniteGaussian.productGaussian I) (directionIsometry v hv))

theorem scalarPullback_ae (v : I → CoefficientSpace) (hv : Orthonormal ℝ v)
    (f : FiniteGaussian.ScalarGaussianL2 I) :
    scalarPullback v hv f =ᵐ[gaussianProduct] fun ω => f (firstChaosFamily v ω) :=
  Lp.coeFn_compMeasurePreserving f (observations_measurePreserving v hv)

theorem vectorPullback_ae (v : I → CoefficientSpace) (hv : Orthonormal ℝ v)
    (g : FiniteGaussian.VectorGaussianL2 I) :
    vectorPullback v hv g =ᵐ[gaussianProduct]
      (fun ω => directionIsometry v hv (g (firstChaosFamily v ω))) := by
  have ha := (observations_measurePreserving v hv).quasiMeasurePreserving.ae_eq_comp
    (BochnerLinearIsometry.lift_coeFn (FiniteGaussian.productGaussian I) (directionIsometry v hv) g)
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (BochnerLinearIsometry.lift (FiniteGaussian.productGaussian I) (directionIsometry v hv) g)
      (observations_measurePreserving v hv), ha] with ω hp ha
  exact hp.trans ha

theorem scalarPullback_polynomial (v : I → CoefficientSpace) (hv : Orthonormal ℝ v)
    (p : MvPolynomial I ℝ) :
    scalarPullback v hv (FiniteGaussian.productPolynomialL2 p) = isonormalCylinderL2 v p := by
  apply Lp.ext
  have ha := (observations_measurePreserving v hv).quasiMeasurePreserving.ae_eq_comp
    (FiniteGaussian.productPolynomialL2_coeFn p)
  filter_upwards [scalarPullback_ae v hv (FiniteGaussian.productPolynomialL2 p),
    ha, isonormalCylinderL2_coeFn v p] with ω hp ha hc
  dsimp only [Function.comp_def] at ha
  rw [hp, ha, hc]
  rfl

theorem vectorPullback_gradient_polynomial (v : I → CoefficientSpace) (hv : Orthonormal ℝ v)
    (p : MvPolynomial I ℝ) :
    vectorPullback v hv (FiniteGaussian.gradientPolynomialL2 p) = isonormalCylinderGradientL2 v p := by
  apply Lp.ext
  have ha := (observations_measurePreserving v hv).quasiMeasurePreserving.ae_eq_comp
    (FiniteGaussian.vectorPolynomialL2_coeFn (FiniteGaussian.gradientPolynomial p))
  filter_upwards [vectorPullback_ae v hv (FiniteGaussian.gradientPolynomialL2 p),
    ha, isonormalCylinderGradientL2_coeFn v p] with ω hp ha hc
  change FiniteGaussian.gradientPolynomialL2 p (firstChaosFamily v ω) = _ at ha
  rw [hp, ha, hc, directionIsometry_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

theorem polynomial_graph_transport (v : I → CoefficientSpace) (hv : Orthonormal ℝ v)
    (p : MvPolynomial I ℝ) :
    (scalarPullback v hv (FiniteGaussian.productPolynomialL2 p),
      vectorPullback v hv (FiniteGaussian.gradientPolynomialL2 p)) ∈ closedCylindricalDerivative.graph := by
  rw [scalarPullback_polynomial, vectorPullback_gradient_polynomial]
  have hg := closedCylindricalDerivative_core_graph
    (GaussianNumberSectors.cylinderCore v p)
  rw [show polynomialDerivative (GaussianNumberSectors.cylinderCore v p) =
      isonormalCylinderGradientL2 v p from polynomialDerivative_on_cylinder _ _] at hg
  exact hg

/-- Full finite closed-gradient graph transport, valid even for an empty
orthonormal family; no covariance inversion or new graph-core premise. -/
theorem closed_gradient_transport (v : I → CoefficientSpace) (hv : Orthonormal ℝ v)
    {f : FiniteGaussian.ScalarGaussianL2 I} {g : FiniteGaussian.VectorGaussianL2 I}
    (hfg : (f, g) ∈ (FiniteGaussian.closedGradient (ι := I)).graph) :
    (scalarPullback v hv f, vectorPullback v hv g) ∈ closedCylindricalDerivative.graph := by
  classical
  have hfg' : (f, g) ∈ (FiniteGaussian.polynomialDivergence (ι := I)).adjoint.graph := by
    rwa [← FiniteGaussian.closedGradient_eq_divergence_adjoint]
  have ht := FiniteGaussian.divergence_adjoint_truncation_tendsto f g
  have hu := (scalarPullback v hv).continuous.continuousAt.tendsto.comp ht.fst_nhds
  have hw := (vectorPullback v hv).continuous.continuousAt.tendsto.comp ht.snd_nhds
  apply closedCylindricalDerivative_isClosed.mem_of_tendsto (hu.prodMk_nhds hw)
  apply Eventually.of_forall
  intro N
  have hn := FiniteGaussian.divergence_adjoint_truncation_graph f g hfg' N
  rw [FiniteGaussian.polynomialGradient_graph] at hn
  obtain ⟨p, hp⟩ := hn
  have hp1 := congrArg Prod.fst hp
  have hp2 := congrArg Prod.snd hp
  change FiniteGaussian.productPolynomialL2 p = FiniteGaussian.scalarHermiteTruncation f (N + 1) at hp1
  change FiniteGaussian.gradientPolynomialL2 p = FiniteGaussian.vectorHermiteTruncation g N at hp2
  dsimp only [Function.comp_def]
  rw [← hp1, ← hp2]
  exact polynomial_graph_transport v hv p

/-- Bounded analytic chain calculus on actual orthonormal Gaussian cylinders,
including the empty family, with a genuine infinite-product derivative graph. -/
theorem bounded_orthonormal_chain_graph {n : ℕ} (v : Fin n → CoefficientSpace)
    (hv : Orthonormal ℝ v) (p : MvPolynomial (Fin n) ℝ)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun ω => φ (isonormalCylinder v p ω)) ∧
      G =ᵐ[gaussianProduct] (fun ω => dφ (isonormalCylinder v p ω) • isonormalCylinderGradient v p ω) := by
  cases n with
  | zero =>
    let c := MvPolynomial.eval (fun _ : Fin 0 => (0 : ℝ)) p
    refine ⟨φ c • gaussianOne, 0, closedDerivative_constant_graph _, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_smul (φ c) gaussianOne, gaussianOne_coeFn] with ω hs ho
      rw [hs, Pi.smul_apply, ho]
      have he : firstChaosFamily v ω = fun _ : Fin 0 => (0 : ℝ) := Subsingleton.elim _ _
      change φ c * 1 = φ (MvPolynomial.eval (firstChaosFamily v ω) p)
      rw [mul_one, he]
    · filter_upwards [Lp.coeFn_zero (E := CoefficientSpace) (p := 2) (μ := gaussianProduct)] with ω hω
      rw [hω]
      simp [isonormalCylinderGradient]
  | succ n =>
    obtain ⟨hf, hg, hfg⟩ := GaussianAnalyticCoordinateIBP.bounded_polynomial_chain_graph
      p φ dφ hd hc A B hA hB
    refine ⟨scalarPullback v hv (hf.toLp _), vectorPullback v hv (hg.toLp _),
      closed_gradient_transport v hv hfg, ?_, ?_⟩
    · have ha := (observations_measurePreserving v hv).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp
      filter_upwards [scalarPullback_ae v hv (hf.toLp _), ha] with ω hp ha
      dsimp only [Function.comp_def] at ha
      rw [hp, ha]
      rfl
    · have ha := (observations_measurePreserving v hv).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp
      filter_upwards [vectorPullback_ae v hv (hg.toLp _), ha] with ω hp ha
      dsimp only [Function.comp_def] at ha
      rw [hp, ha, map_smul, directionIsometry_apply]
      rfl

/-- Arbitrary dependent finite observations are handled through their actual
finite Hilbert span. No independence or covariance inverse is assumed. -/
theorem bounded_cylinder_chain_graph (h : I → CoefficientSpace) (p : MvPolynomial I ℝ)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun ω => φ (isonormalCylinder h p ω)) ∧
      G =ᵐ[gaussianProduct] (fun ω => dφ (isonormalCylinder h p ω) • isonormalCylinderGradient h p ω) := by
  classical
  let S := Submodule.span ℝ (Set.range h)
  letI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range h)
  letI : MeasurableSpace S := borel S
  letI : BorelSpace S := ⟨rfl⟩
  let a : I → S := fun i => ⟨h i, Submodule.subset_span (Set.mem_range_self i)⟩
  let b := stdOrthonormalBasis ℝ S
  let v : Fin (Module.finrank ℝ S) → CoefficientSpace := fun j => S.subtypeₗᵢ (b j)
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℝ (S.subtypeₗᵢ (b i)) (S.subtypeₗᵢ (b j)) = _
    rw [S.subtypeₗᵢ.inner_map_map]
    exact orthonormal_iff_ite.mp b.orthonormal i j
  let q := FiniteGaussian.basisPolynomialMap a p
  have hf : isonormalCylinder h p =ᵐ[gaussianProduct] isonormalCylinder v q := by
    have ha := isonormalCylinder_finiteGaussianPoint S.subtypeₗᵢ a p
    filter_upwards [ha] with ω ha
    change isonormalCylinder h p ω = _ at ha
    rw [ha]
    exact (FiniteGaussian.basisPolynomialMap_eval a p (firstChaosFamily v ω)).symm
  have hgrad : isonormalCylinderGradient h p =ᵐ[gaussianProduct] isonormalCylinderGradient v q := by
    have ha := isonormalCylinderGradient_finiteGaussianPoint S.subtypeₗᵢ a p
    have he (ω : SampleSpace) : isonormalCylinderGradient v q ω =
        S.subtypeₗᵢ (FiniteGaussian.cylinderGradient a p (finiteGaussianPoint S.subtypeₗᵢ ω)) := by
      rw [← b.sum_repr' (FiniteGaussian.cylinderGradient a p (finiteGaussianPoint S.subtypeₗᵢ ω)),
        map_sum]
      simp only [map_smul]
      change (∑ j, MvPolynomial.eval (firstChaosFamily v ω) (MvPolynomial.pderiv j q) • v j) = _
      apply Finset.sum_congr rfl
      intro j hj
      have hc : MvPolynomial.eval (firstChaosFamily v ω) (MvPolynomial.pderiv j q) =
          inner ℝ (FiniteGaussian.cylinderGradient a p (finiteGaussianPoint S.subtypeₗᵢ ω)) (b j) :=
        FiniteGaussian.basisPolynomialMap_pderiv_eval a p j (firstChaosFamily v ω)
      rw [hc, real_inner_comm]
    filter_upwards [ha] with ω ha
    change isonormalCylinderGradient h p ω = _ at ha
    exact ha.trans (he ω).symm
  obtain ⟨F, G, hfg, hF, hG⟩ := bounded_orthonormal_chain_graph v hv q φ dφ hd hc A B hA hB
  refine ⟨F, G, hfg, ?_, ?_⟩
  · filter_upwards [hF, hf] with ω hF hf
    rw [hF, ← hf]
  · filter_upwards [hG, hf, hgrad] with ω hG hf hgrad
    rw [hG, ← hf, ← hgrad]

/-- Analytic bounded chain rule on the ENTIRE existing polynomial cylindrical
operator domain, including arbitrary infinite-support Hilbert directions. -/
theorem bounded_core_chain_graph (u : polynomialCylindricalDomain)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun ω => φ ((u : GaussianL2) ω)) ∧
      G =ᵐ[gaussianProduct] (fun ω => dφ ((u : GaussianL2) ω) • polynomialDerivative u ω) := by
  let r := polynomialRepresentation u
  have hu : (u : GaussianL2) =ᵐ[gaussianProduct] isonormalCylinder r.directions r.polynomial := by
    have he := isonormalCylinderL2_coeFn r.directions r.polynomial
    rw [r.represents] at he
    exact he
  have hg : polynomialDerivative u =ᵐ[gaussianProduct]
      isonormalCylinderGradient r.directions r.polynomial := by
    have he : polynomialDerivative u = isonormalCylinderGradientL2 r.directions r.polynomial :=
      polynomialGradient_agrees u r.directions r.polynomial r.represents
    rw [he]
    exact isonormalCylinderGradientL2_coeFn _ _
  obtain ⟨F, G, hfg, hF, hG⟩ := bounded_cylinder_chain_graph r.directions r.polynomial
    φ dφ hd hc A B hA hB
  refine ⟨F, G, hfg, ?_, ?_⟩
  · filter_upwards [hF, hu] with ω hF hu
    rw [hu]
    exact hF
  · filter_upwards [hG, hu, hg] with ω hG hu hg
    rw [hu, hg]
    exact hG

end OperatorDerivativeRewrite.Foundation.GaussianFiniteGradientTransport
