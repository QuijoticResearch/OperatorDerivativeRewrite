import Foundation.IBMReflectedGaussianSobolev
import Foundation.GaussianHermiteDomains
import Mathlib.Algebra.MvPolynomial.Equiv

/-! Transport of the actual one-dimensional Gaussian derivative along a
normalized first-chaos observation in the constructed clock probability space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Polynomial
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockObservationGraph
open InfiniteGaussian
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

theorem observation_measurePreserving (h : CoefficientSpace) (hh : ‖h‖ = 1) :
    MeasurePreserving (firstChaosEmbedding h) gaussianProduct GaussianCore.γ := by
  refine ⟨(Lp.stronglyMeasurable _).measurable, ?_⟩
  rw [firstChaos_law]
  simp only [hh, one_pow]
  rfl

def pullback (h : CoefficientSpace) (hh : ‖h‖ = 1) :
    GaussianCore.GaussianL2 →ₗᵢ[ℝ] GaussianL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (firstChaosEmbedding h) (observation_measurePreserving h hh)

theorem pullback_ae (h : CoefficientSpace) (hh : ‖h‖ = 1) (f : GaussianCore.GaussianL2) :
    pullback h hh f =ᵐ[gaussianProduct] fun ω => f (firstChaosEmbedding h ω) :=
  Lp.coeFn_compMeasurePreserving f (observation_measurePreserving h hh)

theorem pderiv_univariate (p : ℝ[X]) :
    MvPolynomial.pderiv () (p.toMvPolynomial ()) = p.derivative.toMvPolynomial () := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.derivative_add, hp, hq]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.derivative_C_mul_X_pow]
    simp only [map_mul, map_pow, Polynomial.toMvPolynomial_C, Polynomial.toMvPolynomial_X,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
      MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self, mul_one]
    simp [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

theorem pullback_polynomial (h : CoefficientSpace) (hh : ‖h‖ = 1) (p : ℝ[X]) :
    pullback h hh (GaussianCore.polynomialL2 p) =
      isonormalCylinderL2 (fun _ : Unit => h) (p.toMvPolynomial ()) := by
  apply Lp.ext
  have hp := (observation_measurePreserving h hh).quasiMeasurePreserving.ae_eq_comp
    (GaussianCore.polynomialL2_coeFn p)
  filter_upwards [pullback_ae h hh (GaussianCore.polynomialL2 p), hp,
    isonormalCylinderL2_coeFn (fun _ : Unit => h) (p.toMvPolynomial ())] with ω hl hp hr
  dsimp only [Function.comp_def] at hp
  rw [hl, hp, hr]
  exact (MvPolynomial.eval_toMvPolynomial (fun _ : Unit => firstChaosEmbedding h ω) () p).symm

theorem pullback_polynomial_graph (h : CoefficientSpace) (hh : ‖h‖ = 1) (p : ℝ[X]) :
    (pullback h hh (GaussianCore.polynomialL2 p),
      scalarTensor h (pullback h hh (GaussianCore.polynomialL2 p.derivative))) ∈
        closedCylindricalDerivative.graph := by
  let c : polynomialCylindricalDomain :=
    ⟨isonormalCylinderL2 (fun _ : Unit => h) (p.toMvPolynomial ()), isonormalCylinderL2_mem_core _ _⟩
  have hd : polynomialDerivative c =
      scalarTensor h (pullback h hh (GaussianCore.polynomialL2 p.derivative)) := by
    rw [show polynomialDerivative c =
      isonormalCylinderGradientL2 (fun _ : Unit => h) (p.toMvPolynomial ()) from
        polynomialDerivative_on_cylinder _ _]
    apply Lp.ext
    filter_upwards [isonormalCylinderGradientL2_coeFn (fun _ : Unit => h) (p.toMvPolynomial ()),
      scalarTensor_coeFn h (pullback h hh (GaussianCore.polynomialL2 p.derivative)),
      isonormalCylinderL2_coeFn (fun _ : Unit => h) (p.derivative.toMvPolynomial ())] with ω hg ht hp
    rw [hg, ht, pullback_polynomial h hh p.derivative, hp]
    simp only [isonormalCylinderGradient, Fintype.sum_unique]
    change isonormalCylinder (fun _ : Unit => h)
      (MvPolynomial.pderiv () (p.toMvPolynomial ())) ω • h = _
    rw [pderiv_univariate]
  have hc := closedCylindricalDerivative_core_graph c
  rw [hd] at hc
  simpa only [pullback_polynomial, c] using hc

/-- Transport the entire existing closed graph, not only its polynomial core. -/
theorem pullback_closed_graph (h : CoefficientSpace) (hh : ‖h‖ = 1)
    {f g : GaussianCore.GaussianL2} (hfg : (f, g) ∈ GaussianCore.closedDerivative.graph) :
    (pullback h hh f, scalarTensor h (pullback h hh g)) ∈ closedCylindricalDerivative.graph := by
  have ha := GaussianCore.divergence_adjoint_hermite_approximation f g
    (by rwa [← GaussianCore.closedDerivative_eq_divergence_adjoint])
  let L := (pullback h hh).toContinuousLinearMap
  let M := (IBMClockAverageCandidate.tensorBilinear h).comp L
  have ht := ((L.continuous.comp continuous_fst).prodMk
    (M.continuous.comp continuous_snd)).continuousAt.tendsto.comp ha.2
  have he : M g = scalarTensor h (pullback h hh g) := IBMClockAverageCandidate.tensorBilinear_eq h _
  have ht' : Tendsto (fun N => (L (GaussianCore.hermiteTruncation f (N + 1)),
      M (GaussianCore.hermiteTruncation g N))) atTop (𝓝 (L f, M g)) := ht
  rw [he] at ht'
  apply closedCylindricalDerivative_isClosed.mem_of_tendsto ht'
  apply Eventually.of_forall
  intro N
  have hn := ha.1 N
  rw [GaussianCore.polynomialDerivative_graph] at hn
  obtain ⟨p, hp⟩ := hn
  have hp1 := congrArg Prod.fst hp
  have hp2 := congrArg Prod.snd hp
  change GaussianCore.polynomialL2 p = GaussianCore.hermiteTruncation f (N + 1) at hp1
  change GaussianCore.polynomialL2 p.derivative = GaussianCore.hermiteTruncation g N at hp2
  change (L (GaussianCore.hermiteTruncation f (N + 1)), M (GaussianCore.hermiteTruncation g N)) ∈ _
  rw [← hp1, ← hp2]
  change (pullback h hh (GaussianCore.polynomialL2 p),
    IBMClockAverageCandidate.tensorBilinear h (pullback h hh (GaussianCore.polynomialL2 p.derivative))) ∈ _
  rw [IBMClockAverageCandidate.tensorBilinear_eq]
  exact pullback_polynomial_graph h hh p

/-- Actual ambient Gaussian representatives and their actual closed derivative,
for every scalar scenery test at a normalized clock observation. -/
theorem reflected_observation_graph (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (n : ℕ) (V : GaussianL2) (a : ℝ) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun ω => inner ℝ V
        (IBMContinuousScenery.wholeLineScenery (IBMMollifier.kernel n)
          (a * |firstChaosEmbedding h ω|))) ∧
      G =ᵐ[gaussianProduct] (fun ω => (a * inner ℝ V
        (IBMClockAverageCandidate.sourceColumn n (a * |firstChaosEmbedding h ω|)) *
          BrownianSignIntegral.signum (firstChaosEmbedding h ω)) • h) := by
  obtain ⟨hf, hg, hfg⟩ := IBMReflectedGaussianSobolev.mollified_pair_reflected_graph n V a
  refine ⟨pullback h hh (hf.toLp _), scalarTensor h (pullback h hh (hg.toLp _)),
    pullback_closed_graph h hh hfg, ?_, ?_⟩
  · have ha := (observation_measurePreserving h hh).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp
    filter_upwards [pullback_ae h hh (hf.toLp _), ha] with ω hp ha
    exact hp.trans ha
  · have ha := (observation_measurePreserving h hh).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp
    filter_upwards [scalarTensor_coeFn h (pullback h hh (hg.toLp _)),
      pullback_ae h hh (hg.toLp _), ha] with ω ht hp ha
    dsimp only [Function.comp_def] at ha
    rw [ht, hp, ha]

theorem reflected_direction_graph (h : CoefficientSpace) (hh : h ≠ 0)
    (n : ℕ) (V : GaussianL2) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun ω => inner ℝ V
        (IBMContinuousScenery.wholeLineScenery (IBMMollifier.kernel n) |firstChaosEmbedding h ω|)) ∧
      G =ᵐ[gaussianProduct] (fun ω => (inner ℝ V
        (IBMClockAverageCandidate.sourceColumn n |firstChaosEmbedding h ω|) *
          BrownianSignIntegral.signum (firstChaosEmbedding h ω)) • h) := by
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  let u : CoefficientSpace := ‖h‖⁻¹ • h
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  obtain ⟨F, G, hfg, hF, hG⟩ := reflected_observation_graph u hu n V ‖h‖
  have hc : firstChaosEmbedding u =ᵐ[gaussianProduct]
      (fun ω => ‖h‖⁻¹ * firstChaosEmbedding h ω) := by
    have he : firstChaosEmbedding u = ‖h‖⁻¹ • firstChaosEmbedding h := map_smul _ _ _
    rw [he]
    filter_upwards [Lp.coeFn_smul ‖h‖⁻¹ (firstChaosEmbedding h)] with ω hω
    exact hω
  have hs (x : ℝ) : BrownianSignIntegral.signum (‖h‖⁻¹ * x) = BrownianSignIntegral.signum x := by
    have hp := inv_pos.mpr hn
    simp [BrownianSignIntegral.signum, mul_pos_iff_of_pos_left hp,
      mul_neg_iff, hp, not_lt.mpr hp.le]
  refine ⟨F, G, hfg, ?_, ?_⟩
  · filter_upwards [hF, hc] with ω hf hc
    have ha : ‖h‖ * |firstChaosEmbedding u ω| = |firstChaosEmbedding h ω| := by
      rw [hc, abs_mul, abs_inv, abs_of_pos hn]
      field_simp
    rw [hf, ha]
  · filter_upwards [hG, hc] with ω hg hc
    have ha : ‖h‖ * |firstChaosEmbedding u ω| = |firstChaosEmbedding h ω| := by
      rw [hc, abs_mul, abs_inv, abs_of_pos hn]
      field_simp
    rw [hg, ha, hc, hs]
    dsimp only [u]
    rw [smul_smul]
    congr 1
    field_simp

theorem reflected_clock_graph (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (V : GaussianL2) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun ω => inner ℝ V
        (IBMContinuousScenery.wholeLineScenery (IBMMollifier.kernel n) |GaussianTimeProcess.process t ω|)) ∧
      G =ᵐ[gaussianProduct] (fun ω => (inner ℝ V
        (IBMClockAverageCandidate.sourceColumn n |GaussianTimeProcess.process t ω|) *
          BrownianSignIntegral.signum (GaussianTimeProcess.process t ω)) •
            IBMClockAverageCandidate.direction t) := by
  have hd : IBMClockAverageCandidate.direction t ≠ 0 := by
    intro hz
    have hs := IBMClockAverageCandidate.direction_norm_sq t
    rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
    have he : (t : ℝ) = 0 := by simpa using hs.symm
    exact (ne_of_gt (show (0 : ℝ) < t from ht)) he
  have he (ω : SampleSpace) : firstChaosEmbedding (IBMClockAverageCandidate.direction t) ω =
      GaussianTimeProcess.process t ω := by
    change firstChaosEmbedding (SeparableHilbertEmbedding.hilbertEmbedding
      GaussianTimeHilbert.TimeHilbert (GaussianTimeHilbert.timeVector (t : ℝ).toNNReal)) ω = _
    rw [Real.toNNReal_coe]
    rfl
  simpa only [he] using
    reflected_direction_graph (IBMClockAverageCandidate.direction t) hd n V

/-- The same graph has representatives evaluated on the actual constructed
continuous Brownian clock, not merely its chosen first-chaos coordinates. -/
theorem reflected_actual_clock_graph (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (V : GaussianL2) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun ω => inner ℝ V
        (IBMContinuousScenery.wholeLineScenery (IBMMollifier.kernel n)
          |IBMConstructedSources.clockPath ω t|)) ∧
      G =ᵐ[gaussianProduct] (fun ω => (inner ℝ V
        (IBMClockAverageCandidate.sourceColumn n |IBMConstructedSources.clockPath ω t|) *
          BrownianSignIntegral.signum (IBMConstructedSources.clockPath ω t)) •
            IBMClockAverageCandidate.direction t) := by
  obtain ⟨F, G, hfg, hF, hG⟩ := reflected_clock_graph t ht n V
  refine ⟨F, G, hfg, ?_, ?_⟩
  · filter_upwards [hF, IBMConstructedSources.clockPath_coordinate_ae t] with ω hf hc
    simpa only [hc] using hf
  · filter_upwards [hG, IBMConstructedSources.clockPath_coordinate_ae t] with ω hg hc
    simpa only [hc] using hg

end OperatorDerivativeRewrite.Foundation.IBMClockObservationGraph
