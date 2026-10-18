import Foundation.IBMMixedCubicStein
import Foundation.IBMSecondChaosTesting

/-! Full second-source projection of the genuine shifted Schwartz curvature.
All products are realized in native Gaussian L2 before projection. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzSecondProjection
open InfiniteGaussian GaussianTimeSpaceHermite GaussianNumberSectors FractionalControlledEstimate
open IBMFirstChaosMixedStein IBMCorrectionStein IBMShiftedJetMoments
open IBMMixedFourthStein IBMMixedCubicStein IBMSecondChaosTesting IBMQuarticSecondChaos

theorem weighted_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u : CoefficientSpace) (j : ℕ) (f : GaussianL2) :
    MemLp (fun ω => shiftedJet g a j (firstChaosEmbedding u ω)*f ω) 2 gaussianProduct := by
  apply (Lp.memLp f).of_le_mul (c := SchwartzMap.seminorm ℝ 0 0 (jet g j))
    (((shiftedJet_smooth g a j).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (firstChaosEmbedding u))).mul (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun ω => by
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (shiftedJet_bound g a j _) (norm_nonneg _)

def weightedClass (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u : CoefficientSpace) (j : ℕ) (f : GaussianL2) : GaussianL2 :=
  (weighted_memLp g a u j f).toLp _

theorem weightedClass_coeFn (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u : CoefficientSpace) (j : ℕ) (f : GaussianL2) :
    weightedClass g a u j f =ᵐ[gaussianProduct]
      fun ω => shiftedJet g a j (firstChaosEmbedding u ω)*f ω := MemLp.coeFn_toLp _

def correctionClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v w : CoefficientSpace) : GaussianL2 :=
  weightedClass g a u 2 (square v) + weightedClass g a u 1 (firstChaosEmbedding w)

theorem correctionClass_coeFn (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v w : CoefficientSpace) :
    correctionClass g a u v w =ᵐ[gaussianProduct] fun ω =>
      shiftedJet g a 2 (firstChaosEmbedding u ω)*(firstChaosEmbedding v ω)^2 +
      shiftedJet g a 1 (firstChaosEmbedding u ω)*firstChaosEmbedding w ω := by
  filter_upwards [Lp.coeFn_add (weightedClass g a u 2 (square v))
    (weightedClass g a u 1 (firstChaosEmbedding w)),
    weightedClass_coeFn g a u 2 (square v), weightedClass_coeFn g a u 1 (firstChaosEmbedding w),
    square_coeFn v] with ω ha h2 h1 hv
  rw [correctionClass, ha, Pi.add_apply, h2, h1, hv]

theorem weighted_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u : CoefficientSpace) (j : ℕ) (f : GaussianL2) (k : CoefficientSpace) :
    inner ℝ (weightedClass g a u j f) (wick k 2 : GaussianL2) =
      ∫ ω, f ω*((firstChaosEmbedding k ω)^2-‖k‖^2)*
        shiftedJet g a j (firstChaosEmbedding u ω) ∂gaussianProduct := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [weightedClass_coeFn g a u j f, wickTwo_coeFn k] with ω hf hk
  rw [hf, hk]
  simp only [Real.inner_apply]
  ring

theorem correction_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v w k : CoefficientSpace) :
    inner ℝ (correctionClass g a u v w) (wick k 2 : GaussianL2) =
      2*((inner ℝ v k)^2+inner ℝ w k*inner ℝ u k)*M g a u 2 0 +
      ((‖v‖^2+inner ℝ u w)*(inner ℝ u k)^2+
        4*inner ℝ v k*inner ℝ u v*inner ℝ u k)*M g a u 4 0 +
      (inner ℝ u v)^2*(inner ℝ u k)^2*M g a u 6 0 := by
  rw [correctionClass, inner_add_left, weighted_pairing, weighted_pairing]
  have he : (∫ ω, square v ω*((firstChaosEmbedding k ω)^2-‖k‖^2)*
      shiftedJet g a 2 (firstChaosEmbedding u ω) ∂gaussianProduct) =
      ∫ ω, (firstChaosEmbedding v ω)^2*((firstChaosEmbedding k ω)^2-‖k‖^2)*
        shiftedJet g a 2 (firstChaosEmbedding u ω) ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [square_coeFn v] with ω hv
    rw [hv]
  rw [he, centered_square_test, centered_linear_test]
  norm_num
  ring

def secondCandidate (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v w : CoefficientSpace) : GaussianL2 :=
  (((‖v‖^2+inner ℝ u w)*M g a u 4 0+(inner ℝ u v)^2*M g a u 6 0)/2) •
      (wick u 2 : GaussianL2) +
    (2*inner ℝ u v*M g a u 4 0) • cross u v +
    M g a u 2 0 • ((wick v 2 : GaussianL2)+cross u w)

theorem secondCandidate_mem (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v w : CoefficientSpace) :
    secondCandidate g a u v w ∈ sector 2 := by
  exact (sector 2).add_mem ((sector 2).add_mem
    ((sector 2).smul_mem _ (IBMCubicFirstChaos.wick_mem_sector u 2))
    ((sector 2).smul_mem _ (cross_mem_sector u v)))
    ((sector 2).smul_mem _ ((sector 2).add_mem
      (IBMCubicFirstChaos.wick_mem_sector v 2) (cross_mem_sector u w)))

theorem secondCandidate_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v w k : CoefficientSpace) :
    inner ℝ (secondCandidate g a u v w) (wick k 2 : GaussianL2) =
      inner ℝ (correctionClass g a u v w) (wick k 2 : GaussianL2) := by
  rw [correction_pairing]
  simp only [secondCandidate, inner_add_left, real_inner_smul_left,
    cross_wick_pairing, wick_inner]
  norm_num
  ring

/-- The completed native projection, not just a finite polynomial test. -/
theorem correction_projection_two (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v w : CoefficientSpace) :
    projection 2 (correctionClass g a u v w) = secondCandidate g a u v w := by
  apply projection_eq_of_wick_tests _ _ (secondCandidate_mem g a u v w)
  intro k
  exact (secondCandidate_pairing g a u v w k).symm

/-- In particular j=1 gives the second source sector of the actual
origin term g'(a+U)V. -/
theorem weighted_linear_projection (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u w : CoefficientSpace) (j : ℕ) :
    projection 2 (weightedClass g a u j (firstChaosEmbedding w)) =
      M g a u (j+1) 0 • cross u w +
        (inner ℝ u w*M g a u (j+3) 0/2) • (wick u 2 : GaussianL2) := by
  apply projection_eq_of_wick_tests _ _ ((sector 2).add_mem
    ((sector 2).smul_mem _ (cross_mem_sector u w))
    ((sector 2).smul_mem _ (IBMCubicFirstChaos.wick_mem_sector u 2)))
  intro k
  rw [weighted_pairing, centered_linear_test]
  simp only [inner_add_left, real_inner_smul_left, cross_wick_pairing, wick_inner]
  norm_num
  ring

def mollifiedClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : GaussianL2 :=
  correctionClass g a (IBMGaussianSteinMoments.tripleCoefficient n r 0)
    (IBMGaussianSteinMoments.tripleCoefficient n r 1)
    (IBMGaussianSteinMoments.tripleCoefficient n r 2)

theorem mollifiedClass_coeFn (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    mollifiedClass g a n r =ᵐ[gaussianProduct] fun ω =>
      shiftedJet g a 2 (IBMDyadicExtension.field n 0 ω r)*(IBMDyadicExtension.field n 1 ω r)^2 +
      shiftedJet g a 1 (IBMDyadicExtension.field n 0 ω r)*IBMDyadicExtension.field n 2 ω r := by
  filter_upwards [correctionClass_coeFn g a (IBMGaussianSteinMoments.tripleCoefficient n r 0)
      (IBMGaussianSteinMoments.tripleCoefficient n r 1)
      (IBMGaussianSteinMoments.tripleCoefficient n r 2),
    IBMDyadicExtension.field_coordinate_ae n 0 r,
    IBMDyadicExtension.field_coordinate_ae n 1 r,
    IBMDyadicExtension.field_coordinate_ae n 2 r] with ω hc h0 h1 h2
  rw [IBMGaussianSteinMoments.gaussianTriple_eq_firstChaos] at h0 h1 h2
  exact hc.trans (by rw [h0, h1, h2])

theorem mollified_projection_two (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    projection 2 (mollifiedClass g a n r) =
      secondCandidate g a (IBMGaussianSteinMoments.tripleCoefficient n r 0)
        (IBMGaussianSteinMoments.tripleCoefficient n r 1)
        (IBMGaussianSteinMoments.tripleCoefficient n r 2) := correction_projection_two _ _ _ _ _

end OperatorDerivativeRewrite.Foundation.IBMSchwartzSecondProjection
