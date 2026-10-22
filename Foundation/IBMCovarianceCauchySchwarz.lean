import Foundation.IBMFiniteSignedCovarianceIntegral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Algebra.QuadraticDiscriminant

/-! Full predictable covariance bilinearity, variation Cauchy–Schwarz, and separate energy-null invariance. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCovarianceCauchySchwarz
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableRingContent
open IBMJointPredictableEnergyMeasure IBMPredictableCovarianceMeasure IBMCovarianceVariationControl
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
local instance (F : JointL2) : IsFiniteMeasure (predictableMeasure F) := finite_measure F
local instance (F G : JointL2) : IsFiniteMeasure (covariance F G).variation := finite_variation F G

def exhaustion (n : ℕ) : Set Space := origin univ ∪ rect 0 n univ

theorem origin_measurable {A : Set IBMSourceLaws.JointSample}
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration 0] A) :
    MeasurableSet (origin A) := by
  change MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration.predictable] (origin A)
  rw [← predictable_generation]
  exact MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨A, hA, rfl⟩)

theorem exhaustion_measurable (n : ℕ) : MeasurableSet (exhaustion n) := by
  exact (origin_measurable MeasurableSet.univ).union (rect_predictable 0 n univ MeasurableSet.univ)

theorem exhaustion_monotone : Monotone exhaustion := by
  intro i j hij p hp
  rcases hp with hp | hp
  · exact Or.inl hp
  · exact Or.inr ⟨⟨hp.1.1, hp.1.2.trans (by exact_mod_cast hij)⟩, hp.2⟩

theorem exhaustion_union : (⋃ n, exhaustion n) = univ := by
  apply eq_univ_of_forall
  rintro ⟨r, ω⟩
  by_cases hz : r = 0
  · exact mem_iUnion.mpr ⟨0, Or.inl ⟨hz, mem_univ ω⟩⟩
  · obtain ⟨n, hn⟩ := exists_nat_ge r
    exact mem_iUnion.mpr ⟨n, Or.inr ⟨⟨pos_iff_ne_zero.mpr hz, hn⟩, mem_univ ω⟩⟩

theorem signed_ext (μ ν : SignedMeasure Space)
    (h : ∀ E ∈ generators, μ E = ν E) : μ = ν := by
  apply VectorMeasure.ext_of_generateFrom generators h predictable_generation.symm
    (fun E hE H hH _ => generators_inter hE hH)
  have hn : ∀ n, μ (exhaustion n) = ν (exhaustion n) := by
    intro n
    have hR : rect 0 n univ ∈ elementaryRing :=
      subset_supClosure (rect_mem 0 n univ MeasurableSet.univ)
    have hO := origin_measurable MeasurableSet.univ
    simp only [exhaustion, VectorMeasure.of_union ((ring_disjoint_origin hR univ).symm)
      hO (elementary_predictable hR)]
    rw [h (origin univ) (Or.inr ⟨univ, MeasurableSet.univ, rfl⟩), h _ (Or.inl hR)]
  have hm := μ.tendsto_vectorMeasure_iUnion_atTop_nat exhaustion_monotone exhaustion_measurable
  have hv := ν.tendsto_vectorMeasure_iUnion_atTop_nat exhaustion_monotone exhaustion_measurable
  rw [exhaustion_union] at hm hv
  exact tendsto_nhds_unique hm (by simpa only [hn] using hv)

theorem covariance_origin (F G : JointL2) {A : Set IBMSourceLaws.JointSample}
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration 0] A) :
    covariance F G (origin A) = 0 := by
  have hO := origin_measurable hA
  rw [covariance_apply F G hO, predictableMeasure_origin (F+G) A hA,
    predictableMeasure_origin (F-G) A hA]
  norm_num

theorem covariance_add_left (F G H : JointL2) :
    covariance (F+G) H = covariance F H + covariance G H := by
  apply signed_ext
  intro E hE
  rcases hE with hE | ⟨A, hA, rfl⟩
  · simp only [add_apply, covariance_ring _ _ hE, ring_terminal_add, inner_add_left]
  · change covariance (F+G) H (origin A) = (covariance F H + covariance G H) (origin A)
    simp only [add_apply, covariance_origin _ _ hA, zero_add]

theorem covariance_smul_left (c : ℝ) (F G : JointL2) :
    covariance (c • F) G = c • covariance F G := by
  apply signed_ext
  intro E hE
  rcases hE with hE | ⟨A, hA, rfl⟩
  · have he : ringIntegral (c • F) E = c • ringIntegral F E := by
      rw [← ringOperator_eq, (ringOperator E).map_smul, ringOperator_eq]
    simp only [smul_apply, covariance_ring _ _ hE, he, real_inner_smul_left, smul_eq_mul]
  · change covariance (c • F) G (origin A) = (c • covariance F G) (origin A)
    simp only [smul_apply, covariance_origin _ _ hA, smul_zero]

theorem covariance_symm (F G : JointL2) : covariance F G = covariance G F := by
  apply signed_ext
  intro E hE
  rcases hE with hE | ⟨A, hA, rfl⟩
  · rw [covariance_ring _ _ hE, covariance_ring _ _ hE, real_inner_comm]
  · change covariance F G (origin A) = covariance G F (origin A)
    rw [covariance_origin _ _ hA, covariance_origin _ _ hA]

theorem covariance_add_right (F G H : JointL2) :
    covariance F (G+H) = covariance F G + covariance F H := by
  rw [covariance_symm F (G+H), covariance_add_left, covariance_symm G F, covariance_symm H F]

theorem covariance_smul_right (c : ℝ) (F G : JointL2) :
    covariance F (c • G) = c • covariance F G := by
  rw [covariance_symm F (c • G), covariance_smul_left, covariance_symm G F]

theorem covariance_quadratic (F G : JointL2) (c : ℝ) {E : Set Space} (hE : MeasurableSet E) :
    (predictableMeasure (F+c•G) E).toReal = (predictableMeasure F E).toReal +
      2*c*covariance F G E + c^2*(predictableMeasure G E).toReal := by
  have he := congrArg (fun ν : SignedMeasure Space => ν E) (covariance_diagonal (F+c•G))
  rw [covariance_add_left, covariance_add_right, covariance_add_right,
    covariance_smul_left, covariance_smul_right, covariance_smul_right, covariance_smul_left,
    covariance_symm G F, covariance_diagonal F, covariance_diagonal G] at he
  simp only [add_apply, smul_apply, smul_eq_mul, Measure.toSignedMeasure_apply_measurable hE,
    measureReal_def] at he
  nlinarith [he]

theorem covariance_sq_bound (F G : JointL2) {E : Set Space} (hE : MeasurableSet E) :
    (covariance F G E)^2 ≤ (predictableMeasure F E).toReal * (predictableMeasure G E).toReal := by
  have hd := discrim_le_zero (a := (predictableMeasure G E).toReal)
    (b := 2*covariance F G E) (c := (predictableMeasure F E).toReal) (fun c => by
      have he := covariance_quadratic F G c hE
      nlinarith [ENNReal.toReal_nonneg (a := predictableMeasure (F+c•G) E)])
  dsimp [discrim] at hd
  nlinarith

theorem variation_young (F G : JointL2) (c : ℝ) {E : Set Space} (hE : MeasurableSet E) :
    |c| * (covariance F G).variation.real E ≤
      (1/2 : ℝ) * ((predictableMeasure F).real E + c^2*(predictableMeasure G).real E) := by
  have hb := (Measure.le_iff.mp (variation_bound F (c • G))) E hE
  rw [covariance_smul_right, VectorMeasure.variation_smul, homogeneity] at hb
  simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul] at hb
  have ht := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_smul, NNReal.smul_def, coe_nnnorm, Real.norm_eq_abs, ENNReal.toReal_mul,
    ENNReal.toReal_add (measure_ne_top _ _) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg c)] at ht
  norm_num at ht
  exact ht

theorem variation_sq_bound (F G : JointL2) {E : Set Space} (hE : MeasurableSet E) :
    ((covariance F G).variation.real E)^2 ≤
      (predictableMeasure F).real E * (predictableMeasure G).real E := by
  have hd := discrim_le_zero (a := (predictableMeasure G).real E)
    (b := -2*(covariance F G).variation.real E) (c := (predictableMeasure F).real E) (fun c => by
      have hy := variation_young F G c hE
      have hv : c*(covariance F G).variation.real E ≤ |c| * (covariance F G).variation.real E :=
        mul_le_mul_of_nonneg_right (le_abs_self c) measureReal_nonneg
      nlinarith)
  dsimp [discrim] at hd
  nlinarith

theorem variation_ac_left (F G : JointL2) :
    (covariance F G).variation ≪ predictableMeasure F := by
  apply Measure.AbsolutelyContinuous.mk
  intro E hE hz
  have hb := variation_sq_bound F G hE
  have hf : (predictableMeasure F).real E = 0 := by simp [measureReal_def, hz]
  rw [hf, zero_mul] at hb
  apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
  nlinarith [measureReal_nonneg (μ := (covariance F G).variation) (s := E)]

theorem variation_ac_right (F G : JointL2) :
    (covariance F G).variation ≪ predictableMeasure G := by
  rw [covariance_symm F G]
  exact variation_ac_left G F

theorem product_ae_congr (F G : JointL2) {H H' K K' : Space → ℝ}
    (hH : H =ᵐ[predictableMeasure F] H') (hK : K =ᵐ[predictableMeasure G] K') :
    (fun p => H p * K p) =ᵐ[(covariance F G).variation] (fun p => H' p * K' p) := by
  filter_upwards [(variation_ac_left F G).ae_le hH, (variation_ac_right F G).ae_le hK] with p hp hq
  rw [hp, hq]

theorem signed_integral_ae_congr (F G : JointL2) {H H' K K' : Space → ℝ}
    (hH : H =ᵐ[predictableMeasure F] H') (hK : K =ᵐ[predictableMeasure G] K') :
    (∫ᵛ p, H p * K p ∂<•covariance F G) = (∫ᵛ p, H' p * K' p ∂<•covariance F G) :=
  VectorMeasure.integral_congr_ae (product_ae_congr F G hH hK)

end OperatorDerivativeRewrite.Foundation.IBMCovarianceCauchySchwarz
