import Foundation.CubeHaarOperator
import Foundation.CubeChordTransfer

/-! Exact full-L2 five-chord compression of the actual stationary Wilson transfer.
The orthogonal complement is killed; no arbitrary Haar observable is declared reduced. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeChordOperator
open CubeTemporalSlab CubeWilsonSlab CubeSlabGround CubeGroundUnitary CubeHaarOperator
open CubeAxialSlice CubeAxialGauge CubeHaarSplit CubeReducedHaar CubeChordTransfer
attribute [local irreducible] CubeWilsonSlab.kernel boundaryHaar

abbrev ChordL2 := Lp ℝ 2 chordHaar

def embedding : ChordL2 →ₗᵢ[ℝ] HaarL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ reduced reduced_preserving
def lift : ChordL2 →L[ℝ] HaarL2 := embedding.toContinuousLinearMap
def pull : HaarL2 →L[ℝ] ChordL2 := lift.adjoint
def projection : HaarL2 →L[ℝ] HaarL2 := lift.comp pull

theorem lift_coe (f : ChordL2) : lift f =ᵐ[boundaryHaar] (fun U => f (reduced U)) :=
  Lp.coeFn_compMeasurePreserving f reduced_preserving

theorem lift_norm (f : ChordL2) : ‖lift f‖=‖f‖ := embedding.norm_map f

theorem pull_lift (f : ChordL2) : pull (lift f)=f := by
  have h := (ContinuousLinearMap.isometry_iff_adjoint_comp_self lift).mp embedding.isometry
  exact congrArg (fun T : ChordL2 →L[ℝ] ChordL2 => T f) h

theorem pull_contraction (F : HaarL2) : ‖pull F‖ ≤ ‖F‖ := by
  have h : ‖pull‖ ≤ 1 := by
    change ‖lift.adjoint‖ ≤ 1
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact embedding.norm_toContinuousLinearMap_le
  exact (pull.le_opNorm F).trans (by nlinarith [norm_nonneg F])

theorem projection_selfadjoint : projection.adjoint=projection := by
  simp only [projection,pull,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

theorem projection_lift (f : ChordL2) : projection (lift f)=lift f := by
  change lift (pull (lift f))=lift f
  rw [pull_lift]

theorem projection_idempotent : projection.comp projection=projection := by
  apply ContinuousLinearMap.ext
  intro F
  exact projection_lift (pull F)

variable {beta : ℝ} (d : GroundData beta)

private def output (F : HaarL2) (q : Chords) : ℝ := rawKernel beta F (axialState q)/d.value

private theorem output_measurable (F : HaarL2) : Measurable (output d F) :=
  ((raw_measurable F).comp axial_measurable).div_const d.value

private theorem output_memLp (F : HaarL2) : MemLp (output d F) 2 chordHaar := by
  apply MemLp.of_bound (output_measurable d F).aestronglyMeasurable
    ((Real.exp (36*|beta|)*(∫ V,|F V| ∂boundaryHaar))/d.value)
  filter_upwards with q
  rw [Real.norm_eq_abs]
  change |rawKernel beta F (axialState q)/d.value| ≤ _
  rw [abs_div,abs_of_pos d.value_pos]
  exact div_le_div_of_nonneg_right (raw_bound F (axialState q)) d.value_pos.le

private def outputClass (F : HaarL2) : ChordL2 := (output_memLp d F).toLp (output d F)

private theorem raw_reduced (F : HaarL2) (U : State) :
    rawKernel beta F (axialState (reduced U))=rawKernel beta F U := by
  apply integral_congr_ae
  filter_upwards with V
  have h := CubeSlabGauge.kernel_left_invariant beta (rootedGauge U) U V
  rw [reconstruction] at h
  rw [h]

private theorem operator_output (F : HaarL2) : haarOperator d F=lift (outputClass d F) := by
  rw [haarOperator_eq_normalizedRaw]
  apply Lp.ext
  filter_upwards [normalizedRaw_coe d F,lift_coe (outputClass d F),
    reduced_preserving.quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp (output_memLp d F))] with U hA hI hf
  change outputClass d F (reduced U)=output d F (reduced U) at hf
  rw [hA,hI,hf]
  unfold output
  rw [raw_reduced]

/-- Every actual transfer output, for every Haar-L2 input, lies in the reduced subspace. -/
theorem operator_range (F : HaarL2) : ∃ f : ChordL2, haarOperator d F=lift f :=
  ⟨outputClass d F,operator_output d F⟩

theorem projection_after_operator : projection.comp (haarOperator d)=haarOperator d := by
  apply ContinuousLinearMap.ext
  intro F
  obtain ⟨f,hf⟩ := operator_range d F
  change projection (haarOperator d F)=haarOperator d F
  rw [hf,projection_lift]

theorem operator_after_projection : (haarOperator d).comp projection=haarOperator d := by
  have h := congrArg (fun T : HaarL2 →L[ℝ] HaarL2 => T.adjoint) (projection_after_operator d)
  simpa only [ContinuousLinearMap.adjoint_comp,haarOperator_selfadjoint,projection_selfadjoint] using h

def chordOperator : ChordL2 →L[ℝ] ChordL2 := pull.comp ((haarOperator d).comp lift)

/-- Exact factorization of the actual operator on its entire Haar-L2 domain. -/
theorem factorization : haarOperator d=lift.comp ((chordOperator d).comp pull) := by
  apply ContinuousLinearMap.ext
  intro F
  have hA := congrArg (fun T : HaarL2 →L[ℝ] HaarL2 => T F) (operator_after_projection d)
  have hP := congrArg (fun T : HaarL2 →L[ℝ] HaarL2 => T F) (projection_after_operator d)
  change haarOperator d F=projection (haarOperator d (projection F))
  change haarOperator d (projection F)=haarOperator d F at hA
  change projection (haarOperator d F)=haarOperator d F at hP
  rw [hA,hP]

theorem intertwines (f : ChordL2) : lift (chordOperator d f)=haarOperator d (lift f) := by
  have h := congrArg (fun T : HaarL2 →L[ℝ] HaarL2 => T (lift f)) (projection_after_operator d)
  exact h

theorem kills_orthogonal (F : HaarL2) (hF : pull F = 0) : haarOperator d F=0 := by
  rw [factorization]
  simp only [ContinuousLinearMap.comp_apply,hF,map_zero]

theorem chordOperator_selfadjoint : (chordOperator d).adjoint=chordOperator d := by
  simp only [chordOperator,pull,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,haarOperator_selfadjoint,ContinuousLinearMap.comp_assoc]

theorem chordOperator_contraction (f : ChordL2) : ‖chordOperator d f‖ ≤ ‖f‖ := by
  rw [← lift_norm,intertwines]
  exact (haarOperator_contraction d (lift f)).trans_eq (lift_norm f)

def chordGround : ChordL2 := pull (groundVector d)

theorem lift_chordGround : lift (chordGround d)=groundVector d := by
  change projection (groundVector d)=groundVector d
  have h := congrArg (fun T : HaarL2 →L[ℝ] HaarL2 => T (groundVector d))
    (projection_after_operator d)
  simpa only [ContinuousLinearMap.comp_apply,groundVector_fixed] using h

theorem chordGround_norm : ‖chordGround d‖=1 := by
  rw [← lift_norm,lift_chordGround,groundVector_norm]

theorem chordGround_fixed : chordOperator d (chordGround d)=chordGround d := by
  apply embedding.injective
  change lift (chordOperator d (chordGround d))=lift (chordGround d)
  rw [intertwines,lift_chordGround,groundVector_fixed]

theorem chordOperator_norm : ‖chordOperator d‖=1 := by
  apply le_antisymm
  · apply (chordOperator d).opNorm_le_bound (by norm_num : (0:ℝ)≤1)
    intro f
    simpa only [one_mul] using chordOperator_contraction d f
  · have h := (chordOperator d).le_opNorm (chordGround d)
    rw [chordGround_fixed,chordGround_norm,mul_one] at h
    exact h

theorem pull_zero_iff_orthogonal (F : HaarL2) :
    pull F=0 ↔ ∀ f : ChordL2, inner ℝ F (lift f)=0 := by
  constructor
  · intro h f
    rw [← ContinuousLinearMap.adjoint_inner_left]
    change inner ℝ (pull F) f=0
    rw [h,inner_zero_left]
  · intro h
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    change inner ℝ (lift.adjoint F) (pull F)=0
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact h (pull F)

/-- The original physical Haar ground complement is exactly preserved by the embedding. -/
theorem ground_complement_iff (f : ChordL2) :
    inner ℝ (lift f) (groundVector d)=0 ↔ inner ℝ f (chordGround d)=0 := by
  rw [← lift_chordGround]
  change inner ℝ (embedding f) (embedding (chordGround d))=0 ↔ _
  rw [embedding.inner_map_map]

theorem eigen_iff (f : ChordL2) (a : ℝ) :
    chordOperator d f=a • f ↔ haarOperator d (lift f)=a • lift f := by
  constructor
  · intro h
    rw [← intertwines,h,map_smul]
  · intro h
    apply embedding.injective
    change lift (chordOperator d f)=lift (a • f)
    rw [intertwines,h,map_smul]

def rawChord (f : ChordL2) (q : Chords) : ℝ :=
  ∫ r,kernel beta (axialState q) (axialState r)*f r ∂chordHaar

theorem raw_lift (f : ChordL2) (q : Chords) :
    rawKernel beta (lift f) (axialState q)=rawChord (beta := beta) f q := by
  unfold rawKernel rawChord
  calc
    _ = ∫ V,kernel beta (axialState q) (axialState (reduced V))*f (reduced V) ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards [lift_coe f] with V hV
      rw [hV]
      have h := CubeSlabGauge.kernel_right_invariant beta (rootedGauge V) (axialState q) V
      rw [reconstruction] at h
      rw [h]
    _ = _ := integral_reduced _
      ((((kernel_joint_measurable beta).comp
        (measurable_const.prodMk axial_measurable))).mul (Lp.stronglyMeasurable f).measurable)

theorem rawChord_measurable (f : ChordL2) : Measurable (rawChord (beta := beta) f) := by
  have h : (fun q : Chords => rawChord (beta := beta) f q)=
      (fun q => rawKernel beta (lift f) (axialState q)) := funext (fun q => (raw_lift f q).symm)
  change Measurable (fun q : Chords => rawChord (beta := beta) f q)
  rw [h]
  exact (raw_measurable (lift f)).comp axial_measurable

theorem rawChord_integrable (f : ChordL2) (q : Chords) :
    Integrable (fun r => kernel beta (axialState q) (axialState r)*f r) chordHaar := by
  have hi : Integrable (fun r => |f r|) chordHaar := by
    simpa only [Real.norm_eq_abs] using (Lp.memLp f).norm.integrable (by norm_num : (1:ENNReal)≤2)
  apply (hi.const_mul (Real.exp (36*|beta|))).mono'
    (((kernel_joint_measurable beta).comp
      (measurable_const.prodMk axial_measurable)).mul
        (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable
  filter_upwards with r
  change ‖kernel beta (axialState q) (axialState r)*f r‖ ≤
    Real.exp (36*|beta|)*|f r|
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (kernel_positive beta _ _)]
  exact mul_le_mul_of_nonneg_right (kernel_bounds beta _ _).2 (abs_nonneg _)

theorem rawChord_memLp (f : ChordL2) : MemLp (rawChord (beta := beta) f) 2 chordHaar := by
  apply MemLp.of_bound (rawChord_measurable f).aestronglyMeasurable
    (Real.exp (36*|beta|)*(∫ V,|lift f V| ∂boundaryHaar))
  filter_upwards with q
  rw [Real.norm_eq_abs,← raw_lift]
  exact raw_bound (lift f) (axialState q)

/-- Literal normalized chord-kernel identity on the entire chord L2 quotient space. -/
theorem chordOperator_coe (f : ChordL2) : chordOperator d f =ᵐ[chordHaar]
    (fun q => rawChord (beta := beta) f q/d.value) := by
  have h : chordOperator d f=outputClass d (lift f) := by
    change pull (haarOperator d (lift f))=outputClass d (lift f)
    rw [operator_output,pull_lift]
  rw [h]
  filter_upwards [MemLp.coeFn_toLp (output_memLp d (lift f))] with q hq
  change outputClass d (lift f) q=output d (lift f) q at hq
  rw [hq]
  unfold output
  rw [raw_lift]

theorem chord_pairing_integrable (f g : ChordL2) :
    Integrable (fun q => g q*rawChord (beta := beta) f q) chordHaar :=
  (Lp.memLp g).integrable_mul (rawChord_memLp f)

theorem chordOperator_kernel_pairing (f g : ChordL2) :
    inner ℝ (chordOperator d f) g=
      (∫ q,g q*(∫ r,kernel beta (axialState q) (axialState r)*f r ∂chordHaar) ∂chordHaar)/d.value := by
  rw [L2.inner_def,← integral_div]
  apply integral_congr_ae
  filter_upwards [chordOperator_coe d f] with q hq
  rw [hq,Real.inner_apply]
  change rawChord f q/d.value*g q=g q*rawChord f q/d.value
  ring

end OperatorDerivativeRewrite.Foundation.CubeChordOperator
