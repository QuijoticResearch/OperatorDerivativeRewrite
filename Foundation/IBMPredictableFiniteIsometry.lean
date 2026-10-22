import Foundation.IBMJointPredictableEnergyMeasure

/-! The actual finite stochastic integral has the genuine predictable L2 energy. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableFiniteIsometry
open IBMPredictableRectangles IBMPredictableFiniteIntegral IBMPredictableRingContent
open IBMJointPredictableEnergyMeasure IBMTimeAveragedObservable
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable

theorem disjoint_ring_orthogonal (F : JointL2) {E H : Set Space}
    (hE : E ∈ elementaryRing) (hH : H ∈ elementaryRing) (hd : Disjoint E H) :
    inner ℝ (ringIntegral F E) (ringIntegral F H) = 0 := by
  classical
  obtain ⟨P, hP⟩ := rectangle_semiring.mem_supClosure_iff.mp hE
  obtain ⟨Q, hQ⟩ := rectangle_semiring.mem_supClosure_iff.mp hH
  have hp : ⋃₀ (P.parts : Set (Set Space)) = E := by
    simpa only [Finset.sup_id_set_eq_sUnion] using P.sup_parts
  have hq : ⋃₀ (Q.parts : Set (Set Space)) = H := by
    simpa only [Finset.sup_id_set_eq_sUnion] using Q.sup_parts
  rw [← hp, ringIntegral_sUnion F P.parts (fun R hR => subset_supClosure (hP hR))
    P.disjoint (hp.symm ▸ hE), ← hq,
    ringIntegral_sUnion F Q.parts (fun R hR => subset_supClosure (hQ hR))
      Q.disjoint (hq.symm ▸ hH), sum_inner]
  apply Finset.sum_eq_zero
  intro R hR
  rw [inner_sum]
  exact Finset.sum_eq_zero fun S hS =>
    disjoint_rectangle_orthogonal F (hP hR) (hQ hS) (hd.mono (P.le hR) (Q.le hS))

theorem ringIntegral_disjoint_union (F : JointL2) {E H : Set Space}
    (hE : E ∈ elementaryRing) (hH : H ∈ elementaryRing) (hd : Disjoint E H) :
    ringIntegral F (E ∪ H) = ringIntegral F E + ringIntegral F H := by
  have hi : indicatorClass (E ∪ H) = indicatorClass E + indicatorClass H := by
    apply Subtype.ext
    change (indicatorClass (E ∪ H) : Space → ℝ) =
      (indicatorClass E : Space → ℝ) + (indicatorClass H : Space → ℝ)
    rw [indicatorClass_value (elementary_isSetRing.union_mem hE hH),
      indicatorClass_value hE, indicatorClass_value hH, indicator_union_of_disjoint hd]
    rfl
  exact (congrArg (integral F) hi).trans (map_add _ _ _)

theorem ring_cross_energy (F : JointL2) {E H : Set Space}
    (hE : E ∈ elementaryRing) (hH : H ∈ elementaryRing) :
    inner ℝ (ringIntegral F E) (ringIntegral F H) = (predictableMeasure F (E ∩ H)).toReal := by
  have hI := elementary_isSetRing.inter_mem hE hH
  have hD := elementary_isSetRing.sdiff_mem hE hH
  have hB := elementary_isSetRing.sdiff_mem hH hE
  have he : ringIntegral F E = ringIntegral F (E \ H) + ringIntegral F (E ∩ H) := by
    rw [← ringIntegral_disjoint_union F hD hI disjoint_sdiff_inter, sdiff_union_inter]
  have hh : ringIntegral F H = ringIntegral F (H \ E) + ringIntegral F (E ∩ H) := by
    have hu : (H \ E) ∪ (E ∩ H) = H := by ext p; simp only [mem_union, mem_sdiff, mem_inter_iff]; tauto
    have hd : Disjoint (H \ E) (E ∩ H) := disjoint_left.mpr fun _ h h' => h.2 h'.1
    rw [← ringIntegral_disjoint_union F hB hI hd, hu]
  calc
    inner ℝ (ringIntegral F E) (ringIntegral F H) = ‖ringIntegral F (E ∩ H)‖ ^ 2 := by
      nth_rw 1 [he]
      rw [inner_add_left, disjoint_ring_orthogonal F hD hH disjoint_sdiff_left, zero_add, hh,
        inner_add_right, disjoint_ring_orthogonal F hI hB
          (disjoint_left.mpr fun _ h h' => h'.2 h.1), zero_add, real_inner_self_eq_norm_sq]
    _ = _ := by rw [predictableMeasure_generator F (Or.inl hI), content_energy F hI,
      ENNReal.toReal_ofReal (sq_nonneg _)]

theorem basis_memLp (F : JointL2) (d : Index) :
    MemLp (basisProcess d) 2 (predictableMeasure F) := by
  letI := finite_measure F
  exact (memLp_const (1 : ℝ)).indicator (rect_predictable _ _ _ (event_measurable d))

theorem process_memLp (F : JointL2) (l : Index →₀ ℝ) :
    MemLp (processLinear l) 2 (predictableMeasure F) := by
  have he : processLinear l = fun p => ∑ d ∈ l.support, l d * basisProcess d p :=
    funext (processLinear_apply l)
  rw [he]
  exact memLp_finsetSum _ fun d _ => (basis_memLp F d).const_mul (l d)

theorem basis_cross_integral (F : JointL2) (d e : Index) :
    inner ℝ (basisIntegral F d) (basisIntegral F e) =
      ∫ p, basisProcess d p * basisProcess e p ∂predictableMeasure F := by
  have hd := subset_supClosure (rect_mem (left d) (right d) (event d) (event_measurable d))
  have he := subset_supClosure (rect_mem (left e) (right e) (event e) (event_measurable e))
  have h := ring_cross_energy F hd he
  rw [ringIntegral_rect F _ _ _ (ordered d) (event_measurable d),
    ringIntegral_rect F _ _ _ (ordered e) (event_measurable e)] at h
  change inner ℝ (basisIntegral F d) (basisIntegral F e) = _ at h
  rw [h]
  have hp : (fun p => basisProcess d p * basisProcess e p) =
      (rect (left d) (right d) (event d) ∩ rect (left e) (right e) (event e)).indicator
        (fun _ => (1 : ℝ)) := by
    funext p
    by_cases hpd : p ∈ rect (left d) (right d) (event d) <;>
      by_cases hpe : p ∈ rect (left e) (right e) (event e) <;> simp [basisProcess, hpd, hpe]
  rw [hp]
  simpa only [smul_eq_mul, mul_one, measureReal_def] using
    (integral_indicator_const (μ := predictableMeasure F) (1 : ℝ)
      ((elementary_predictable hd).inter (elementary_predictable he))).symm

theorem finite_cross_integral (F : JointL2) (l k : Index →₀ ℝ) :
    inner ℝ (integralLinear F l) (integralLinear F k) =
      ∫ p, processLinear l p * processLinear k p ∂predictableMeasure F := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add l m hl hm =>
      simp only [map_add, Pi.add_apply, inner_add_left, add_mul]
      have h1 : Integrable (fun p => processLinear l p * processLinear k p)
          (predictableMeasure F) := (process_memLp F l).integrable_mul (process_memLp F k)
      have h2 : Integrable (fun p => processLinear m p * processLinear k p)
          (predictableMeasure F) := (process_memLp F m).integrable_mul (process_memLp F k)
      rw [integral_add h1 h2, hl, hm]
  | single d a =>
      induction k using Finsupp.induction_linear with
      | zero => simp
      | add k m hk hm =>
          simp only [map_add, Pi.add_apply, inner_add_right, mul_add]
          have h1 : Integrable (fun p => processLinear (Finsupp.single d a) p * processLinear k p)
              (predictableMeasure F) :=
            (process_memLp F (Finsupp.single d a)).integrable_mul (process_memLp F k)
          have h2 : Integrable (fun p => processLinear (Finsupp.single d a) p * processLinear m p)
              (predictableMeasure F) :=
            (process_memLp F (Finsupp.single d a)).integrable_mul (process_memLp F m)
          rw [integral_add h1 h2, hk, hm]
      | single e b =>
          simp only [integralLinear, processLinear, Finsupp.linearCombination_single,
            real_inner_smul_left, real_inner_smul_right, Pi.smul_apply, smul_eq_mul]
          simp_rw [mul_mul_mul_comm a _ b _, integral_const_mul, basis_cross_integral]
          ring

theorem integral_energy (F : JointL2) (H : processSpace) :
    ‖integral F H‖ ^ 2 = ∫ p, (H : Space → ℝ) p ^ 2 ∂predictableMeasure F := by
  obtain ⟨l, hl⟩ := H.property
  have he : H = ⟨processLinear l, ⟨l, rfl⟩⟩ := Subtype.ext hl.symm
  rw [he, integral_process, ← real_inner_self_eq_norm_sq, finite_cross_integral]
  simp only [pow_two]

end OperatorDerivativeRewrite.Foundation.IBMPredictableFiniteIsometry
