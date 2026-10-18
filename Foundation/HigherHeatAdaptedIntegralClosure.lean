import Foundation.HigherHeatCompletedStepAgreement

/-! The actual L1 closure of polynomial adapted fields and its unique bounded signed integral.
Uniqueness concerns the integral extension, not its integrands. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAdaptedIntegralClosure
open MeasureTheory Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement HigherHeatAdaptedStepDuality
open HigherHeatCompletedStepAgreement HigherHeatCompletedPairing HigherHeatPairedDualCausality
open HigherHeatTimeDerivative

def generators (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Set (Field timeMeasure) :=
  {A | ∃ (n : ℕ) (F : Fin (size n) → Test n), Adapted F ∧ A = adaptedField n m hm T hT F}

def stepSpan (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Submodule ℝ (Field timeMeasure) := Submodule.span ℝ (generators m hm T hT)

def space (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Submodule ℝ (Field timeMeasure) := (stepSpan m hm T hT).topologicalClosure

instance space_complete (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    CompleteSpace (space m hm T hT) :=
  Submodule.topologicalClosure.completeSpace _

def native (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (F : Fin (size n) → Test n) (hF : Adapted F) : space m hm T hT :=
  ⟨adaptedField n m hm T hT F,
    (stepSpan m hm T hT).le_topologicalClosure (Submodule.subset_span ⟨n, F, hF, rfl⟩)⟩

def integral (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    space m hm T hT →L[ℝ] Dual := (firstChannel m T).comp (space m hm T hT).subtypeL

theorem integral_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : space m hm T hT) : ‖integral m hm T hT A‖ ≤ ((2*m:ℕ):ℝ)*(T:ℝ)*‖A‖ :=
  firstChannel_bound m T A.val

theorem integral_native (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (F : Fin (size n) → Test n) (hF : Adapted F) :
    integral m hm T hT (native m hm T hT n F hF) =
      pairing m hm T hT (core (cylinderOf n (stepPolynomial F))) :=
  adapted_sum_dual n m hm T hT F hF

theorem derivative_integral_duality (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : space m hm T hT) (G : Domain) :
    integral m hm T hT A G = coefficient m T *
      ∫ t : ℝ, A.val t (((atTime t)^(2*m-1)) G) ∂timeMeasure :=
  firstChannel_apply m T A.val G

theorem duality_integrable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : space m hm T hT) (G : Domain) :
    Integrable (fun t : ℝ => A.val t (((atTime t)^(2*m-1)) G)) timeMeasure :=
  evaluation_integrable timeMeasure (2*m-1) A.val G

theorem integral_eq_iff_kernel (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A B : space m hm T hT) :
    integral m hm T hT A = integral m hm T hT B ↔
      A-B ∈ (integral m hm T hT).ker := by
  change _ ↔ integral m hm T hT (A-B) = 0
  rw [(integral m hm T hT).map_sub A B]
  exact (sub_eq_zero (a := integral m hm T hT A) (b := integral m hm T hT B)).symm

def spanInclusion (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    stepSpan m hm T hT →L[ℝ] space m hm T hT :=
  (stepSpan m hm T hT).subtypeL.codRestrict _
    (fun A => (stepSpan m hm T hT).le_topologicalClosure A.property)

theorem span_dense (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    DenseRange (spanInclusion m hm T hT) := by
  intro A
  have hA : A.val ∈ closure (stepSpan m hm T hT : Set (Field timeMeasure)) := A.property
  obtain ⟨g, hg, hlim⟩ := mem_closure_iff_seq_limit.mp hA
  have hlim' : Tendsto (fun k => spanInclusion m hm T hT ⟨g k, hg k⟩) atTop (𝓝 A) :=
    tendsto_subtype_rng.mpr hlim
  apply isClosed_closure.mem_of_tendsto hlim'
  exact Eventually.of_forall (fun k => subset_closure ⟨⟨g k, hg k⟩, rfl⟩)

theorem integral_unique (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (L : space m hm T hT →L[ℝ] Dual)
    (hL : ∀ (n : ℕ) (F : Fin (size n) → Test n) (hF : Adapted F),
      L (native m hm T hT n F hF) =
        pairing m hm T hT (core (cylinderOf n (stepPolynomial F)))) :
    L = integral m hm T hT := by
  have hs (x : Field timeMeasure) (hx : x ∈ stepSpan m hm T hT) :
      L ⟨x, (stepSpan m hm T hT).le_topologicalClosure hx⟩ =
        integral m hm T hT ⟨x, (stepSpan m hm T hT).le_topologicalClosure hx⟩ := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, F, hF, rfl⟩ := hx
      exact (hL n F hF).trans (integral_native m hm T hT n F hF).symm
    | zero => exact (map_zero L).trans (map_zero (integral m hm T hT)).symm
    | add x y hx hy ihx ihy =>
      let X : space m hm T hT := ⟨x, (stepSpan m hm T hT).le_topologicalClosure hx⟩
      let Y : space m hm T hT := ⟨y, (stepSpan m hm T hT).le_topologicalClosure hy⟩
      change L (X + Y) = integral m hm T hT (X + Y)
      exact (L.map_add X Y).trans
        ((congrArg₂ (fun a b : Dual => a+b) ihx ihy).trans
          ((integral m hm T hT).map_add X Y).symm)
    | smul c x hx ih =>
      let X : space m hm T hT := ⟨x, (stepSpan m hm T hT).le_topologicalClosure hx⟩
      change L (c • X) = integral m hm T hT (c • X)
      exact (L.map_smul c X).trans
        ((congrArg (fun a : Dual => c • a) ih).trans
          ((integral m hm T hT).map_smul c X).symm)
  apply ContinuousLinearMap.coeFn_injective
  apply (span_dense m hm T hT).equalizer L.continuous (integral m hm T hT).continuous
  funext x
  exact hs x.val x.property

theorem native_integrals_converge {ι : Type*} (l : Filter ι)
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ι → ℕ) (F : ∀ i, Fin (size (n i)) → Test (n i)) (hF : ∀ i, Adapted (F i))
    (A : space m hm T hT)
    (h : Tendsto (fun i => adaptedField (n i) m hm T hT (F i)) l (𝓝 A.val)) :
    Tendsto (fun i => pairing m hm T hT (core (cylinderOf (n i) (stepPolynomial (F i)))))
      l (𝓝 (integral m hm T hT A)) := by
  have hh := ((firstChannel m T).continuous.tendsto A.val).comp h
  change Tendsto (fun i => firstChannel m T (adaptedField (n i) m hm T hT (F i)))
    l (𝓝 (integral m hm T hT A)) at hh
  have he : (fun i => firstChannel m T (adaptedField (n i) m hm T hT (F i))) =
      (fun i => pairing m hm T hT (core (cylinderOf (n i) (stepPolynomial (F i))))) :=
    funext (fun i => adapted_sum_dual (n i) m hm T hT (F i) (hF i))
  rw [he] at hh
  exact hh

end OperatorDerivativeRewrite.Foundation.HigherHeatAdaptedIntegralClosure
