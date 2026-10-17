import Foundation.PeriodicCoarseCurl
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Actual raw-averaging gauge and normalized planar Stokes counterexamples. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseGaugeDiagnostics
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

def coarseOrigin : CoarseVertex := fun _ => 0

def averageZ (f : Edge → ℤ) (q : CoarseEdge) : ℤ :=
  ∑ b : Bits, if b q.2=1 then f (fineVertex q.1 b,q.2) else 0

def coarseIntCurl (c : CoarseEdge → ℤ) (q : CoarseVertex) (i j : Direction) : ℤ :=
  c (q,i)+c (coarseShift q i,j)-c (coarseShift q j,i)-c (q,j)

def flatLiftZ (c : CoarseEdge → ℤ) (e : Edge) : ℤ :=
  if oddEdge e then c (coarseBlock e.1,e.2) else 0

theorem average_cast (f : Edge → ℤ) (q : CoarseEdge) :
    average (fun e => (f e : ℝ)) q=(1/8 : ℝ)*(averageZ f q : ℝ) := by
  rw [average_apply]
  congr 1
  unfold averageZ
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : b q.2=1 <;> simp [h]

theorem flatLift_cast (c : CoarseEdge → ℤ) :
    flatLift (fun e => (c e : ℝ)) = fun e => (flatLiftZ c e : ℝ) := by
  funext e
  rw [flatLift_apply]
  by_cases h : oddEdge e <;> simp [flatLiftZ, h]

theorem curl_cast (f : Edge → ℤ) (v : Vertex) (i j : Direction) :
    curl (fun e => (f e : ℝ)) v i j=(intCurl f v i j : ℝ) := by
  simp [curl, intCurl]

theorem coarseCurl_cast (c : CoarseEdge → ℤ) (q : CoarseVertex) (i j : Direction) :
    coarseCurl (fun e => (c e : ℝ)) q i j=(coarseIntCurl c q i j : ℝ) := by
  simp [coarseCurl, coarseIntCurl]

theorem coarseCurl_average_cast (f : Edge → ℤ) (q : CoarseVertex) (i j : Direction) :
    coarseCurl (average (fun e => (f e : ℝ))) q i j =
      (1/8 : ℝ)*(coarseIntCurl (averageZ f) q i j : ℝ) := by
  simp only [coarseCurl, average_cast, coarseIntCurl, Int.cast_add, Int.cast_sub]
  ring

def badPotentialZ (v : Vertex) : ℤ := (-1)^(v 0).val * (-1)^((v 1).val/2)
def badPotential (v : Vertex) : ℝ := (badPotentialZ v : ℝ)
def badGradient : Edge → ℝ := gradientMap badPotential

theorem badGradient_cast (e : Edge) : badGradient e=(gradient badPotentialZ e : ℝ) := by
  simp [badGradient, gradientMap, badPotential, gradient]

theorem badGradient_fine_closed : incidence badGradient=0 := incidence_gradient_zero badPotential

theorem int_averaged_bad_curl :
    coarseIntCurl (averageZ (gradient badPotentialZ)) coarseOrigin 0 1=32 := by decide

theorem averaged_bad_curl : coarseCurl (average badGradient) coarseOrigin 0 1=4 := by
  have he : badGradient=(fun e => (gradient badPotentialZ e : ℝ)) := funext badGradient_cast
  rw [he, coarseCurl_average_cast, int_averaged_bad_curl]
  norm_num

theorem averaged_bad_not_gradient : average badGradient ∉ LinearMap.range coarseGradient := by
  rintro ⟨φ, hφ⟩
  have h := congrArg (fun c => coarseCurl c coarseOrigin 0 1) hφ
  rw [coarseCurl_gradient, averaged_bad_curl] at h
  norm_num at h

theorem averaging_not_gradient_compatible :
    ¬ LinearMap.range gradientMap ≤ (LinearMap.range coarseGradient).comap average := by
  intro h
  exact averaged_bad_not_gradient (h ⟨badPotential, rfl⟩)

abbrev FineGaugeQuotient := (Edge → ℝ) ⧸ LinearMap.range gradientMap
abbrev CoarseGaugeQuotient := (CoarseEdge → ℝ) ⧸ LinearMap.range coarseGradient

theorem no_raw_quotient_map : ¬ ∃ F : FineGaugeQuotient → CoarseGaugeQuotient,
    ∀ f : Edge → ℝ, F (Submodule.Quotient.mk f)=Submodule.Quotient.mk (average f) := by
  rintro ⟨F, hF⟩
  have hclass : (Submodule.Quotient.mk badGradient : FineGaugeQuotient)=Submodule.Quotient.mk 0 := by
    apply (Submodule.Quotient.eq _).mpr
    simpa only [sub_zero] using
      (show badGradient ∈ LinearMap.range gradientMap from ⟨badPotential, rfl⟩)
  have he := congrArg F hclass
  rw [hF badGradient, hF 0, map_zero] at he
  have hz : (Submodule.Quotient.mk (average badGradient) : CoarseGaugeQuotient)=0 := by
    simpa using he
  exact averaged_bad_not_gradient ((Submodule.Quotient.mk_eq_zero _).mp hz)

theorem normalizedLift_gradient (φ : CoarseVertex → ℝ) :
    normalizedLift (coarseGradient φ) =
      gradientMap ((1/8 : ℝ) • (fun v => φ (coarseBlock v))) := by
  rw [normalizedLift, LinearMap.smul_apply, flatLift_gradient, map_smul]

def planarVertex (a b : ZMod 2) : Vertex :=
  fun i => if i=0 then (a.val : ℕ) else if i=1 then (b.val : ℕ) else 0

def coarseDeltaZ (e : CoarseEdge) : ℤ := if e=(coarseOrigin,0) then 1 else 0
def coarseDelta (e : CoarseEdge) : ℝ := (coarseDeltaZ e : ℝ)

theorem int_coarse_delta_curl : coarseIntCurl coarseDeltaZ coarseOrigin 0 1=1 := by decide

theorem int_flat_planar_sum : (∑ a : ZMod 2, ∑ b : ZMod 2,
    intCurl (flatLiftZ coarseDeltaZ) (planarVertex a b) 0 1)=1 := by decide

theorem coarse_delta_curl : coarseCurl coarseDelta coarseOrigin 0 1=1 := by
  unfold coarseDelta
  rw [coarseCurl_cast, int_coarse_delta_curl]
  norm_num

theorem flat_planar_sum : (∑ a : ZMod 2, ∑ b : ZMod 2,
    curl (flatLift coarseDelta) (planarVertex a b) 0 1)=1 := by
  unfold coarseDelta
  rw [flatLift_cast]
  simp_rw [curl_cast]
  exact_mod_cast int_flat_planar_sum

theorem normalized_planar_sum : (∑ a : ZMod 2, ∑ b : ZMod 2,
    curl (normalizedLift coarseDelta) (planarVertex a b) 0 1)=(1/8 : ℝ) := by
  simp_rw [normalizedLift, LinearMap.smul_apply, curl_smul]
  simp_rw [← Finset.mul_sum]
  rw [flat_planar_sum]
  norm_num

theorem literal_unscaled_Stokes_fails : coarseCurl coarseDelta coarseOrigin 0 1 ≠
    ∑ a : ZMod 2, ∑ b : ZMod 2, curl (normalizedLift coarseDelta) (planarVertex a b) 0 1 := by
  rw [coarse_delta_curl, normalized_planar_sum]
  norm_num

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseGaugeDiagnostics
