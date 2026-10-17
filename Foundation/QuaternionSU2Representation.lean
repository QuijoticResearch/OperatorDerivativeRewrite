import Foundation.QuaternionAngularHaar
import Foundation.SU2ExponentialMembership
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! An explicit faithful quaternion representation and its unit-quaternion / SU(2) equivalence. -/
noncomputable section
open scoped Quaternion Matrix Topology
namespace OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open SU2TraceHessianModel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev SU2 := ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)

def repr (q : ℍ) : M2 :=
  !![(q.re:ℂ)+(q.imI:ℂ)*Complex.I, (q.imJ:ℂ)+(q.imK:ℂ)*Complex.I;
    -(q.imJ:ℂ)+(q.imK:ℂ)*Complex.I, (q.re:ℂ)-(q.imI:ℂ)*Complex.I]

theorem repr_one : repr 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [repr]

theorem repr_mul (p q : ℍ) : repr (p*q) = repr p * repr q := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [repr, Matrix.mul_apply, Fin.sum_univ_two, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem repr_star (q : ℍ) : repr (star q) = (repr q)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [repr, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im]

theorem repr_real (r : ℝ) : repr (r : ℍ) = (r:ℂ) • (1 : M2) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [repr]

theorem repr_det (q : ℍ) : Matrix.det (repr q) = ((Quaternion.normSq q : ℝ) : ℂ) := by
  apply Complex.ext <;>
    norm_num [repr, Matrix.det_fin_two, Quaternion.normSq_def', Fin.sum_univ_succ,
      pow_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem repr_trace (q : ℍ) : Matrix.trace (repr q) = (2*q.re : ℝ) := by
  simp [repr, Matrix.trace_fin_two]
  ring

theorem repr_traceReal (q : ℍ) : traceReal (repr q) = 2*q.re := by
  rw [traceReal, repr_trace]
  norm_num

theorem repr_halfTrace (q : ℍ) : traceReal (repr q)/2 = q.re := by
  rw [repr_traceReal]
  ring

def recover (A : M2) : ℍ := ⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im⟩

theorem recover_repr (q : ℍ) : recover (repr q) = q := by
  ext <;> norm_num [recover, repr, Complex.mul_re, Complex.mul_im]

theorem repr_injective : Function.Injective repr :=
  Function.LeftInverse.injective recover_repr

theorem repr_mem (u : QuaternionAngularHaar.Group) : repr (u : ℍ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_specialUnitaryGroup_iff.mpr
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    change repr (u : ℍ) * (repr (u : ℍ))ᴴ = 1
    have hu : (u : ℍ) * star (u : ℍ) = 1 := (Unitary.mem_iff.mp u.property).2
    rw [← repr_star, ← repr_mul, hu, repr_one]
  · rw [repr_det]
    have hn : Quaternion.normSq (u : ℍ) = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, CStarRing.norm_coe_unitary, one_mul]
    rw [hn]
    norm_num

theorem adjugate_eq_star (A : M2) (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix.adjugate A = Aᴴ := by
  have hu : A*Aᴴ=1 := Matrix.mem_unitaryGroup_iff.mp hA.1
  have hd : Matrix.det A=1 := hA.2
  calc
    Matrix.adjugate A = Matrix.adjugate A * 1 := (mul_one _).symm
    _ = Matrix.adjugate A * (A*Aᴴ) := by rw [hu]
    _ = (Matrix.adjugate A*A)*Aᴴ := (mul_assoc _ _ _).symm
    _ = Aᴴ := by rw [Matrix.adjugate_mul, hd, one_smul, one_mul]

theorem repr_recover (A : M2) (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    repr (recover A) = A := by
  have he := adjugate_eq_star A hA
  have hdiag : A 1 1 = star (A 0 0) := by
    have h := congrArg (fun B : M2 => B 0 0) he
    simpa [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] using h
  have hlow : A 1 0 = -star (A 0 1) := by
    have h := congrArg (fun B : M2 => B 1 0) he
    have hh : -A 1 0 = star (A 0 1) := by
      simpa [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] using h
    exact neg_eq_iff_eq_neg.mp hh
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [repr, recover, hdiag, hlow, Complex.mul_re, Complex.mul_im]

theorem recover_mem (A : SU2) : recover (A : M2) ∈ unitary ℍ := by
  apply QuaternionAngularHaar.mem_unitary_of_norm_one
  have hd := repr_det (recover (A : M2))
  rw [repr_recover _ A.property] at hd
  have hn : Quaternion.normSq (recover (A : M2)) = 1 := by
    have h := congrArg Complex.re hd
    have hdet : Matrix.det (A : M2) = 1 := A.property.2
    rw [hdet] at h
    simpa using h.symm
  rw [Quaternion.normSq_eq_norm_mul_self] at hn
  nlinarith [norm_nonneg (recover (A : M2))]

def hom : QuaternionAngularHaar.Group →* SU2 where
  toFun u := ⟨repr (u : ℍ), repr_mem u⟩
  map_one' := Subtype.ext repr_one
  map_mul' u v := Subtype.ext (repr_mul (u : ℍ) (v : ℍ))

theorem hom_injective : Function.Injective hom := by
  intro u v huv
  apply Subtype.ext
  apply repr_injective
  exact congrArg (fun A : SU2 => (A : M2)) huv

theorem hom_surjective : Function.Surjective hom := by
  intro A
  refine ⟨⟨recover (A : M2), recover_mem A⟩, ?_⟩
  apply Subtype.ext
  exact repr_recover _ A.property

def equiv : QuaternionAngularHaar.Group ≃* SU2 :=
  MulEquiv.ofBijective hom ⟨hom_injective, hom_surjective⟩

theorem halfTrace_hom (u : QuaternionAngularHaar.Group) :
    traceReal ((hom u : SU2) : M2)/2 = QuaternionAngularHaar.realCoordinate u :=
  repr_halfTrace (u : ℍ)

theorem repr_continuous : Continuous repr := by
  have ha : Continuous (fun q : ℍ => (q.re : ℂ)) :=
    Complex.continuous_ofReal.comp Quaternion.continuous_re
  have hb : Continuous (fun q : ℍ => (q.imI : ℂ)) :=
    Complex.continuous_ofReal.comp Quaternion.continuous_imI
  have hc : Continuous (fun q : ℍ => (q.imJ : ℂ)) :=
    Complex.continuous_ofReal.comp Quaternion.continuous_imJ
  have hd : Continuous (fun q : ℍ => (q.imK : ℂ)) :=
    Complex.continuous_ofReal.comp Quaternion.continuous_imK
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · exact ha.add (hb.mul_const Complex.I)
  · exact hc.add (hd.mul_const Complex.I)
  · exact hc.neg.add (hd.mul_const Complex.I)
  · exact ha.sub (hb.mul_const Complex.I)

theorem hom_continuous : Continuous hom := by
  exact (repr_continuous.comp continuous_subtype_val).subtype_mk _

def homeomorph : QuaternionAngularHaar.Group ≃ₜ SU2 :=
  hom_continuous.homeoOfEquivCompactToT2 (f := equiv.toEquiv)

instance su2_compact : CompactSpace SU2 := homeomorph.compactSpace

instance su2_continuousInv : ContinuousInv SU2 where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun A : SU2 => star (A : M2))
    exact continuous_subtype_val.star

instance su2_topologicalGroup : IsTopologicalGroup SU2 where

def law : MeasureTheory.Measure SU2 := QuaternionAngularHaar.law.map hom

instance law_probability : MeasureTheory.IsProbabilityMeasure law := by unfold law; infer_instance

instance law_isHaar : law.IsHaarMeasure :=
  MeasureTheory.Measure.isHaarMeasure_map_of_isFiniteMeasure
    QuaternionAngularHaar.law hom hom_continuous hom_surjective

theorem law_eq_probability_haar (ν : MeasureTheory.Measure SU2)
    [MeasureTheory.IsProbabilityMeasure ν] [ν.IsHaarMeasure] : law = ν :=
  MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure law ν

def halfTrace (A : SU2) : ℝ := traceReal (A : M2)/2

theorem halfTrace_map (u : QuaternionAngularHaar.Group) :
    halfTrace (hom u) = QuaternionAngularHaar.realCoordinate u := halfTrace_hom u

theorem halfTrace_measurable : Measurable halfTrace := by
  have he : halfTrace = fun A : SU2 => ((A : M2) 0 0).re/2+((A : M2) 1 1).re/2 := by
    funext A
    simp [halfTrace, traceReal, Matrix.trace_fin_two, add_div]
  rw [he]
  have hentry (i j : Fin 2) : Continuous (fun A : SU2 => (A : M2) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact (((Complex.continuous_re.comp (hentry 0 0)).div_const 2).add
    ((Complex.continuous_re.comp (hentry 1 1)).div_const 2)).measurable

theorem halfTrace_bound (A : SU2) : |halfTrace A| ≤ 1 := by
  obtain ⟨u, rfl⟩ := hom_surjective A
  rw [halfTrace_map]
  exact QuaternionAngularHaar.realCoordinate_bound u

open MeasureTheory Filter in
theorem weighted_halfTrace (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (g : ℝ → ℝ) (hg : Measurable g) (t : ℝ) :
    BoundedExponentialTiltResponse.weighted ν halfTrace (fun A => g (halfTrace A)) t =
      BoundedExponentialTiltResponse.weighted QuaternionAngularHaar.law
        QuaternionAngularHaar.realCoordinate (fun u => g (QuaternionAngularHaar.realCoordinate u)) t := by
  rw [← law_eq_probability_haar ν]
  have hm : Measurable (fun A : SU2 => g (halfTrace A)*Real.exp (t*halfTrace A)) :=
    (hg.comp halfTrace_measurable).mul ((measurable_const.mul halfTrace_measurable).exp)
  have he := integral_map (μ := QuaternionAngularHaar.law)
    hom_continuous.measurable.aemeasurable hm.aestronglyMeasurable
  change (∫ A, g (halfTrace A)*Real.exp (t*halfTrace A) ∂QuaternionAngularHaar.law.map hom) = _
  rw [he]
  change (∫ u, g (halfTrace (hom u))*Real.exp (t*halfTrace (hom u)) ∂QuaternionAngularHaar.law) = _
  simp only [halfTrace_map, BoundedExponentialTiltResponse.weighted]

open MeasureTheory in
theorem partition_halfTrace (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] (t : ℝ) :
    BoundedExponentialTiltResponse.partition ν halfTrace t =
      BoundedExponentialTiltResponse.partition QuaternionAngularHaar.law
        QuaternionAngularHaar.realCoordinate t :=
  weighted_halfTrace ν (fun _ => 1) measurable_const t

open MeasureTheory in
theorem expectation_halfTrace (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (g : ℝ → ℝ) (hg : Measurable g) (t : ℝ) :
    BoundedExponentialTiltResponse.expectation ν halfTrace (fun A => g (halfTrace A)) t =
      BoundedExponentialTiltResponse.expectation QuaternionAngularHaar.law
        QuaternionAngularHaar.realCoordinate (fun u => g (QuaternionAngularHaar.realCoordinate u)) t := by
  unfold BoundedExponentialTiltResponse.expectation
  rw [weighted_halfTrace ν g hg t, partition_halfTrace ν t]

open MeasureTheory in
theorem su2_variance_eq (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] (t : ℝ) :
    BoundedExponentialTiltResponse.variance ν halfTrace (fun A => halfTrace A+halfTrace A^2) t =
      BoundedExponentialTiltResponse.variance QuaternionAngularHaar.law
        QuaternionAngularHaar.realCoordinate
        (fun u => QuaternionAngularHaar.realCoordinate u+QuaternionAngularHaar.realCoordinate u^2) t := by
  unfold BoundedExponentialTiltResponse.variance
  rw [expectation_halfTrace ν (fun r => (r+r^2)^2) (by fun_prop) t,
    expectation_halfTrace ν (fun r => r+r^2) (by fun_prop) t]

open MeasureTheory in
theorem su2_variance_zero (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] :
    BoundedExponentialTiltResponse.variance ν halfTrace (fun A => halfTrace A+halfTrace A^2) 0 = 5/16 := by
  rw [su2_variance_eq, QuaternionAngularHaar.haar_variance_zero]

open MeasureTheory in
theorem su2_variance_derivative (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] :
    HasDerivAt (BoundedExponentialTiltResponse.variance ν halfTrace
      (fun A => halfTrace A+halfTrace A^2)) (1/8) 0 := by
  have he : BoundedExponentialTiltResponse.variance ν halfTrace (fun A => halfTrace A+halfTrace A^2) =
      BoundedExponentialTiltResponse.variance QuaternionAngularHaar.law
        QuaternionAngularHaar.realCoordinate
        (fun u => QuaternionAngularHaar.realCoordinate u+QuaternionAngularHaar.realCoordinate u^2) :=
    funext (su2_variance_eq ν)
  rw [he]
  exact QuaternionAngularHaar.haar_variance_derivative QuaternionAngularHaar.law

open MeasureTheory in
theorem su2_variance_increases (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (ε : ℝ) (hε : 0 < ε) : ∃ t, 0 < t ∧ t < ε ∧
      BoundedExponentialTiltResponse.variance ν halfTrace (fun A => halfTrace A+halfTrace A^2) 0 <
      BoundedExponentialTiltResponse.variance ν halfTrace (fun A => halfTrace A+halfTrace A^2) t := by
  simpa only [su2_variance_eq] using
    QuaternionAngularHaar.haar_variance_increases QuaternionAngularHaar.law ε hε

open MeasureTheory Set in
theorem su2_variance_not_antitone (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] :
    ¬ AntitoneOn (BoundedExponentialTiltResponse.variance ν halfTrace
      (fun A => halfTrace A+halfTrace A^2)) (Ici 0) := by
  intro hanti
  obtain ⟨t, ht, _, hinc⟩ := su2_variance_increases ν 1 (by norm_num)
  have he := hanti (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht.le) ht.le
  exact (not_lt_of_ge he) hinc

theorem halfTrace_conjugate (U A : SU2) : halfTrace (U*A*U⁻¹) = halfTrace A := by
  have hi : (((U⁻¹ : SU2) : M2)*(U : M2)) = 1 := by
    change ((U⁻¹*U : SU2) : M2) = 1
    simp
  change (Matrix.trace (((U : M2)*(A : M2))*((U⁻¹ : SU2) : M2))).re/2 =
    (Matrix.trace (A : M2)).re/2
  rw [Matrix.trace_mul_comm, ← mul_assoc, hi, one_mul]

theorem halfTrace_polynomial_not_constant :
    ¬ ∃ c : ℝ, ∀ A : SU2, halfTrace A+halfTrace A^2 = c := by
  rintro ⟨c, hc⟩
  have hp := hc 1
  norm_num [halfTrace, traceReal, Matrix.trace_fin_two] at hp
  let u : QuaternionAngularHaar.Group := ⟨(-1 : ℍ), by simp [Unitary.mem_iff]⟩
  have hn := hc (hom u)
  rw [halfTrace_map] at hn
  norm_num [QuaternionAngularHaar.realCoordinate, u] at hn
  linarith

end OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
