import Foundation.StochasticCauchyExitMoments
import Foundation.CauchyPoissonDomainDensity
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Actual exit angle, normalized Haar law, and bounded boundary observables. -/
noncomputable section
open MeasureTheory Set Filter AddCircle
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyExitLaw
open InfiniteGaussian StochasticCauchyExitOccupation StochasticCauchyExitMoments
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct
private abbrev Angle := AddCircle (1:ℝ)
private abbrev e := CauchyPoissonDomainDensity.circleEquiv

def normalizedValue (R : ℝ) (w : Sample) : ℂ :=
  if ‖exitValue R w‖=R then exitValue R w/(R:ℂ) else 1

theorem normalizedValue_measurable (R : ℝ) : Measurable (normalizedValue R) :=
  Measurable.ite (measurableSet_eq_fun ((exitValue_measurable R).norm) measurable_const)
    ((exitValue_measurable R).div_const (R:ℂ)) measurable_const

theorem normalizedValue_ae (R : ℝ) (hR : 0≤R) :
    normalizedValue R =ᵐ[μ] fun w => exitValue R w/(R:ℂ) := by
  filter_upwards [exitValue_boundary R hR] with w hw
  simp [normalizedValue,hw]

theorem normalizedValue_norm (R : ℝ) (hR : 0<R) (w : Sample) : ‖normalizedValue R w‖=1 := by
  unfold normalizedValue
  split_ifs with h
  · rw [norm_div,h,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,div_self hR.ne']
  · simp

def normalizedCircle (R : ℝ) (hR : 0<R) (w : Sample) : Circle :=
  ⟨normalizedValue R w,mem_sphere_zero_iff_norm.mpr (normalizedValue_norm R hR w)⟩

theorem normalizedCircle_measurable (R : ℝ) (hR : 0<R) : Measurable (normalizedCircle R hR) :=
  (normalizedValue_measurable R).subtype_mk

def exitAngle (R : ℝ) (hR : 0<R) : Sample → Angle := fun w => e.symm (normalizedCircle R hR w)

theorem exitAngle_measurable (R : ℝ) (hR : 0<R) : Measurable (exitAngle R hR) :=
  e.symm.continuous.measurable.comp (normalizedCircle_measurable R hR)

theorem exitAngle_toCircle (R : ℝ) (hR : 0<R) (w : Sample) :
    (AddCircle.toCircle (exitAngle R hR w) : ℂ)=normalizedValue R w := by
  have he : e (e.symm (normalizedCircle R hR w))=normalizedCircle R hR w := e.apply_symm_apply _
  change AddCircle.homeomorphCircle (by norm_num : (1:ℝ) ≠ 0) (e.symm (normalizedCircle R hR w))=normalizedCircle R hR w at he
  rw [AddCircle.homeomorphCircle_apply] at he
  exact congrArg (fun z : Circle => (z:ℂ)) he

theorem normalizedValue_moment (R : ℝ) (hR : 0<R) (n : ℕ) :
    (∫ w,(normalizedValue R w)^n ∂μ)=if n=0 then 1 else 0 := by
  have he : (∫ w,(normalizedValue R w)^n ∂μ)=(∫ w,(exitValue R w)^n ∂μ)/(R:ℂ)^n := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [normalizedValue_ae R hR.le] with w hw
    rw [hw,div_pow]
  rw [he,exit_moment R hR.le n]
  by_cases hn : n=0
  · simp [hn]
  · simp [hn,zero_pow hn]

theorem exitAngle_fourier (R : ℝ) (hR : 0<R) (n : ℤ) :
    (∫ w,fourier (T := (1:ℝ)) n (exitAngle R hR w) ∂μ)=if n=0 then 1 else 0 := by
  have hp (m : ℕ) : (∫ w,fourier (T := (1:ℝ)) (m:ℤ) (exitAngle R hR w) ∂μ)=if m=0 then 1 else 0 := by
    have hf : ∀ w,fourier (T := (1:ℝ)) (m:ℤ) (exitAngle R hR w)=(normalizedValue R w)^m := by
      intro w
      rw [fourier_apply,toCircle_zsmul,Circle.coe_zpow,zpow_natCast,exitAngle_toCircle]
    simp_rw [hf]
    exact normalizedValue_moment R hR m
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast,Int.natCast_eq_zero] using hp m
  | negSucc m =>
    have hf : ∀ x : Angle,fourier (Int.negSucc m) x=starRingEnd ℂ (fourier ((m+1:ℕ):ℤ) x) := by
      intro x
      simpa only [Int.negSucc_eq,Int.natCast_add,Int.natCast_one] using (fourier_neg (T := (1:ℝ)) (n := ((m+1:ℕ):ℤ)) (x := x))
    simp_rw [hf]
    rw [integral_conj,hp]
    simp

def angleLaw (R : ℝ) (hR : 0<R) : Measure Angle := μ.map (exitAngle R hR)

instance angleLaw_probability (R : ℝ) (hR : 0<R) : IsProbabilityMeasure (angleLaw R hR) :=
by
  unfold angleLaw
  infer_instance

private def circleIntegral (ν : Measure Angle) [IsProbabilityMeasure ν] : C(Angle,ℂ) →L[ℂ] ℂ := by
  let L : C(Angle,ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x,f x ∂ν
      map_add' := fun f g => integral_add' (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c _ }
  exact L.mkContinuous 1 (fun f => by
    change ‖∫ x,f x ∂ν‖≤1*‖f‖
    simpa using norm_integral_le_of_norm_le_const (μ := ν) (C := ‖f‖)
      (Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x))

private theorem angle_measure_unique (ν η : Measure Angle) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (h : ∀ n : ℤ,(∫ x,fourier n x ∂ν)=∫ x,fourier n x ∂η) : ν=η := by
  let S := Submodule.span ℂ (range (fourier (T := (1:ℝ))))
  let F := circleIntegral ν
  let G := circleIntegral η
  have hS : ∀ f∈S,F f=G f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨n,rfl⟩ := hx;exact h n
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using congrArg₂ (·+·) ihx ihy
    | smul c x hx ih => simpa only [map_smul] using congrArg (c • ·) ih
  have hd : Dense (S : Set C(Angle,ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
  have hall : ∀ f : C(Angle,ℂ),F f=G f := by
    intro f
    exact closure_minimal (fun x hx => hS x hx) (isClosed_eq F.continuous G.continuous)
      (hd.closure_eq.symm ▸ Set.mem_univ f)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(Angle,ℂ) := ⟨fun x => (f x:ℂ),Complex.continuous_ofReal.comp f.continuous⟩
  have hf := hall fc
  change (∫ x,(f x:ℂ) ∂ν)=(∫ x,(f x:ℂ) ∂η) at hf
  rw [integral_complex_ofReal,integral_complex_ofReal] at hf
  exact Complex.ofReal_injective hf

theorem angleLaw_haar (R : ℝ) (hR : 0<R) : angleLaw R hR=haarAddCircle := by
  apply angle_measure_unique
  intro n
  rw [angleLaw,integral_map (exitAngle_measurable R hR).aemeasurable
    (fourier n).continuous.aestronglyMeasurable,exitAngle_fourier]
  by_cases hn : n=0
  · subst n;simp
  · rw [ite_eq_right hn]
    exact (integral_eq_zero_of_add_right_eq_neg (μ := haarAddCircle)
      (fourier_add_half_inv_index hn (by norm_num))).symm

/-- The actual complex exit law equals the radius-scaled uniform circle law. -/
theorem exitValue_law (R : ℝ) (hR : 0<R) :
    μ.map (exitValue R) = haarAddCircle.map (fun x : Angle => (R:ℂ)*(AddCircle.toCircle x:ℂ)) := by
  have hm : Measurable (fun x : Angle => (R:ℂ)*(AddCircle.toCircle x:ℂ)) := by fun_prop
  rw [← angleLaw_haar R hR,angleLaw,Measure.map_map hm (exitAngle_measurable R hR)]
  apply Measure.map_congr
  filter_upwards [normalizedValue_ae R hR.le] with w hw
  change exitValue R w = (R:ℂ)*(AddCircle.toCircle (exitAngle R hR w):ℂ)
  rw [exitAngle_toCircle,hw]
  field_simp [Complex.ofReal_ne_zero.mpr hR.ne']

theorem exit_observable_integrable (R : ℝ) (f : ℂ →ᵇ ℂ) :
    Integrable (fun w => f (exitValue R w)) μ := by
  apply Integrable.mono' (integrable_const ‖f‖)
    (f.continuous.measurable.comp (exitValue_measurable R)).aestronglyMeasurable
  exact Eventually.of_forall fun w => f.norm_coe_le_norm (exitValue R w)

/-- Actual-source expectation equals the genuine uniform boundary integral. -/
theorem exit_observable_mean (R : ℝ) (hR : 0<R) (f : ℂ →ᵇ ℂ) :
    (∫ w,f (exitValue R w) ∂μ)=
      ∫ x : Angle,f ((R:ℂ)*(AddCircle.toCircle x:ℂ)) ∂haarAddCircle := by
  have hm : Measurable (fun x : Angle => (R:ℂ)*(AddCircle.toCircle x:ℂ)) := by fun_prop
  rw [← integral_map (exitValue_measurable R).aemeasurable f.continuous.aestronglyMeasurable,
    exitValue_law R hR,integral_map hm.aemeasurable f.continuous.aestronglyMeasurable]

/-- The degenerate disk has a point law, without division by zero. -/
theorem exitValue_law_zero : μ.map (exitValue 0)=Measure.dirac (0:ℂ) := by
  have he : exitValue 0 =ᵐ[μ] fun _ : Sample => (0:ℂ) := by
    filter_upwards [exitValue_boundary 0 le_rfl] with w hw
    exact norm_eq_zero.mp hw
  rw [Measure.map_congr he]
  simp

end OperatorDerivativeRewrite.Foundation.StochasticCauchyExitLaw
