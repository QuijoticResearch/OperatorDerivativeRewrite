import Foundation.CauchyPoissonGeneratorDomain
import Mathlib.Analysis.Fourier.AddCircle
/-! Density of the actual circle-generator domain by exact period-one Fourier
transport. At the zero pole the actual generator is unbounded on unit Fourier
modes. Ordinary domain density is distinct from finite graph-core equality. -/
noncomputable section
open Complex MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonDomainDensity
open CauchyPoissonCoreGenerator CauchyPoissonGeneratorDomain

def circleEquiv : AddCircle (1:ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)

def transport : C(AddCircle (1:ℝ),ℂ) →ₐ[ℂ] C(Circle,ℂ) :=
  ContinuousMap.compRightAlgHom ℂ ℂ ⟨circleEquiv.symm,circleEquiv.symm.continuous⟩

theorem transport_continuous : Continuous transport :=
  ContinuousMap.compRightAlgHom_continuous ℂ ℂ ⟨circleEquiv.symm,circleEquiv.symm.continuous⟩

theorem transport_surjective : Function.Surjective transport := by
  intro f
  refine ⟨f.comp ⟨circleEquiv,circleEquiv.continuous⟩, ?_⟩
  ext z
  change f (circleEquiv (circleEquiv.symm z)) = f z
  rw [circleEquiv.apply_symm_apply]

theorem transport_one_mode : transport (fourier (T := (1:ℝ)) 1) = coordinate := by
  ext z
  change fourier 1 (circleEquiv.symm z) = (z:ℂ)
  rw [fourier_one]
  have h : AddCircle.toCircle (circleEquiv.symm z) = z := by
    rw [← AddCircle.homeomorphCircle_apply (by norm_num : (1:ℝ) ≠ 0)]
    exact circleEquiv.apply_symm_apply z
  exact congrArg (fun w : Circle => (w:ℂ)) h

theorem fourier_nat_power (n : ℕ) : fourier (T := (1:ℝ)) (n:ℤ) = fourier 1 ^ n := by
  induction n with
  | zero => ext x; simp [fourier_zero]
  | succ n ih =>
    have h : fourier (T := (1:ℝ)) ((n:ℤ)+1) = fourier (n:ℤ) * fourier 1 := by
      ext x
      exact fourier_add
    simpa only [Nat.cast_add,Nat.cast_one,h,ih,pow_succ] using h

theorem transport_nat (n : ℕ) : transport (fourier (T := (1:ℝ)) (n:ℤ)) = coordinate^n := by
  rw [fourier_nat_power,map_pow,transport_one_mode]

theorem transport_neg_nat (n : ℕ) : transport (fourier (T := (1:ℝ)) (-(n:ℤ))) = star (coordinate^n) := by
  ext z
  change fourier (-(n:ℤ)) (circleEquiv.symm z) = star ((coordinate^n) z)
  rw [fourier_neg]
  have h := congrArg (fun f : C(Circle,ℂ) => f z) (transport_nat n)
  change fourier (n:ℤ) (circleEquiv.symm z) = (coordinate^n) z at h
  rw [h]
  rfl

theorem derivative_mem_domain (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ))
    (h : HasDerivWithinAt (orbit q hq f) g (Ioi 0) 0) : f ∈ (generator q hq).domain := by
  rw [domain_iff]
  refine ⟨g, ?_⟩
  have hh := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp h
  change Tendsto (fun t : ℝ => (t-0)⁻¹ • (orbit q hq f t-orbit q hq f 0)) _ _ at hh
  simpa only [Tangent,sub_zero,orbit_zero] using hh

theorem transported_mode_mem_domain (q : ℝ) (hq : |q| < 1) (n : ℤ) :
    transport (fourier (T := (1:ℝ)) n) ∈ (generator q hq).domain := by
  cases n with
  | ofNat n =>
    change transport (fourier (n:ℤ)) ∈ _
    rw [transport_nat]
    exact derivative_mem_domain q hq _ _ (power_hasDerivWithinAt q hq n)
  | negSucc n =>
    change transport (fourier (-((n+1:ℕ):ℤ))) ∈ _
    rw [transport_neg_nat]
    exact derivative_mem_domain q hq _ _ (star_power_hasDerivWithinAt q hq (n+1))

theorem domain_dense (q : ℝ) (hq : |q| < 1) : Dense ((generator q hq).domain : Set C(Circle,ℂ)) := by
  let S := Submodule.span ℂ (range (fourier (T := (1:ℝ))))
  have hm : S ≤ (generator q hq).domain.comap transport.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact transported_mode_mem_domain q hq n
  have hd : closure (S : Set C(AddCircle (1:ℝ),ℂ)) = univ := by
    change closure ((Submodule.span ℂ (range (fourier (T := (1:ℝ))))) : Set C(AddCircle (1:ℝ),ℂ)) = univ
    rw [← Submodule.topologicalClosure_coe,span_fourier_closure_eq_top]
    rfl
  intro f
  obtain ⟨u,hu⟩ := transport_surjective f
  have hi : f ∈ closure (transport '' (S : Set C(AddCircle (1:ℝ),ℂ))) := by
    apply image_closure_subset_closure_image transport_continuous
    exact ⟨u, by rw [hd]; trivial,hu⟩
  apply closure_mono (s := transport '' (S : Set C(AddCircle (1:ℝ),ℂ))) _ hi
  rintro _ ⟨u,hu,rfl⟩
  exact hm hu

theorem zero_power_velocity (n : ℕ) : powerVelocity 0 n = (-(n:ℂ)) • coordinate^n := by
  cases n with
  | zero => simp [powerVelocity]
  | succ n =>
    ext z
    simp only [powerVelocity,ContinuousMap.mul_apply,ContinuousMap.pow_apply,Nat.add_sub_cancel]
    change (((n+1:ℕ):ℂ)*(z:ℂ)^n)* (-(z:ℂ)+(0:ℂ)/(1-0^2)*(1-(z:ℂ)^2)) =
      (-((n+1:ℕ):ℂ))*(z:ℂ)^(n+1)
    simp only [zero_div,zero_mul,add_zero,pow_succ]
    ring

theorem coordinate_power_norm (n : ℕ) : ‖coordinate^n‖ = 1 := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  have h : ∀ z : Circle, ‖(coordinate^n) z‖ = 1 := by
    intro z
    change ‖(z:ℂ)^n‖ = 1
    simp
  simp only [h]
  exact ciSup_const

theorem zero_power_velocity_norm (n : ℕ) : ‖powerVelocity 0 n‖ = (n:ℝ) := by
  rw [zero_power_velocity,norm_smul,coordinate_power_norm,mul_one]
  simp

theorem zero_generator_unbounded :
    ¬ ∃ C : ℝ, ∀ f g : C(Circle,ℂ),
      (f,g) ∈ (generator 0 (by norm_num)).graph → ‖g‖ ≤ C*‖f‖ := by
  rintro ⟨C,hC⟩
  obtain ⟨n,hn⟩ := exists_nat_gt C
  have hg : (coordinate^n,powerVelocity 0 n) ∈ (generator 0 (by norm_num)).graph := by
    rw [generator_graph_iff]
    have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp
      (power_hasDerivWithinAt 0 (by norm_num) n)
    change Tendsto (fun t : ℝ => (t-0)⁻¹ • (orbit 0 (by norm_num) (coordinate^n) t-
      orbit 0 (by norm_num) (coordinate^n) 0)) _ _ at h
    simpa only [Tangent,sub_zero,orbit_zero] using h
  have hb := hC _ _ hg
  rw [zero_power_velocity_norm,coordinate_power_norm,mul_one] at hb
  exact (not_le_of_gt hn) hb

end OperatorDerivativeRewrite.Foundation.CauchyPoissonDomainDensity
