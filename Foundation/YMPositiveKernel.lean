import Foundation.YMResetGroundState
import Foundation.SignedDensityProbabilitySampling
/-!
Positive kinetic kernels under spatial multiplication.
The ground-state spectral statements are conditional on the displayed positive
integrable eigenfunction and affine eigenmode equations. They construct no
physical vacuum or continuum theory. The exact four-point ratio statements
concern the unprojected finite-product SU(2) temporal kernel.
-/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.YMPositiveKernel
variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]

def mass (k : Ω → Ω → ℝ) (x : Ω) : ℝ := ∫ y, k x y ∂ν
def rowDensity (k : Ω → Ω → ℝ) (x y : Ω) : ℝ := k x y / mass ν k x
def average (k : Ω → Ω → ℝ) (f : Ω → ℝ) (x : Ω) : ℝ := ∫ y, rowDensity ν k x y * f y ∂ν

theorem row_integrable (k : Ω → Ω → ℝ) (m M : ℝ) (hm : 0 < m)
    (hk : ∀ x, Measurable (k x)) (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M) (x : Ω) :
    Integrable (k x) ν := by
  apply Integrable.of_bound (hk x).aestronglyMeasurable M
  filter_upwards with y
  simpa [Real.norm_eq_abs,abs_of_pos (hm.trans_le (hb x y).1)] using (hb x y).2

theorem mass_bounds (k : Ω → Ω → ℝ) (m M : ℝ) (hm : 0 < m)
    (hk : ∀ x, Measurable (k x)) (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M) (x : Ω) :
    m ≤ mass ν k x ∧ mass ν k x ≤ M := by
  have hi := row_integrable ν k m M hm hk hb x
  constructor
  · simpa [mass] using integral_mono (integrable_const m) hi (fun y => (hb x y).1)
  · simpa [mass] using integral_mono hi (integrable_const M) (fun y => (hb x y).2)

theorem density_integrable (k : Ω → Ω → ℝ) (m M : ℝ) (hm : 0 < m)
    (hk : ∀ x, Measurable (k x)) (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M) (x : Ω) :
    Integrable (rowDensity ν k x) ν := (row_integrable ν k m M hm hk hb x).div_const _

theorem density_integral (k : Ω → Ω → ℝ) (m M : ℝ) (hm : 0 < m)
    (hk : ∀ x, Measurable (k x)) (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M) (x : Ω) :
    (∫ y, rowDensity ν k x y ∂ν) = 1 := by
  unfold rowDensity
  rw [integral_div]
  exact div_self (hm.trans_le (mass_bounds ν k m M hm hk hb x).1).ne'

theorem common_minorization (k : Ω → Ω → ℝ) (m M : ℝ) (hm : 0 < m)
    (hk : ∀ x, Measurable (k x)) (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M) (x y : Ω) :
    m/M ≤ rowDensity ν k x y := by
  have hs := mass_bounds ν k m M hm hk hb x
  exact div_le_div₀ (le_of_lt (hm.trans_le (hb x y).1)) (hb x y).1 (hm.trans_le hs.1) hs.2

theorem residual_bounds (k : Ω → Ω → ℝ) (m M : ℝ) (hm : 0 < m)
    (hk : ∀ x, Measurable (k x)) (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M)
    (f : Ω → ℝ) (hf : Measurable f) (hfb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (x : Ω) :
    0 ≤ average ν k f x - (m/M)*(∫ y, f y ∂ν) ∧
    average ν k f x - (m/M)*(∫ y, f y ∂ν) ≤ 1-m/M := by
  have hfi : Integrable f ν := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    filter_upwards with y
    simpa [Real.norm_eq_abs,abs_of_nonneg (hfb y).1] using (hfb y).2
  have hd := density_integrable ν k m M hm hk hb x
  have hdif : Integrable (fun y => rowDensity ν k x y * f y) ν := by
    have hi := hd.bdd_mul hf.aestronglyMeasurable (c := 1) (by
      filter_upwards with y
      simpa [Real.norm_eq_abs,abs_of_nonneg (hfb y).1] using (hfb y).2)
    simpa only [mul_comm] using hi
  have hr : Integrable (fun y => rowDensity ν k x y - m/M) ν := hd.sub (integrable_const _)
  have hrf : Integrable (fun y => (rowDensity ν k x y - m/M)*f y) ν := by
    have hi := hr.bdd_mul hf.aestronglyMeasurable (c := 1) (by
      filter_upwards with y
      simpa [Real.norm_eq_abs,abs_of_nonneg (hfb y).1] using (hfb y).2)
    simpa only [mul_comm] using hi
  have he : (∫ y, (rowDensity ν k x y-m/M)*f y ∂ν) =
      average ν k f x-(m/M)*(∫ y, f y ∂ν) := by
    simp_rw [sub_mul]
    rw [integral_sub hdif (hfi.const_mul _),integral_const_mul]
    rfl
  have hn (y : Ω) : 0 ≤ rowDensity ν k x y-m/M := sub_nonneg.mpr (common_minorization ν k m M hm hk hb x y)
  constructor
  · rw [← he]
    exact integral_nonneg (fun y => mul_nonneg (hn y) (hfb y).1)
  · have hh := integral_mono hrf hr (fun y => mul_le_of_le_one_right (hn y) (hfb y).2)
    rw [he,integral_sub hd (integrable_const _),density_integral ν k m M hm hk hb x] at hh
    simpa using hh

theorem oscillation_bound (k : Ω → Ω → ℝ) (m M : ℝ) (hm : 0 < m)
    (hk : ∀ x, Measurable (k x)) (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M)
    (f : Ω → ℝ) (hf : Measurable f) (hfb : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (x z : Ω) :
    |average ν k f x-average ν k f z| ≤ 1-m/M := by
  have hx := residual_bounds ν k m M hm hk hb f hf hfb x
  have hz := residual_bounds ν k m M hm hk hb f hf hfb z
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem affine_eigenvalue_bound (k : Ω → Ω → ℝ) (m M : ℝ) (hm : 0 < m)
    (hk : ∀ x, Measurable (k x)) (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M)
    (f : Ω → ℝ) (hf : Measurable f) (hfb : ∀ y, 0 ≤ f y ∧ f y ≤ 1)
    (r c : ℝ) (he : ∀ x, average ν k f x = r*f x+c)
    (x z : Ω) (hx : f x=1) (hz : f z=0) : |r| ≤ 1-m/M := by
  have hh := oscillation_bound ν k m M hm hk hb f hf hfb x z
  simpa [he,hx,hz] using hh
end OperatorDerivativeRewrite.Foundation.YMPositiveKernel


namespace OperatorDerivativeRewrite.Foundation.YMPositiveKernel
open SignedDensityProbabilitySampling
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem positive_sampler_integral (q f : Ω → ℝ) (hq : Measurable q)
    (hn : ∀ y, 0 ≤ q y) (hp : 0 < SignedDensityProbabilitySampling.mass μ q) :
    (∫ y, f y ∂sampler μ q) = (∫ y, q y*f y ∂μ)/SignedDensityProbabilitySampling.mass μ q := by
  rw [sampler,integral_smul_measure,ENNReal.toReal_inv,ENNReal.toReal_ofReal hp.le]
  have he := integral_orientation μ q hq f
  have ho : orientation q = fun _ => (1:ℝ) := by
    funext y
    simp only [orientation,ite_eq_left_iff]; intro hnneg; exact False.elim (hnneg (hn y))
  rw [ho] at he
  simp only [smul_eq_mul,one_mul] at he
  rw [he]
  simp only [smul_eq_mul]; exact inv_mul_eq_div _ _

def sandwich (h : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) (x : Ω) : ℝ :=
  h x * ∫ y, k x y*h y*f y ∂μ

theorem ground_bridge (h ψ : Ω → ℝ) (k : Ω → Ω → ℝ) (lam : ℝ)
    (hq : Measurable (fun y => h y*ψ y)) (hh : ∀ y, 0 < h y)
    (hψ : ∀ y, 0 < ψ y) (hlam : 0 < lam)
    (hp : 0 < SignedDensityProbabilitySampling.mass μ (fun y => h y*ψ y))
    (he : ∀ x, sandwich μ h k ψ x = lam*ψ x) (f : Ω → ℝ) (x : Ω) :
    sandwich μ h k (fun y => ψ y*f y) x/(lam*ψ x) =
      average (sampler μ (fun y => h y*ψ y)) k f x := by
  have hn (y : Ω) : 0 ≤ h y*ψ y := (mul_pos (hh y) (hψ y)).le
  have ht : (∫ y, k x y*h y*ψ y ∂μ) ≠ 0 := by
    have he' := he x
    unfold sandwich at he'
    intro hz
    rw [hz,mul_zero] at he'
    exact (mul_pos hlam (hψ x)).ne' he'.symm
  have hprod : (fun y => (h y*ψ y)*k x y) = (fun y => k x y*h y*ψ y) := by
    funext y; ring
  have hprod' : (fun y => (h y*ψ y)*(k x y*f y)) =
      (fun y => k x y*h y*(ψ y*f y)) := by funext y; ring
  unfold average rowDensity
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div,mass,positive_sampler_integral μ _ _ hq hn hp,
    positive_sampler_integral μ _ _ hq hn hp,hprod,hprod']
  change h x*(∫ y, k x y*h y*(ψ y*f y) ∂μ)/(lam*ψ x) = _
  have he' := he x
  unfold sandwich at he'
  rw [← he']
  field_simp [(hh x).ne',hp.ne',ht]



theorem ground_affine_eigenvalue_bound (h ψ : Ω → ℝ) (k : Ω → Ω → ℝ)
    (m M lam eta c : ℝ) (hm : 0 < m) (hlam : 0 < lam)
    (hk : ∀ x, Measurable (k x)) (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M)
    (hq : Measurable (fun y => h y*ψ y)) (hqi : Integrable (fun y => h y*ψ y) μ)
    (hh : ∀ y, 0 < h y) (hψ : ∀ y, 0 < ψ y)
    (hp : 0 < SignedDensityProbabilitySampling.mass μ (fun y => h y*ψ y))
    (he : ∀ x, sandwich μ h k ψ x = lam*ψ x)
    (g : Ω → ℝ) (hg : Measurable g) (hgb : ∀ y, 0 ≤ g y ∧ g y ≤ 1)
    (heig : ∀ x, sandwich μ h k (fun y => ψ y*g y) x = eta*ψ x*g x+c*(lam*ψ x))
    (x z : Ω) (hx : g x=1) (hz : g z=0) : |eta/lam| ≤ 1-m/M := by
  let ν := sampler μ (fun y => h y*ψ y)
  letI : IsProbabilityMeasure ν := sampler_probability μ _ hqi hp
  apply affine_eigenvalue_bound ν k m M hm hk hb g hg hgb (eta/lam) c ?_ x z hx hz
  intro y
  rw [← ground_bridge μ h ψ k lam hq hh hψ hlam hp he g y,heig y]
  have hln := hlam.ne'
  have hpn := (hψ y).ne'
  field_simp
end OperatorDerivativeRewrite.Foundation.YMPositiveKernel

namespace OperatorDerivativeRewrite.Foundation.YMPositiveKernel
open QuaternionSU2Representation SU2WilsonConvolution

def kinetic {n : ℕ} (β : ℝ) (C D : Fin n → SU2) : ℝ :=
  Real.exp (β*∑ i, halfTrace (C i*(D i)⁻¹))
def weightedKernel {n : ℕ} (h : (Fin n → SU2) → ℝ) (β : ℝ) (C D : Fin n → SU2) : ℝ :=
  h C*kinetic β C D*h D

def crossRatio {E : Type*} (K : E → E → ℝ) (x z y w : E) : ℝ := K x y*K z w/(K x w*K z y)

theorem spatial_cancellation {n : ℕ} (h : (Fin n → SU2) → ℝ) (hh : ∀ C, 0 < h C)
    (β : ℝ) (C E D F : Fin n → SU2) :
    crossRatio (weightedKernel h β) C E D F = crossRatio (kinetic β) C E D F := by
  unfold crossRatio weightedKernel kinetic
  field_simp [(hh C).ne',(hh E).ne',(hh D).ne',(hh F).ne']

theorem kinetic_bounds {n : ℕ} (β : ℝ) (C D : Fin n → SU2) :
    Real.exp (-((n:ℝ)*|β|)) ≤ kinetic β C D ∧
      kinetic β C D ≤ Real.exp ((n:ℝ)*|β|) := by
  have hs : |∑ i, halfTrace (C i*(D i)⁻¹)| ≤ (n:ℝ) := by
    calc
      _ ≤ ∑ i, |halfTrace (C i*(D i)⁻¹)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (1:ℝ) := Finset.sum_le_sum (fun i _ => halfTrace_bound _)
      _ = (n:ℝ) := by simp
  have he : |β*(∑ i, halfTrace (C i*(D i)⁻¹))| ≤ (n:ℝ)*|β| := by
    rw [abs_mul,mul_comm (n:ℝ)]
    exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp he).1,Real.exp_le_exp.mpr (abs_le.mp he).2⟩

theorem crossRatio_formula {n : ℕ} (β : ℝ) (C E D F : Fin n → SU2) :
    crossRatio (kinetic β) C E D F = Real.exp
      ((β*∑ i, halfTrace (C i*(D i)⁻¹))+(β*∑ i, halfTrace (E i*(F i)⁻¹))-
       ((β*∑ i, halfTrace (C i*(F i)⁻¹))+(β*∑ i, halfTrace (E i*(D i)⁻¹)))) := by
  unfold crossRatio kinetic
  rw [← Real.exp_add,← Real.exp_add,← Real.exp_sub]

theorem weighted_crossRatio_bound {n : ℕ} (h : (Fin n → SU2) → ℝ)
    (hh : ∀ C, 0 < h C) (β : ℝ) (C E D F : Fin n → SU2) :
    crossRatio (weightedKernel h β) C E D F ≤ Real.exp (4*(n:ℝ)*|β|) := by
  rw [spatial_cancellation h hh,crossRatio_formula]
  apply Real.exp_le_exp.mpr
  have bounds (A B : Fin n → SU2) :
      -((n:ℝ)*|β|) ≤ β*∑ i, halfTrace (A i*(B i)⁻¹) ∧
      (β*∑ i, halfTrace (A i*(B i)⁻¹)) ≤ (n:ℝ)*|β| := by
    have hb := kinetic_bounds β A B
    exact ⟨Real.exp_le_exp.mp hb.1,Real.exp_le_exp.mp hb.2⟩
  have h1 := bounds C D
  have h2 := bounds E F
  have h3 := bounds C F
  have h4 := bounds E D
  linarith

theorem center_crossRatio {n : ℕ} (h : (Fin n → SU2) → ℝ)
    (hh : ∀ C, 0 < h C) (β : ℝ) :
    crossRatio (weightedKernel h β) (fun _ => 1) (fun _ => SU2StapleExtremes.minusOne)
      (fun _ => 1) (fun _ => SU2StapleExtremes.minusOne) = Real.exp (4*(n:ℝ)*β) := by
  rw [spatial_cancellation h hh,crossRatio_formula]
  simp only [mul_inv_cancel,SU2OpenLinkGaugeObstruction.halfTrace_one,
    one_mul,halfTrace_inv,SU2OpenLinkGaugeObstruction.halfTrace_minusOne,
    inv_one,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  ring

theorem no_volume_uniform_crossRatio (β B : ℝ) (hβ : 0 < β) :
    ∃ n : ℕ, ∀ h : (Fin n → SU2) → ℝ, (∀ C, 0 < h C) →
      B < crossRatio (weightedKernel h β) (fun _ => 1) (fun _ => SU2StapleExtremes.minusOne)
        (fun _ => 1) (fun _ => SU2StapleExtremes.minusOne) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (B/(4*β))
  refine ⟨n,fun h hh => ?_⟩
  rw [center_crossRatio h hh]
  have hb : B < (n:ℝ)*(4*β) := (div_lt_iff₀ (by positivity : 0 < 4*β)).mp hn
  have he := Real.add_one_le_exp (4*(n:ℝ)*β)
  nlinarith
end OperatorDerivativeRewrite.Foundation.YMPositiveKernel

namespace OperatorDerivativeRewrite.Foundation.YMPositiveKernel
open QuaternionSU2Representation

theorem kinetic_measurable {n : ℕ} (β : ℝ) (C : Fin n → SU2) :
    Measurable (kinetic β C) := by
  apply Measurable.exp
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact halfTrace_measurable.comp
    ((measurable_const_mul (C i)).comp ((measurable_pi_apply i).inv))

theorem kinetic_oscillation_bound {n : ℕ} (ν : Measure (Fin n → SU2))
    [IsProbabilityMeasure ν] (β : ℝ) (f : (Fin n → SU2) → ℝ) (hf : Measurable f)
    (hfb : ∀ D, 0 ≤ f D ∧ f D ≤ 1) (C E : Fin n → SU2) :
    |average ν (kinetic β) f C-average ν (kinetic β) f E| ≤
      1-Real.exp (-(2*(n:ℝ)*|β|)) := by
  have he := oscillation_bound ν (kinetic β) (Real.exp (-((n:ℝ)*|β|)))
    (Real.exp ((n:ℝ)*|β|)) (Real.exp_pos _) (kinetic_measurable β)
    (kinetic_bounds β) f hf hfb C E
  have hratio : Real.exp (-((n:ℝ)*|β|))/Real.exp ((n:ℝ)*|β|) =
      Real.exp (-(2*(n:ℝ)*|β|)) := by
    rw [← Real.exp_sub]
    congr 1; ring
  rwa [hratio] at he

theorem kinetic_ground_eigenvalue_bound {n : ℕ} (μ : Measure (Fin n → SU2))
    (h ψ : (Fin n → SU2) → ℝ) (β lam eta c : ℝ) (hlam : 0 < lam)
    (hq : Measurable (fun D => h D*ψ D)) (hqi : Integrable (fun D => h D*ψ D) μ)
    (hh : ∀ D, 0 < h D) (hψ : ∀ D, 0 < ψ D)
    (hp : 0 < SignedDensityProbabilitySampling.mass μ (fun D => h D*ψ D))
    (he : ∀ C, sandwich μ h (kinetic β) ψ C = lam*ψ C)
    (g : (Fin n → SU2) → ℝ) (hg : Measurable g) (hgb : ∀ D, 0 ≤ g D ∧ g D ≤ 1)
    (heig : ∀ C, sandwich μ h (kinetic β) (fun D => ψ D*g D) C =
      eta*ψ C*g C+c*(lam*ψ C))
    (C E : Fin n → SU2) (hC : g C=1) (hE : g E=0) :
    |eta/lam| ≤ 1-Real.exp (-(2*(n:ℝ)*|β|)) := by
  let ν := SignedDensityProbabilitySampling.sampler μ (fun D => h D*ψ D)
  letI : IsProbabilityMeasure ν := SignedDensityProbabilitySampling.sampler_probability μ _ hqi hp
  have hav (A : Fin n → SU2) : average ν (kinetic β) g A = (eta/lam)*g A+c := by
    rw [← ground_bridge μ h ψ (kinetic β) lam hq hh hψ hlam hp he g A,heig A]
    field_simp [hlam.ne',(hψ A).ne']
  have ho := kinetic_oscillation_bound ν β g hg hgb C E
  simpa [hav,hC,hE] using ho
end OperatorDerivativeRewrite.Foundation.YMPositiveKernel

namespace OperatorDerivativeRewrite.Foundation.YMPositiveKernel
variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]

def rowLaw (k : Ω → Ω → ℝ) (x : Ω) : Measure Ω :=
  ν.withDensity (fun y => ENNReal.ofReal (rowDensity ν k x y))

theorem rowLaw_probability (k : Ω → Ω → ℝ) (m M : ℝ) (hm : 0 < m)
    (hk : ∀ x, Measurable (k x)) (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M) (x : Ω) :
    IsProbabilityMeasure (rowLaw ν k x) := by
  have hn (y : Ω) : 0 ≤ rowDensity ν k x y :=
    (div_pos (hm.trans_le (hb x y).1) (hm.trans_le (mass_bounds ν k m M hm hk hb x).1)).le
  constructor
  rw [rowLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (density_integrable ν k m M hm hk hb x)
      (ae_of_all ν hn),density_integral ν k m M hm hk hb x]
  norm_num

theorem rowLaw_integral (k : Ω → Ω → ℝ) (m M : ℝ) (hm : 0 < m)
    (hk : ∀ x, Measurable (k x)) (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M)
    (f : Ω → ℝ) (x : Ω) : (∫ y, f y ∂rowLaw ν k x) = average ν k f x := by
  have hn (y : Ω) : 0 ≤ rowDensity ν k x y :=
    (div_pos (hm.trans_le (hb x y).1) (hm.trans_le (mass_bounds ν k m M hm hk hb x).1)).le
  have hd : Measurable (rowDensity ν k x) := (hk x).div_const _
  rw [rowLaw,integral_withDensity_eq_integral_toReal_smul hd.ennreal_ofReal
    (ae_of_all ν (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul]
  rfl

theorem doob_balance {E : Type*} (h ψ : E → ℝ) (k : E → E → ℝ) (lam : ℝ)
    (hψ : ∀ x, ψ x ≠ 0) (hlam : lam ≠ 0) (hsym : ∀ x y, k x y=k y x) (x y : E) :
    ψ x^2*(h x*k x y*h y*ψ y/(lam*ψ x)) =
      ψ y^2*(h y*k y x*h x*ψ x/(lam*ψ y)) := by
  rw [hsym x y]
  field_simp [hψ x,hψ y,hlam]
end OperatorDerivativeRewrite.Foundation.YMPositiveKernel

namespace OperatorDerivativeRewrite.Foundation.YMPositiveKernel
open QuaternionSU2Representation SU2WilsonConvolution

theorem kinetic_symmetric {n : ℕ} (β : ℝ) (C D : Fin n → SU2) :
    kinetic β C D = kinetic β D C := by
  unfold kinetic
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_inv_rev,inv_inv] using (halfTrace_inv (C i*(D i)⁻¹)).symm
end OperatorDerivativeRewrite.Foundation.YMPositiveKernel
