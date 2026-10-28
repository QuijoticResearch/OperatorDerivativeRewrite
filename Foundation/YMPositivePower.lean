import Foundation.YMPositiveKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Constructive positive-kernel powers for the missing finite-volume Wilson
vacuum. The intended limit construction is not an assumed existence axiom. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.YMPositivePower
variable {Ω : Type*} [MeasurableSpace Ω] [Nonempty Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

def applyKernel (k : Ω → Ω → ℝ) (f : Ω → ℝ) (x : Ω) : ℝ := ∫ y,k x y*f y ∂μ

def power (k : Ω → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 1
  | n+1 => applyKernel μ k (power k n)

variable (k : Ω → Ω → ℝ) (m M : ℝ)
variable (hk : Measurable (Function.uncurry k)) (hm : 0 < m)
variable (hb : ∀ x y,m ≤ k x y ∧ k x y ≤ M)

include hm hb in
private theorem upper_pos : 0 < M := by
  let x : Ω := Classical.choice inferInstance
  exact hm.trans_le ((hb x x).1.trans (hb x x).2)

include hk in
theorem power_measurable (n : ℕ) : Measurable (power μ k n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ((hk.mul (ih.comp measurable_snd)).stronglyMeasurable.integral_prod_right).measurable

include hk hm hb in
private theorem integrand_integrable (f : Ω → ℝ) (U : ℝ) (hf : Measurable f)
    (hfb : ∀ y,0 ≤ f y ∧ f y ≤ U) (x : Ω) : Integrable (fun y => k x y*f y) μ := by
  apply Integrable.of_bound ((hk.comp measurable_prodMk_left).mul hf).aestronglyMeasurable (M*U)
  filter_upwards with y
  change ‖k x y*f y‖ ≤ M*U
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hm.trans_le (hb x y).1).le (hfb y).1)]
  exact mul_le_mul (hb x y).2 (hfb y).2 (hfb y).1 (upper_pos k m M hm hb).le

include hk hm hb in
private theorem apply_bounds (f : Ω → ℝ) (L U : ℝ) (hL : 0 ≤ L) (hf : Measurable f)
    (hfb : ∀ y,L ≤ f y ∧ f y ≤ U) (x : Ω) :
    m*L ≤ applyKernel μ k f x ∧ applyKernel μ k f x ≤ M*U := by
  have hi := integrand_integrable μ k m M hk hm hb f U hf
    (fun y => ⟨hL.trans (hfb y).1,(hfb y).2⟩) x
  constructor
  · have he := integral_mono (integrable_const (m*L)) hi
      (fun y => mul_le_mul (hb x y).1 (hfb y).1 hL (hm.trans_le (hb x y).1).le)
    simpa [applyKernel] using he
  · have he := integral_mono hi (integrable_const (M*U))
      (fun y => mul_le_mul (hb x y).2 (hfb y).2 (hL.trans (hfb y).1)
        (upper_pos k m M hm hb).le)
    simpa [applyKernel] using he

include hk hm hb in
theorem power_bounds (n : ℕ) (x : Ω) : m^n ≤ power μ k n x ∧ power μ k n x ≤ M^n := by
  induction n generalizing x with
  | zero => simp [power]
  | succ n ih =>
    have he := apply_bounds μ k m M hk hm hb (power μ k n) (m^n) (M^n)
      (pow_nonneg hm.le _) (power_measurable μ k hk n) (fun y => ih y) x
    simpa [power,pow_succ,mul_comm] using he

include hk hm hb in
theorem power_pos (n : ℕ) (x : Ω) : 0 < power μ k n x :=
  (pow_pos hm n).trans_le (power_bounds μ k m M hk hm hb n x).1

include hk hm hb in
private theorem power_integrand (n : ℕ) (x : Ω) :
    Integrable (fun y => k x y*power μ k n y) μ :=
  integrand_integrable μ k m M hk hm hb (power μ k n) (M^n)
    (power_measurable μ k hk n)
    (fun y => ⟨(power_pos μ k m M hk hm hb n y).le,
      (power_bounds μ k m M hk hm hb n y).2⟩) x

include hk hm hb in
theorem power_successor_bounds (n : ℕ) (x : Ω) :
    m*power μ k n x ≤ power μ k (n+1) x ∧
      power μ k (n+1) x ≤ M*power μ k n x := by
  induction n generalizing x with
  | zero => simpa [power] using power_bounds μ k m M hk hm hb 1 x
  | succ n ih =>
    have hlo := integral_mono ((power_integrand μ k m M hk hm hb n x).const_mul m)
      (power_integrand μ k m M hk hm hb (n+1) x) (fun y => by
        have hp := mul_le_mul_of_nonneg_left (ih y).1 (hm.trans_le (hb x y).1).le
        nlinarith only [hp])
    have hhi := integral_mono (power_integrand μ k m M hk hm hb (n+1) x)
      ((power_integrand μ k m M hk hm hb n x).const_mul M) (fun y => by
        have hp := mul_le_mul_of_nonneg_left (ih y).2 (hm.trans_le (hb x y).1).le
        nlinarith only [hp])
    rw [integral_const_mul] at hlo hhi
    exact ⟨hlo,hhi⟩

def ratio (n : ℕ) (x : Ω) : ℝ := power μ k (n+1) x/power μ k n x

include hk hm hb in
theorem ratio_bounds (n : ℕ) (x : Ω) : m ≤ ratio μ k n x ∧ ratio μ k n x ≤ M := by
  have he := power_successor_bounds μ k m M hk hm hb n x
  have hp := power_pos μ k m M hk hm hb n x
  exact ⟨(le_div_iff₀ hp).mpr he.1,(div_le_iff₀ hp).mpr he.2⟩

include hk in
theorem ratio_measurable (n : ℕ) : Measurable (ratio μ k n) :=
  (power_measurable μ k hk (n+1)).div (power_measurable μ k hk n)


include hk hm hb in
private theorem power_integrable (n : ℕ) : Integrable (power μ k n) μ := by
  apply Integrable.of_bound (power_measurable μ k hk n).aestronglyMeasurable (M^n)
  filter_upwards with y
  rw [Real.norm_eq_abs,abs_of_pos (power_pos μ k m M hk hm hb n y)]
  exact (power_bounds μ k m M hk hm hb n y).2

include hk hm hb in
private theorem power_mass_pos (n : ℕ) :
    0 < SignedDensityProbabilitySampling.mass μ (power μ k n) := by
  have he := integral_mono (integrable_const (m^n))
    (power_integrable μ k m M hk hm hb n)
    (fun y => (power_bounds μ k m M hk hm hb n y).1)
  have hh : m^n ≤ ∫ y,power μ k n y ∂μ := by simpa using he
  unfold SignedDensityProbabilitySampling.mass
  simp_rw [abs_of_pos (power_pos μ k m M hk hm hb n _)]
  exact (pow_pos hm n).trans_le hh

include hk hm hb in
/-- Consecutive power ratios evolve by a genuine probability average with
reference law proportional to the PREVIOUS power, without a supplied vacuum. -/
theorem ratio_bridge (n : ℕ) (x : Ω) :
    ratio μ k (n+1) x = YMPositiveKernel.average
      (SignedDensityProbabilitySampling.sampler μ (power μ k n)) k (ratio μ k n) x := by
  have hp := power_mass_pos μ k m M hk hm hb n
  have hn (y : Ω) := (power_pos μ k m M hk hm hb n y).le
  have hden : (∫ y,power μ k n y*k x y ∂μ)=power μ k (n+1) x := by
    change (∫ y,power μ k n y*k x y ∂μ)=∫ y,k x y*power μ k n y ∂μ
    apply integral_congr_ae
    filter_upwards with y
    ring
  have hnum : (∫ y,power μ k n y*(k x y*ratio μ k n y) ∂μ)=
      power μ k (n+2) x := by
    change (∫ y,power μ k n y*(k x y*ratio μ k n y) ∂μ)=
      ∫ y,k x y*power μ k (n+1) y ∂μ
    apply integral_congr_ae
    filter_upwards with y
    unfold ratio
    field_simp [(power_pos μ k m M hk hm hb n y).ne']
  unfold YMPositiveKernel.average YMPositiveKernel.rowDensity
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div,YMPositiveKernel.mass]
  rw [YMPositiveKernel.positive_sampler_integral μ _ _ (power_measurable μ k hk n) hn hp,
    YMPositiveKernel.positive_sampler_integral μ _ _ (power_measurable μ k hk n) hn hp,
    hden,hnum]
  unfold ratio
  field_simp [hp.ne']

include hk hm hb in
private theorem average_affine (f : Ω → ℝ) (hf : Measurable f)
    (hfb : ∀ y,0 ≤ f y ∧ f y ≤ 1) (a b : ℝ) (x : Ω) :
    YMPositiveKernel.average μ k (fun y => a+b*f y) x=
      a+b*YMPositiveKernel.average μ k f x := by
  have hd := YMPositiveKernel.density_integrable μ k m M hm
    (fun w => hk.comp measurable_prodMk_left) hb x
  have hi : Integrable (fun y => YMPositiveKernel.rowDensity μ k x y*f y) μ := by
    have he := hd.bdd_mul hf.aestronglyMeasurable (c := 1) (by
      filter_upwards with y
      simpa [Real.norm_eq_abs,abs_of_nonneg (hfb y).1] using (hfb y).2)
    simpa only [mul_comm] using he
  have he : (fun y => YMPositiveKernel.rowDensity μ k x y*(a+b*f y))=
      (fun y => a*YMPositiveKernel.rowDensity μ k x y+
        b*(YMPositiveKernel.rowDensity μ k x y*f y)) := by funext y; ring
  unfold YMPositiveKernel.average
  rw [he,integral_add (hd.const_mul a) (hi.const_mul b),integral_const_mul,integral_const_mul,
    YMPositiveKernel.density_integral μ k m M hm (fun w => hk.comp measurable_prodMk_left) hb x]
  ring

include hk hm hb in
theorem average_reset_range (f : Ω → ℝ) (hf : Measurable f) (L U : ℝ)
    (hfb : ∀ y,L ≤ f y ∧ f y ≤ U) (x : Ω) :
    (1-m/M)*L ≤ YMPositiveKernel.average μ k f x-(m/M)*(∫ y,f y ∂μ) ∧
      YMPositiveKernel.average μ k f x-(m/M)*(∫ y,f y ∂μ) ≤ (1-m/M)*U := by
  have hLU : L ≤ U := by
    let y : Ω := Classical.choice inferInstance
    exact (hfb y).1.trans (hfb y).2
  by_cases h : L=U
  · have he : f=fun _ => L := by funext y; have hh := hfb y; rw [← h] at hh; linarith
    rw [he]
    have ha := average_affine μ k m M hk hm hb (fun _ => 0) measurable_const
      (fun _ => ⟨le_refl 0,by norm_num⟩) L 0 x
    simp only [zero_mul,add_zero] at ha
    rw [ha]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    rw [← h]
    constructor <;> linarith
  · have hp : 0 < U-L := sub_pos.mpr (lt_of_le_of_ne hLU h)
    let g : Ω → ℝ := fun y => (f y-L)/(U-L)
    have hg : Measurable g := (hf.sub_const L).div_const _
    have hgb (y : Ω) : 0 ≤ g y ∧ g y ≤ 1 :=
      ⟨div_nonneg (sub_nonneg.mpr (hfb y).1) hp.le,
        (div_le_one hp).mpr (sub_le_sub_right (hfb y).2 L)⟩
    have hi : Integrable g μ := by
      apply Integrable.of_bound hg.aestronglyMeasurable 1
      filter_upwards with y
      simpa [Real.norm_eq_abs,abs_of_nonneg (hgb y).1] using (hgb y).2
    have he : f=fun y => L+(U-L)*g y := by
      funext y
      dsimp [g]
      field_simp [hp.ne']
      <;> ring
    have ha : YMPositiveKernel.average μ k f x=L+(U-L)*YMPositiveKernel.average μ k g x := by
      rw [he]
      exact average_affine μ k m M hk hm hb g hg hgb L (U-L) x
    have hmoy : (∫ y,f y ∂μ)=L+(U-L)*(∫ y,g y ∂μ) := by
      rw [he,integral_add (integrable_const L) (hi.const_mul _),integral_const_mul]
      simp
    have hr := YMPositiveKernel.residual_bounds μ k m M hm
      (fun w => hk.comp measurable_prodMk_left) hb g hg hgb x
    rw [ha,hmoy]
    have hl := mul_nonneg hp.le hr.1
    have hu := mul_le_mul_of_nonneg_left hr.2 hp.le
    constructor <;> nlinarith

include hk hm hb in
/-- The exact ratio reset interval. Its reference measure changes with n;
ordinary power iteration is not mistaken for a stationary Markov chain. -/
theorem ratio_next_range (n : ℕ) (L U : ℝ)
    (hfb : ∀ y,L ≤ ratio μ k n y ∧ ratio μ k n y ≤ U) (x : Ω) :
    (m/M)*(∫ y,ratio μ k n y ∂SignedDensityProbabilitySampling.sampler μ (power μ k n))+
        (1-m/M)*L ≤ ratio μ k (n+1) x ∧
      ratio μ k (n+1) x ≤
        (m/M)*(∫ y,ratio μ k n y ∂SignedDensityProbabilitySampling.sampler μ (power μ k n))+
          (1-m/M)*U := by
  let ν := SignedDensityProbabilitySampling.sampler μ (power μ k n)
  letI : IsProbabilityMeasure ν := SignedDensityProbabilitySampling.sampler_probability μ _
    (power_integrable μ k m M hk hm hb n) (power_mass_pos μ k m M hk hm hb n)
  have he := average_reset_range ν k m M hk hm hb (ratio μ k n)
    (ratio_measurable μ k hk n) L U hfb x
  rw [ratio_bridge μ k m M hk hm hb n x]
  dsimp [ν] at he
  constructor <;> linarith [he.1,he.2]


def ratioMean (n : ℕ) : ℝ := ∫ y,ratio μ k n y
  ∂SignedDensityProbabilitySampling.sampler μ (power μ k n)

def enclosure : ℕ → ℝ × ℝ
  | 0 => (m,M)
  | n+1 => ((m/M)*ratioMean μ k n+(1-m/M)*(enclosure n).1,
      (m/M)*ratioMean μ k n+(1-m/M)*(enclosure n).2)

include hk hm hb in
theorem enclosure_contains (n : ℕ) (x : Ω) :
    (enclosure μ k m M n).1 ≤ ratio μ k n x ∧
      ratio μ k n x ≤ (enclosure μ k m M n).2 := by
  induction n generalizing x with
  | zero => exact ratio_bounds μ k m M hk hm hb 0 x
  | succ n ih => exact ratio_next_range μ k m M hk hm hb n _ _ ih x

theorem enclosure_width (n : ℕ) :
    (enclosure μ k m M n).2-(enclosure μ k m M n).1=(M-m)*(1-m/M)^n := by
  induction n with
  | zero => simp [enclosure]
  | succ n ih =>
    change (m/M)*ratioMean μ k n+(1-m/M)*(enclosure μ k m M n).2-
      ((m/M)*ratioMean μ k n+(1-m/M)*(enclosure μ k m M n).1)=_
    calc
      _ = (1-m/M)*((enclosure μ k m M n).2-(enclosure μ k m M n).1) := by ring
      _ = _ := by rw [ih,pow_succ]; ring

include hk hm hb in
private theorem ratioMean_in_range (n : ℕ) (L U : ℝ)
    (hfb : ∀ y,L ≤ ratio μ k n y ∧ ratio μ k n y ≤ U) :
    L ≤ ratioMean μ k n ∧ ratioMean μ k n ≤ U := by
  let ν := SignedDensityProbabilitySampling.sampler μ (power μ k n)
  letI : IsProbabilityMeasure ν := SignedDensityProbabilitySampling.sampler_probability μ _
    (power_integrable μ k m M hk hm hb n) (power_mass_pos μ k m M hk hm hb n)
  have hi : Integrable (ratio μ k n) ν := by
    apply Integrable.of_bound (ratio_measurable μ k hk n).aestronglyMeasurable M
    filter_upwards with y
    rw [Real.norm_eq_abs,abs_of_pos (hm.trans_le (ratio_bounds μ k m M hk hm hb n y).1)]
    exact (ratio_bounds μ k m M hk hm hb n y).2
  have hl := integral_mono (integrable_const L) hi (fun y => (hfb y).1)
  have hu := integral_mono hi (integrable_const U) (fun y => (hfb y).2)
  constructor
  · simpa [ratioMean,ν] using hl
  · simpa [ratioMean,ν] using hu

include hk hm hb in
theorem enclosure_nested (n : ℕ) :
    (enclosure μ k m M n).1 ≤ (enclosure μ k m M (n+1)).1 ∧
      (enclosure μ k m M (n+1)).2 ≤ (enclosure μ k m M n).2 := by
  have hr := ratioMean_in_range μ k m M hk hm hb n _ _
    (enclosure_contains μ k m M hk hm hb n)
  have hd : 0 ≤ m/M := (div_pos hm (upper_pos k m M hm hb)).le
  have h1 := mul_nonneg hd (sub_nonneg.mpr hr.1)
  have h2 := mul_nonneg hd (sub_nonneg.mpr hr.2)
  simp only [enclosure,Prod.fst,Prod.snd]
  constructor <;> nlinarith

include hk hm hb in
theorem ratio_increment (n : ℕ) (x : Ω) :
    |ratio μ k (n+1) x-ratio μ k n x| ≤ (M-m)*(1-m/M)^n := by
  have h0 := enclosure_contains μ k m M hk hm hb n x
  have h1 := enclosure_contains μ k m M hk hm hb (n+1) x
  have hn := enclosure_nested μ k m M hk hm hb n
  rw [← enclosure_width μ k m M n]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

include hk hm hb in
theorem ratio_cauchy (x : Ω) : CauchySeq (fun n => ratio μ k n x) := by
  have hr : 1-m/M < 1 := by have hp := div_pos hm (upper_pos k m M hm hb); linarith
  apply cauchySeq_of_le_geometric (1-m/M) (M-m) hr
  intro n
  simpa [Real.dist_eq,abs_sub_comm] using ratio_increment μ k m M hk hm hb n x

include hk hm hb in
theorem ratio_limit_exists (x : Ω) : ∃ lam : ℝ, m ≤ lam ∧ lam ≤ M ∧
    Filter.Tendsto (fun n => ratio μ k n x) Filter.atTop (nhds lam) := by
  obtain ⟨lam,hlim⟩ := cauchySeq_tendsto_of_complete (ratio_cauchy μ k m M hk hm hb x)
  refine ⟨lam,?_,?_,hlim⟩
  · exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun n =>
      (ratio_bounds μ k m M hk hm hb n x).1)
  · exact le_of_tendsto hlim (Filter.Eventually.of_forall fun n =>
      (ratio_bounds μ k m M hk hm hb n x).2)


include hk hm hb in
private theorem power_comparison (n : ℕ) (x z : Ω) :
    m*power μ k n x ≤ M*power μ k n z := by
  cases n with
  | zero =>
    simp only [power,mul_one]
    exact (hb x z).1.trans (hb x z).2
  | succ n =>
    have hi := integral_mono ((power_integrand μ k m M hk hm hb n x).const_mul m)
      ((power_integrand μ k m M hk hm hb n z).const_mul M) (fun y => by
        have h1 := mul_le_mul_of_nonneg_left (hb x y).2 hm.le
        have h2 := mul_le_mul_of_nonneg_left (hb z y).1 (upper_pos k m M hm hb).le
        have hh : m*k x y ≤ M*k z y := by nlinarith only [h1,h2]
        have h3 := mul_le_mul_of_nonneg_right hh (power_pos μ k m M hk hm hb n y).le
        nlinarith only [h3])
    change m*(∫ y,k x y*power μ k n y ∂μ) ≤ M*(∫ y,k z y*power μ k n y ∂μ)
    simpa only [integral_const_mul] using hi

def normalized (x0 : Ω) (n : ℕ) (x : Ω) : ℝ := power μ k n x/power μ k n x0

include hk hm hb in
theorem normalized_bounds (x0 : Ω) (n : ℕ) (x : Ω) :
    m/M ≤ normalized μ k x0 n x ∧ normalized μ k x0 n x ≤ M/m := by
  have hM := upper_pos k m M hm hb
  have h0 := power_pos μ k m M hk hm hb n x0
  constructor
  · apply (div_le_div_iff₀ hM h0).mpr
    simpa only [mul_comm] using power_comparison μ k m M hk hm hb n x0 x
  · apply (div_le_div_iff₀ h0 hm).mpr
    simpa only [mul_comm] using power_comparison μ k m M hk hm hb n x x0

include hk hm hb in
private theorem normalized_pos (x0 : Ω) (n : ℕ) (x : Ω) : 0 < normalized μ k x0 n x :=
  (div_pos hm (upper_pos k m M hm hb)).trans_le (normalized_bounds μ k m M hk hm hb x0 n x).1

include hk hm hb in
private theorem normalized_successor (x0 : Ω) (n : ℕ) (x : Ω) :
    normalized μ k x0 (n+1) x=
      normalized μ k x0 n x*(ratio μ k n x/ratio μ k n x0) := by
  unfold normalized ratio
  field_simp [(power_pos μ k m M hk hm hb n x0).ne',
    (power_pos μ k m M hk hm hb n x).ne',(power_pos μ k m M hk hm hb (n+1) x0).ne']

include hk hm hb in
theorem normalized_increment (x0 : Ω) (n : ℕ) (x : Ω) :
    |normalized μ k x0 (n+1) x-normalized μ k x0 n x| ≤
      ((M/m)*(M-m)/m)*(1-m/M)^n := by
  have hq0 : 0 < ratio μ k n x0 := hm.trans_le (ratio_bounds μ k m M hk hm hb n x0).1
  have hp := normalized_pos μ k m M hk hm hb x0 n x
  have hw : 0 ≤ (M-m)*(1-m/M)^n := by
    rw [← enclosure_width μ k m M n]
    have he := enclosure_contains μ k m M hk hm hb n x
    linarith
  have hd : |ratio μ k n x-ratio μ k n x0| ≤ (M-m)*(1-m/M)^n := by
    rw [← enclosure_width μ k m M n]
    have hx := enclosure_contains μ k m M hk hm hb n x
    have h0 := enclosure_contains μ k m M hk hm hb n x0
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hn := mul_le_mul (normalized_bounds μ k m M hk hm hb x0 n x).2 hd
    (abs_nonneg _) (div_pos (upper_pos k m M hm hb) hm).le
  have he : normalized μ k x0 (n+1) x-normalized μ k x0 n x=
      normalized μ k x0 n x*(ratio μ k n x-ratio μ k n x0)/ratio μ k n x0 := by
    rw [normalized_successor μ k m M hk hm hb x0 n x]
    field_simp [hq0.ne']
  rw [he,abs_div,abs_mul,abs_of_pos hp,abs_of_pos hq0]
  calc
    _ ≤ ((M/m)*((M-m)*(1-m/M)^n))/ratio μ k n x0 :=
      div_le_div_of_nonneg_right hn hq0.le
    _ ≤ ((M/m)*((M-m)*(1-m/M)^n))/m :=
      div_le_div_of_nonneg_left (mul_nonneg (div_pos (upper_pos k m M hm hb) hm).le hw)
        hm (ratio_bounds μ k m M hk hm hb n x0).1
    _ = _ := by ring

include hk hm hb in
theorem normalized_cauchy (x0 x : Ω) : CauchySeq (fun n => normalized μ k x0 n x) := by
  have hr : 1-m/M < 1 := by have hp := div_pos hm (upper_pos k m M hm hb); linarith
  apply cauchySeq_of_le_geometric (1-m/M) ((M/m)*(M-m)/m) hr
  intro n
  simpa [Real.dist_eq,abs_sub_comm] using normalized_increment μ k m M hk hm hb x0 n x


include hk hm hb in
private theorem normalized_apply (x0 : Ω) (n : ℕ) (x : Ω) :
    applyKernel μ k (normalized μ k x0 n) x=
      ratio μ k n x0*normalized μ k x0 (n+1) x := by
  unfold applyKernel normalized
  simp_rw [← mul_div_assoc]
  rw [integral_div]
  change power μ k (n+1) x/power μ k n x0=_
  unfold ratio
  field_simp [(power_pos μ k m M hk hm hb n x0).ne',
    (power_pos μ k m M hk hm hb (n+1) x0).ne']

include hk hm hb in
/-- Actual uniformly positive measurable eigenfunction from normalized positive
kernel powers. Bounds are finite-volume bounds and need not survive a limit. -/
theorem positive_eigenfunction_exists (x0 : Ω) :
    ∃ lam : ℝ, ∃ ψ : Ω → ℝ, m ≤ lam ∧ lam ≤ M ∧ Measurable ψ ∧
      (∀ x,m/M ≤ ψ x ∧ ψ x ≤ M/m) ∧ (∀ x,applyKernel μ k ψ x=lam*ψ x) := by
  let ψ : Ω → ℝ := fun x => Filter.limUnder Filter.atTop (fun n => normalized μ k x0 n x)
  have hlim (x : Ω) : Filter.Tendsto (fun n => normalized μ k x0 n x)
      Filter.atTop (nhds (ψ x)) := (normalized_cauchy μ k m M hk hm hb x0 x).tendsto_limUnder
  have hmeas : Measurable ψ := measurable_of_tendsto_metrizable
    (fun n => (power_measurable μ k hk n).div_const _) (tendsto_pi_nhds.mpr hlim)
  have hbounds (x : Ω) : m/M ≤ ψ x ∧ ψ x ≤ M/m := by
    exact ⟨ge_of_tendsto (hlim x) (Filter.Eventually.of_forall fun n =>
        (normalized_bounds μ k m M hk hm hb x0 n x).1),
      le_of_tendsto (hlim x) (Filter.Eventually.of_forall fun n =>
        (normalized_bounds μ k m M hk hm hb x0 n x).2)⟩
  obtain ⟨lam,hl,hU,hlam⟩ := ratio_limit_exists μ k m M hk hm hb x0
  refine ⟨lam,ψ,hl,hU,hmeas,hbounds,?_⟩
  intro x
  have hi := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : Ω => M*(M/m))
    (F := fun n y => k x y*normalized μ k x0 n y) (f := fun y => k x y*ψ y)
    (fun n => ((hk.comp measurable_prodMk_left).mul
      ((power_measurable μ k hk n).div_const _)).aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun y => by
      change ‖k x y*normalized μ k x0 n y‖ ≤ M*(M/m)
      rw [Real.norm_eq_abs,abs_of_pos (mul_pos (hm.trans_le (hb x y).1)
        (normalized_pos μ k m M hk hm hb x0 n y))]
      exact mul_le_mul (hb x y).2 (normalized_bounds μ k m M hk hm hb x0 n y).2
        (normalized_pos μ k m M hk hm hb x0 n y).le (upper_pos k m M hm hb).le)
    (Filter.Eventually.of_forall fun y => tendsto_const_nhds.mul (hlim y))
  have he : Filter.Tendsto (fun n => applyKernel μ k (normalized μ k x0 n) x)
      Filter.atTop (nhds (lam*ψ x)) := by
    simp_rw [normalized_apply μ k m M hk hm hb x0]
    exact hlam.mul ((hlim x).comp (Filter.tendsto_add_atTop_nat 1))
  exact tendsto_nhds_unique hi he

end OperatorDerivativeRewrite.Foundation.YMPositivePower
