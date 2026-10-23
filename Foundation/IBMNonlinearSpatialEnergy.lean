import Foundation.IBMCanonicalMollifiedScenery
import Foundation.PositiveMollifierL2Contraction

/-! Scale-independent spatial L2 energy of original nonlinear source-column
integrals on finite intervals. The nonzero Gaussian covariance correction is
retained in the interval-length dependent bound. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearSpatialEnergy
open InfiniteGaussian IBMMollifier IBMFoldedTransitionBound
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem overlap_product_integrable (n m : ℕ) (r : ℝ) :
    Integrable (fun p : ℝ × ℝ => kernel n (r-p.1)*kernel m (p.2-p.1))
      (volume.prod volume) := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ =>
      kernel n (r-p.1)*kernel m (p.2-p.1)) :=
    (((kernel_smooth n).continuous.comp (continuous_const.sub continuous_fst)).mul
      ((kernel_smooth m).continuous.comp (continuous_snd.sub continuous_fst))).stronglyMeasurable
  have hrev (x : ℝ) : Integrable (fun q => kernel m (q-x)) := by
    have he : (fun q => kernel m (q-x)) = fun q => kernel m (x-q) :=
      funext fun q => IBMClockOccupationConvolution.kernel_sub_swap m q x
    rw [he]
    exact shifted_integrable m x
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun x => (hrev x).const_mul (kernel n (r-x))
  · have he : (fun x => ∫ q, ‖kernel n (r-x)*kernel m (q-x)‖) =
        fun x => kernel n (r-x) := by
      funext x
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg _ _),
        integral_const_mul, PositiveMollifierL2Contraction.reverse_shifted_mass, mul_one]
    rw [he]
    exact shifted_integrable n r

theorem overlap_row_integrable (n m : ℕ) (r : ℝ) : Integrable (overlap n m r) := by
  change Integrable (fun q => ∫ x, kernel n (r-x)*kernel m (q-x)) volume
  exact (overlap_product_integrable n m r).integral_prod_right

theorem overlap_row_mass (n m : ℕ) (r : ℝ) : (∫ q, overlap n m r q) = 1 := by
  unfold overlap
  rw [← integral_integral_swap (overlap_product_integrable n m r)]
  simp only [integral_const_mul, PositiveMollifierL2Contraction.reverse_shifted_mass,
    mul_one, shifted_mass]

theorem overlap_symmetric (n : ℕ) (r q : ℝ) : overlap n n r q = overlap n n q r := by
  unfold overlap
  congr 1
  funext x
  exact mul_comm _ _

/-- The original nonlinear covariance envelope has this finite-window row bound. -/
theorem covariance_row_bound (n : ℕ) (a b r : ℝ) (hab : a ≤ b) :
    (∫ q in Ioc a b, overlap n n r q+4) ≤ 1+4*(b-a) := by
  have hi : IntegrableOn (overlap n n r) (Ioc a b) volume :=
    (overlap_row_integrable n n r).integrableOn
  rw [integral_add hi (integrable_const 4), integral_const]
  have hm : (volume.restrict (Ioc a b)).real univ = b-a := by
    simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hm]
  have hb : (∫ q in Ioc a b, overlap n n r q) ≤ 1 := by
    simpa only [overlap_row_mass] using setIntegral_le_integral
      (overlap_row_integrable n n r) (ae_of_all _ fun q => overlap_nonneg n n r q)
  change _ + (b-a)*4 ≤ _
  linarith

theorem weighted_column_integrable_of_memLp (n : ℕ) (φ : ℝ → ℝ) (a b : ℝ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc a b))) :
    IntegrableOn (fun r => φ r • IBMNonlinearClockColumn.column n r) (Ioc a b) volume := by
  obtain ⟨C,hC,hb⟩ := IBMNonlinearClockColumn.column_bounded n
  have hi := (hφ.integrable (by norm_num)).norm.mul_const C
  apply hi.mono'
    (hφ.aestronglyMeasurable.smul
      (IBMNonlinearClockColumn.column_stronglyMeasurable n).aestronglyMeasurable)
  exact ae_of_all _ fun r => by
    change ‖φ r • IBMNonlinearClockColumn.column n r‖ ≤ ‖φ r‖ * C
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hb r) (norm_nonneg _)

def majorant (n : ℕ) (φ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (φ p.1)^2 * (overlap n n p.1 p.2 + 4)

theorem majorant_integrable (n : ℕ) (φ : ℝ → ℝ) (a b : ℝ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc a b))) :
    Integrable (majorant n φ) ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  obtain ⟨M,hM,hb⟩ := overlap_bounded n n
  have hi : Integrable (fun r => (φ r)^2) μ :=
    hφ.integrable_sq
  have hprod := hi.mul_prod (integrable_const (M+4) : Integrable (fun _ : ℝ => M+4) μ)
  apply hprod.mono'
    ((hφ.aestronglyMeasurable.comp_fst.pow 2).mul
      ((overlap_continuous n n).add continuous_const).aestronglyMeasurable)
  exact ae_of_all _ fun p => by
    change ‖(φ p.1)^2 * (overlap n n p.1 p.2+4)‖ ≤ (φ p.1)^2*(M+4)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (add_nonneg (overlap_nonneg n n p.1 p.2) (by norm_num)))]
    exact mul_le_mul_of_nonneg_left (by linarith [hb p.1 p.2]) (sq_nonneg _)

theorem majorant_integral_le (n : ℕ) (φ : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b) (hφ : MemLp φ 2 (volume.restrict (Ioc a b))) :
    (∫ p, majorant n φ p ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) ≤
      (1+4*(b-a)) * (∫ r in Ioc a b, (φ r)^2) := by
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  rw [integral_prod _ (majorant_integrable n φ a b hφ)]
  change (∫ r, ∫ q, majorant n φ (r,q) ∂μ ∂μ) ≤ _
  have he (r : ℝ) : (∫ q, majorant n φ (r,q) ∂μ) =
      (φ r)^2 * (∫ q in Ioc a b, overlap n n r q+4) := by
    change (∫ q, (φ r)^2 * (overlap n n r q+4) ∂μ) = _
    exact integral_const_mul _ _
  simp_rw [he]
  calc
    _ ≤ ∫ r, (φ r)^2 * (1+4*(b-a)) ∂μ := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun r => mul_nonneg (sq_nonneg _) (integral_nonneg fun q => by
          exact add_nonneg (overlap_nonneg n n r q) (by norm_num)))
        (hφ.integrable_sq.mul_const _)
      exact ae_of_all _ fun r => mul_le_mul_of_nonneg_left
        (covariance_row_bound n a b r hab) (sq_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

/-- Schur energy estimate for the ACTUAL nonlinear Gaussian columns. The
constant retains the covariance correction and is independent of mollifier width. -/
theorem original_energy_le_of_memLp (n : ℕ) (φ : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b) (hφ : MemLp φ 2 (volume.restrict (Ioc a b))) :
    ‖∫ r in a..b, φ r • IBMNonlinearClockColumn.column n r‖^2 ≤
      (1+4*(b-a)) * (∫ r in a..b, (φ r)^2) := by
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  let f : ℝ → GaussianL2 := fun r => φ r • IBMNonlinearClockColumn.column n r
  have hf : Integrable f μ := weighted_column_integrable_of_memLp n φ a b hφ
  have hk : Integrable (fun p : ℝ × ℝ => inner ℝ (f p.1) (f p.2)) (μ.prod μ) :=
    (hf.norm.mul_prod hf.norm).mono'
      (hf.aestronglyMeasurable.comp_fst.inner (𝕜 := ℝ) hf.aestronglyMeasurable.comp_snd)
      (ae_of_all _ fun p => norm_inner_le_norm _ _)
  have he : ‖∫ r, f r ∂μ‖^2 =
      ∫ p : ℝ × ℝ, inner ℝ (f p.1) (f p.2) ∂μ.prod μ := by
    rw [← real_inner_self_eq_norm_sq, real_inner_comm, ← integral_inner hf, integral_prod _ hk]
    apply integral_congr_ae
    exact ae_of_all _ fun r => by
      change inner ℝ (∫ q, f q ∂μ) (f r) = ∫ q, inner ℝ (f r) (f q) ∂μ
      rw [real_inner_comm, ← integral_inner hf]
  have hm := majorant_integrable n φ a b hφ
  have hpoint (p : ℝ × ℝ) : inner ℝ (f p.1) (f p.2) ≤
      (majorant n φ p + majorant n φ p.swap)/2 := by
    have hκ : 0 ≤ overlap n n p.1 p.2+4 :=
      add_nonneg (overlap_nonneg n n p.1 p.2) (by norm_num)
    have hinner := IBMNonlinearClockColumn.column_inner_bound n n p.1 p.2
    have habs : abs (φ p.1)*abs (φ p.2) ≤ ((φ p.1)^2+(φ p.2)^2)/2 := by
      nlinarith [sq_nonneg (abs (φ p.1)-abs (φ p.2)),sq_abs (φ p.1),sq_abs (φ p.2)]
    have hfirst : inner ℝ (f p.1) (f p.2) ≤
        (abs (φ p.1)*abs (φ p.2)) * (overlap n n p.1 p.2+4) := by
      calc
        _ ≤ |inner ℝ (f p.1) (f p.2)| := le_abs_self _
        _ = (abs (φ p.1)*abs (φ p.2)) *
            |inner ℝ (IBMNonlinearClockColumn.column n p.1)
              (IBMNonlinearClockColumn.column n p.2)| := by
          simp only [f, real_inner_smul_left, inner_smul_right, abs_mul]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinner (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hlast := mul_le_mul_of_nonneg_right habs hκ
    have hsym := overlap_symmetric n p.2 p.1
    dsimp only [majorant, Prod.fst_swap, Prod.snd_swap]
    rw [hsym]
    nlinarith
  simp only [intervalIntegral.integral_of_le hab]
  change ‖∫ r, f r ∂μ‖^2 ≤ _
  calc
    _ = ∫ p : ℝ × ℝ, inner ℝ (f p.1) (f p.2) ∂μ.prod μ := he
    _ ≤ ∫ p : ℝ × ℝ, (majorant n φ p + majorant n φ p.swap)/2 ∂μ.prod μ :=
      integral_mono hk ((hm.add hm.swap).div_const 2) hpoint
    _ = ∫ p : ℝ × ℝ, majorant n φ p ∂μ.prod μ := by
      rw [integral_div]
      rw [integral_add (f := fun p => majorant n φ p)
        (g := fun p => majorant n φ p.swap) hm hm.swap]
      rw [integral_prod_swap]
      ring
    _ ≤ _ := majorant_integral_le n φ hab hφ

theorem original_energy_le (n : ℕ) (φ : ℝ → ℝ) (hc : Continuous φ)
    {a b : ℝ} (hab : a ≤ b) :
    ‖∫ r in a..b, φ r • IBMNonlinearClockColumn.column n r‖^2 ≤
      (1+4*(b-a)) * (∫ r in a..b, (φ r)^2) :=
  original_energy_le_of_memLp n φ hab
    ((memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
      ((hc.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self))

/-- The SAME actual Brownian sine distribution inherits spatial-L2 test control. -/
theorem limit_energy_le (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (ha : φ a = 0) (hb : φ b = 0) :
    ‖IBMSineSpatialDistribution.sourceClass φ hφ hab none‖^2 ≤
      (1+4*(b-a)) * (∫ r in a..b, (φ r)^2) :=
  le_of_tendsto ((IBMCanonicalMollifiedScenery.original_bochner_tendsto φ hφ hab ha hb).norm.pow 2)
    (Eventually.of_forall fun n => original_energy_le n φ hφ.continuous hab)

end OperatorDerivativeRewrite.Foundation.IBMNonlinearSpatialEnergy
