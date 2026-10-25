import Foundation.GaussianObservedSecondRegularization
import Foundation.GaussianClockSourceSpectral
import Foundation.IBMClockBochnerConverse
import Foundation.BochnerL2Dominated

/-! Correlations of existing Gaussian observation isometries and their full
source-valued energy series. The comparison is the actual bounded J_u^* J_v;
Hermite and original clock-sector identifications use complete L2 density.
No new semigroup completion or fractional-domain equivalence is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation
open InfiniteGaussian GaussianConditionalCompactness
open IBMClockObservationGraph GaussianObservedSecondRegularization

theorem normalized_cross (u v : CoefficientSpace) (n m : ℕ) :
    inner ℝ (normalizedWick u n) (normalizedWick v m) =
      if n=m then (inner ℝ u v)^n else 0 := by
  simp only [normalizedWick,real_inner_smul_left,real_inner_smul_right,
    GaussianTimeSpaceHermite.wick_inner]
  by_cases hn : n=m
  · subst m
    have hp : Real.sqrt (n.factorial : ℝ) ≠ 0 := by positivity
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ n.factorial by positivity)
    field_simp
    rw [hs]
    simp
  · simp [hn]

def correlation (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    GaussianCore.GaussianL2 →L[ℝ] GaussianCore.GaussianL2 :=
  (pullback u hu).toContinuousLinearMap.adjoint.comp (pullback v hv).toContinuousLinearMap

theorem correlation_hermite (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (n : ℕ) : correlation u v hu hv (GaussianCore.normalizedHermite n) =
      (inner ℝ u v)^n • GaussianCore.normalizedHermite n := by
  apply GaussianCore.hermiteBasis.repr.injective
  ext m
  simp only [GaussianCore.hermiteBasis_coefficient,correlation,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,inner_smul_right,
    ]
  change inner ℝ (pullback u hu (GaussianCore.normalizedHermite m))
    (pullback v hv (GaussianCore.normalizedHermite n)) = _
  rw [pullback_normalizedHermite,pullback_normalizedHermite,normalized_cross]
  have hh := (orthonormal_iff_ite.mp GaussianCore.normalizedHermite_orthonormal) m n
  rw [hh]
  split_ifs with hm
  · subst n
    simp
  · simp

end OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation

namespace OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation
open InfiniteGaussian GaussianConditionalCompactness IBMClockObservationGraph
open GaussianObservedSecondRegularization

theorem correlation_adjoint (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (correlation u v hu hv).adjoint = correlation v u hv hu := by
  simp only [correlation,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

theorem correlation_coefficient (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (f : GaussianCore.GaussianL2) (n : ℕ) :
    GaussianCore.hermiteCoefficient (correlation u v hu hv f) n =
      (inner ℝ u v)^n * GaussianCore.hermiteCoefficient f n := by
  unfold GaussianCore.hermiteCoefficient
  rw [← (correlation u v hu hv).adjoint_inner_left f (GaussianCore.normalizedHermite n),
    correlation_adjoint,correlation_hermite,real_inner_smul_left,real_inner_comm v u]

theorem correlation_inner_hasSum (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (f : GaussianCore.GaussianL2) :
    HasSum (fun n => (inner ℝ u v)^n * GaussianCore.hermiteCoefficient f n^2)
      (inner ℝ f (correlation u v hu hv f)) := by
  have hs := GaussianCore.hermiteBasis.hasSum_inner_mul_inner f (correlation u v hu hv f)
  convert hs using 1
  ext n
  rw [GaussianCore.hermiteBasis_apply]
  change _ = inner ℝ f (GaussianCore.normalizedHermite n) *
    GaussianCore.hermiteCoefficient (correlation u v hu hv f) n
  rw [correlation_coefficient]
  unfold GaussianCore.hermiteCoefficient
  have hh : inner ℝ f (GaussianCore.normalizedHermite n) =
      inner ℝ (GaussianCore.normalizedHermite n) f := real_inner_comm _ _
  rw [hh]
  ring

theorem noise_energy_hasSum (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (f : GaussianCore.GaussianL2) :
    HasSum (fun n => 2*(1-(inner ℝ u v)^n)*GaussianCore.hermiteCoefficient f n^2)
      (‖pullback u hu f-pullback v hv f‖^2) := by
  have hs := ((GaussianCore.hermiteCoefficient_hasSum_sq f).mul_left 2).sub
    ((correlation_inner_hasSum u v hu hv f).mul_left 2)
  convert hs using 1
  · ext n
    ring
  · rw [norm_sub_sq_real,(pullback u hu).norm_map,(pullback v hv).norm_map]
    have hi := (pullback u hu).toContinuousLinearMap.adjoint_inner_right f (pullback v hv f)
    change inner ℝ f (correlation u v hu hv f) = inner ℝ (pullback u hu f) (pullback v hv f) at hi
    rw [← hi]
    ring

end OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation


namespace OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation
open InfiniteGaussian IBMClockObservationGraph IBMClockBochnerConverse
open ProductL2Curry BochnerClosedOperator
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

abbrev Section := Lp GaussianL2 2 GaussianCore.γ
abbrev SourceSections := Lp GaussianCore.GaussianL2 2 gaussianProduct

private theorem fieldPullback_tensor (u : CoefficientSpace) (hu : ‖u‖ = 1)
    (a : GaussianCore.GaussianL2) (b : GaussianL2) :
    fieldPullback u hu (tensor GaussianCore.γ a b) =
      tensor gaussianProduct (pullback u hu a) b := by
  have hmp := observation_measurePreserving u hu
  have ht := hmp.quasiMeasurePreserving.ae_eq_comp (tensor_coeFn GaussianCore.γ a b)
  apply Lp.ext
  filter_upwards [fieldPullback_ae u hu (tensor GaussianCore.γ a b),ht,
    tensor_coeFn gaussianProduct (pullback u hu a) b,pullback_ae u hu a]
    with ω hf ht hT ha
  simp only [Function.comp_def] at ht
  rw [hf,ht,hT,ha]

theorem flip_fieldPullback (u : CoefficientSpace) (hu : ‖u‖ = 1) (F : Section) :
    flip gaussianProduct gaussianProduct (fieldPullback u hu F) =
      (pullback u hu).toContinuousLinearMap.compLpL 2 gaussianProduct
        (flip GaussianCore.γ gaussianProduct F) := by
  let L := (flip gaussianProduct gaussianProduct).toContinuousLinearMap.comp
    (fieldPullback u hu).toContinuousLinearMap
  let M := ((pullback u hu).toContinuousLinearMap.compLpL 2 gaussianProduct).comp
    (flip GaussianCore.γ gaussianProduct).toContinuousLinearMap
  have ht (a : GaussianCore.GaussianL2) (b : GaussianL2) :
      L (tensor GaussianCore.γ a b) = M (tensor GaussianCore.γ a b) := by
    change flip gaussianProduct gaussianProduct (fieldPullback u hu (tensor GaussianCore.γ a b)) =
      (pullback u hu).toContinuousLinearMap.compLpL 2 gaussianProduct
        (flip GaussianCore.γ gaussianProduct (tensor GaussianCore.γ a b))
    rw [fieldPullback_tensor,flip_tensor,flip_tensor]
    exact (BochnerLinearIsometry.lift_tensor gaussianProduct (pullback u hu) b a).symm
  have he : ∀ f : Section, L f = M f := by
    apply Lp.induction (by simp) (fun f : Section => L f = M f)
    · intro b s hs hfin
      change L (indicatorConstLp 2 hs hfin.ne b) = M (indicatorConstLp 2 hs hfin.ne b)
      rw [indicatorConstLp_eq_toSpanSingleton_compLp]
      exact ht (indicatorConstLp 2 hs hfin.ne (1:ℝ)) b
    · intro f g hf hg hd hF hG
      simp only [map_add,hF,hG]
    · exact isClosed_eq L.continuous M.continuous
  exact he F

end OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation


namespace OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation
open InfiniteGaussian IBMClockObservationGraph
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def difference (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    GaussianCore.GaussianL2 →L[ℝ] GaussianL2 :=
  (pullback u hu).toContinuousLinearMap-(pullback v hv).toContinuousLinearMap

def coefficientField (n : ℕ) (G : SourceSections) : GaussianL2 :=
  (innerSL ℝ (GaussianCore.normalizedHermite n)).compLpL 2 gaussianProduct G

private theorem coefficientField_energy (n : ℕ) (G : SourceSections) :
    ‖coefficientField n G‖^2 =
      ∫ x, GaussianCore.hermiteCoefficient (G x) n^2 ∂gaussianProduct := by
  rw [BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [(innerSL ℝ (GaussianCore.normalizedHermite n)).coeFn_compLpL G] with x hx
  change coefficientField n G x = _ at hx
  rw [hx]
  simp only [innerSL_apply_apply,Real.norm_eq_abs,sq_abs,GaussianCore.hermiteCoefficient]

private theorem source_noise_energy_hasSum (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (G : SourceSections) :
    HasSum (fun n => 2*(1-(inner ℝ u v)^n)*‖coefficientField n G‖^2)
      (‖(difference u v hu hv).compLpL 2 gaussianProduct G‖^2) := by
  let w : ℕ → ℝ := fun n => 2*(1-(inner ℝ u v)^n)
  have hρ : |inner ℝ u v| ≤ 1 := by
    simpa only [hu,hv,one_mul] using abs_real_inner_le_norm u v
  have hw (n : ℕ) : 0 ≤ w n := by
    have hp : |(inner ℝ u v)^n| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hρ
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr ((le_abs_self _).trans hp))
  let D := difference u v hu hv
  have hc (x : SampleSpace) :
      HasSum (fun n => w n*GaussianCore.hermiteCoefficient (G x) n^2) (‖D (G x)‖^2) :=
    noise_energy_hasSum u v hu hv (G x)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x => w n*GaussianCore.hermiteCoefficient (G x) n^2) gaussianProduct := by
    have hf : Continuous (fun f : GaussianCore.GaussianL2 =>
        w n*GaussianCore.hermiteCoefficient f n^2) := by
      unfold GaussianCore.hermiteCoefficient
      fun_prop
    exact hf.comp_aestronglyMeasurable (Lp.aestronglyMeasurable G)
  have hD : Integrable (fun x => ‖D (G x)‖^2) gaussianProduct := by
    have hi := (Lp.memLp (D.compLpL 2 gaussianProduct G)).norm.integrable_sq
    apply hi.congr
    filter_upwards [D.coeFn_compLpL G] with x hx
    rw [hx]
  have hepoint : (fun x => ∑' n, w n*GaussianCore.hermiteCoefficient (G x) n^2) =
      fun x => ‖D (G x)‖^2 := funext fun x => (hc x).tsum_eq
  have hs := hasSum_integral_of_dominated_convergence
    (μ := gaussianProduct)
    (F := fun n x => w n*GaussianCore.hermiteCoefficient (G x) n^2)
    (f := fun x => ‖D (G x)‖^2)
    (fun n x => w n*GaussianCore.hermiteCoefficient (G x) n^2) hm
    (fun n => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw n) (sq_nonneg _))])
    (ae_of_all _ fun x => (hc x).summable) (by rw [hepoint];exact hD)
    (ae_of_all _ fun x => hc x)
  have he (n : ℕ) :
      (∫ x, w n*GaussianCore.hermiteCoefficient (G x) n^2 ∂gaussianProduct) =
        w n*‖coefficientField n G‖^2 := by
    rw [integral_const_mul,coefficientField_energy]
  have hf : (∫ x, ‖D (G x)‖^2 ∂gaussianProduct) =
      ‖D.compLpL 2 gaussianProduct G‖^2 := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [D.coeFn_compLpL G] with x hx
    rw [hx]
  simpa only [he,hf] using hs

end OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation


namespace OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation
open InfiniteGaussian IBMClockObservationGraph IBMClockBochnerConverse ProductL2Curry
open GaussianConditionalCompactness GaussianObservedSecondRegularization
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

private theorem difference_compLp (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (G : SourceSections) :
    (difference u v hu hv).compLpL 2 gaussianProduct G =
      (pullback u hu).toContinuousLinearMap.compLpL 2 gaussianProduct G-
        (pullback v hv).toContinuousLinearMap.compLpL 2 gaussianProduct G := by
  apply Lp.ext
  filter_upwards [(difference u v hu hv).coeFn_compLpL G,
    (pullback u hu).toContinuousLinearMap.coeFn_compLpL G,
    (pullback v hv).toContinuousLinearMap.coeFn_compLpL G,
    Lp.coeFn_sub ((pullback u hu).toContinuousLinearMap.compLpL 2 gaussianProduct G)
      ((pullback v hv).toContinuousLinearMap.compLpL 2 gaussianProduct G)] with x hD hu hv hs
  rw [hD,hs]
  simp only [Pi.sub_apply,hu,hv,difference,_root_.sub_apply]

theorem field_noise_energy_hasSum (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (F : Section) :
    HasSum (fun n => 2*(1-(inner ℝ u v)^n)*
      ‖coefficientField n (flip GaussianCore.γ gaussianProduct F)‖^2)
      (‖fieldPullback u hu F-fieldPullback v hv F‖^2) := by
  have hs := source_noise_energy_hasSum u v hu hv
    (flip GaussianCore.γ gaussianProduct F)
  have he : (difference u v hu hv).compLpL 2 gaussianProduct
      (flip GaussianCore.γ gaussianProduct F) =
        flip gaussianProduct gaussianProduct (fieldPullback u hu F-fieldPullback v hv F) := by
    rw [difference_compLp,map_sub,flip_fieldPullback,flip_fieldPullback]
  rw [he,(flip gaussianProduct gaussianProduct).norm_map] at hs
  exact hs

def hermiteProjection (n : ℕ) : GaussianCore.GaussianL2 →L[ℝ] GaussianCore.GaussianL2 :=
  (innerSL ℝ (GaussianCore.normalizedHermite n)).smulRight (GaussianCore.normalizedHermite n)

private theorem hermiteProjection_apply (n : ℕ) (f : GaussianCore.GaussianL2) :
    hermiteProjection n f = GaussianCore.hermiteCoefficient f n • GaussianCore.normalizedHermite n := rfl

private theorem hermiteProjection_basis (n m : ℕ) :
    hermiteProjection n (GaussianCore.normalizedHermite m) =
      if n=m then GaussianCore.normalizedHermite m else 0 := by
  rw [hermiteProjection_apply,GaussianCore.hermiteCoefficient,
    (orthonormal_iff_ite.mp GaussianCore.normalizedHermite_orthonormal) n m]
  split_ifs with hnm <;> simp [hnm]

private theorem projection_pullback_basis (u : CoefficientSpace) (hu : ‖u‖ = 1) (n m : ℕ) :
    GaussianNumberSectors.projection n (pullback u hu (GaussianCore.normalizedHermite m)) =
      pullback u hu (hermiteProjection n (GaussianCore.normalizedHermite m)) := by
  have hm : normalizedWick u m ∈ GaussianNumberSectors.sector m :=
    (GaussianNumberSectors.sector m).smul_mem _ (IBMCubicFirstChaos.wick_mem_sector u m)
  rw [pullback_normalizedHermite,hermiteProjection_basis]
  have hp := GaussianNumberSectors.projection_of_sector (n := n) ⟨_,hm⟩
  rw [hp]
  by_cases hnm : n=m
  · simp only [hnm,ite_true,pullback_normalizedHermite]
  · simp only [hnm,ite_false,map_zero]

theorem projection_pullback (u : CoefficientSpace) (hu : ‖u‖ = 1) (n : ℕ)
    (f : GaussianCore.GaussianL2) :
    GaussianNumberSectors.projection n (pullback u hu f) = pullback u hu (hermiteProjection n f) := by
  let L := (GaussianNumberSectors.projection n).comp (pullback u hu).toContinuousLinearMap-
    (pullback u hu).toContinuousLinearMap.comp (hermiteProjection n)
  have hs : Submodule.span ℝ (range GaussianCore.normalizedHermite) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨m,rfl⟩
    exact sub_eq_zero.mpr (projection_pullback_basis u hu n m)
  have hz : L f=0 := GaussianCore.normalizedHermite_dense_span.induction
    (fun x hx => hs hx) (isClosed_eq L.continuous continuous_const) f
  exact sub_eq_zero.mp hz

private theorem hermiteProjection_norm (n : ℕ) (f : GaussianCore.GaussianL2) :
    ‖hermiteProjection n f‖^2 = GaussianCore.hermiteCoefficient f n^2 := by
  rw [hermiteProjection_apply,norm_smul,GaussianCore.normalizedHermite_orthonormal.1 n,mul_one]
  simp only [Real.norm_eq_abs,sq_abs]

private theorem hermiteProjection_field_energy (n : ℕ) (G : SourceSections) :
    ‖(hermiteProjection n).compLpL 2 gaussianProduct G‖^2 = ‖coefficientField n G‖^2 := by
  rw [BochnerL2Dominated.norm_sq_integral,coefficientField_energy]
  apply integral_congr_ae
  filter_upwards [(hermiteProjection n).coeFn_compLpL G] with x hx
  rw [hx,hermiteProjection_norm]

end OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation

namespace OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation
open InfiniteGaussian IBMClockObservationGraph IBMClockBochnerConverse ProductL2Curry
open GaussianClockValueOperators
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

private theorem projected_source_energy (u : CoefficientSpace) (hu : ‖u‖ = 1) (n : ℕ)
    (G : SourceSections) :
    ‖(GaussianNumberSectors.projection n).compLpL 2 gaussianProduct
      ((pullback u hu).toContinuousLinearMap.compLpL 2 gaussianProduct G)‖^2 =
        ‖coefficientField n G‖^2 := by
  have he : (GaussianNumberSectors.projection n).compLpL 2 gaussianProduct
      ((pullback u hu).toContinuousLinearMap.compLpL 2 gaussianProduct G) =
      (pullback u hu).toContinuousLinearMap.compLpL 2 gaussianProduct
        ((hermiteProjection n).compLpL 2 gaussianProduct G) := by
    apply Lp.ext
    filter_upwards [(GaussianNumberSectors.projection n).coeFn_compLpL
        ((pullback u hu).toContinuousLinearMap.compLpL 2 gaussianProduct G),
      (pullback u hu).toContinuousLinearMap.coeFn_compLpL G,
      (pullback u hu).toContinuousLinearMap.coeFn_compLpL
        ((hermiteProjection n).compLpL 2 gaussianProduct G),
      (hermiteProjection n).coeFn_compLpL G] with x hp hU hJ hH
    rw [hp,hU,hJ,hH]
    exact projection_pullback u hu n (G x)
  rw [he]
  have hn := (BochnerLinearIsometry.lift gaussianProduct (pullback u hu)).norm_map
    ((hermiteProjection n).compLpL 2 gaussianProduct G)
  exact (congrArg (fun z : ℝ => z^2) hn).trans (hermiteProjection_field_energy n G)

theorem clock_projection_energy (u : CoefficientSpace) (hu : ‖u‖ = 1) (n : ℕ)
    (F : Section) :
    ‖clockLift (GaussianNumberSectors.projection n) (fieldPullback u hu F)‖^2 =
      ‖coefficientField n (flip GaussianCore.γ gaussianProduct F)‖^2 := by
  have he : flip gaussianProduct gaussianProduct
      (clockLift (GaussianNumberSectors.projection n) (fieldPullback u hu F)) =
      (GaussianNumberSectors.projection n).compLpL 2 gaussianProduct
        (flip gaussianProduct gaussianProduct (fieldPullback u hu F)) := by
    change flip gaussianProduct gaussianProduct (flip gaussianProduct gaussianProduct _) = _
    exact GaussianClockValueOperators.flip_involutive _
  rw [flip_fieldPullback] at he
  have hn := (flip gaussianProduct gaussianProduct).norm_map
    (clockLift (GaussianNumberSectors.projection n) (fieldPullback u hu F))
  calc
    _ = ‖flip gaussianProduct gaussianProduct
        (clockLift (GaussianNumberSectors.projection n) (fieldPullback u hu F))‖^2 := by rw [hn]
    _ = _ := by rw [he,projected_source_energy]

theorem clock_sector_noise_hasSum (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (F : Section) :
    HasSum (fun n => 2*(1-(inner ℝ u v)^n)*
      ‖clockLift (GaussianNumberSectors.projection n) (fieldPullback u hu F)‖^2)
      (‖fieldPullback u hu F-fieldPullback v hv F‖^2) := by
  simpa only [clock_projection_energy] using field_noise_energy_hasSum u v hu hv F

end OperatorDerivativeRewrite.Foundation.GaussianObservationCorrelation
