import Foundation.GaussianQuadraticCylinders
import Foundation.GaussianQuadraticIto

/-! A genuine mixed stopped-coordinate product rule. The mixed correction
is min(T,r,s), not separate componentwise quadratic variations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianMixedStoppedIto
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeDivergence
open GaussianTimeProductL2 GaussianProductDerivative GaussianPredictableFull GaussianSensitivityCore
open GaussianQuadraticCylinders GaussianQuadraticRepresentation

theorem past_coordinate (s : ℝ≥0) :
    (pastCoefficient (fun _ : Fin 1 => s) (MvPolynomial.X 0) : GaussianL2) = wienerL2 s := by
  apply Lp.ext
  filter_upwards [pastCoefficient_coeFn (fun _ : Fin 1 => s) (MvPolynomial.X 0)] with ω hω
  simpa only [MvPolynomial.eval_X, process] using hω

theorem past_coordinate_step_slices (s t : ℝ≥0) :
    scalarCurry (pastStep s t (fun _ : Fin 1 => s) (fun _ => le_rfl) (MvPolynomial.X 0) : TimeProbabilityL2)
      =ᵐ[volume] (Ioc (s:ℝ) (t:ℝ)).indicator (fun _ => wienerL2 s) := by
  change scalarCurry (productTensor (intervalVector s t)
    (pastCoefficient (fun _ : Fin 1 => s) (MvPolynomial.X 0))) =ᵐ[volume] _
  rw [past_coordinate, scalarCurry_productTensor]
  filter_upwards [BochnerClosedOperator.tensor_coeFn volume (intervalVector s t) (wienerL2 s),
    intervalVector_coeFn s t] with x hx hi
  rw [hx, hi]
  by_cases hm : x ∈ Ioc (s:ℝ) (t:ℝ) <;> simp [hm]

theorem orderedCrossField_slices (s t : ℝ≥0) :
    scalarCurry (orderedCrossField s t : TimeProbabilityL2) =ᵐ[volume] fun x =>
      (Ioc 0 (s:ℝ)).indicator (fun x => (2:ℝ) • wienerL2 x.toNNReal) x +
      (Ioc (s:ℝ) (t:ℝ)).indicator (fun _ => wienerL2 s) x := by
  change scalarCurry ((2:ℝ) • (quadraticIntegrand s : TimeProbabilityL2) +
    (pastStep s t (fun _ : Fin 1 => s) (fun _ => le_rfl) (MvPolynomial.X 0) : TimeProbabilityL2)) =ᵐ[volume] _
  rw [map_add, map_smul]
  filter_upwards [Lp.coeFn_add ((2:ℝ) • scalarCurry (quadraticIntegrand s))
    (scalarCurry (pastStep s t (fun _ : Fin 1 => s) (fun _ => le_rfl) (MvPolynomial.X 0))),
    Lp.coeFn_smul (2:ℝ) (scalarCurry (quadraticIntegrand s)),
    GaussianQuadraticIto.quadraticIntegrand_slices s, past_coordinate_step_slices s t]
      with x ha hs hq hp
  rw [ha]
  simp only [Pi.add_apply, hs, Pi.smul_apply, hq, hp, GaussianQuadraticIto.horizonValue]
  by_cases hm : x ∈ Ioc 0 (s:ℝ) <;> simp [hm]

/-- Actual stopped-coordinate spatial product-rule coefficient. -/
def crossRunning (s t : ℝ≥0) (x : ℝ) : GaussianL2 :=
  (Ioc 0 (s:ℝ)).indicator (fun x => wienerL2 (min x.toNNReal t)) x +
  (Ioc 0 (t:ℝ)).indicator (fun x => wienerL2 (min x.toNNReal s)) x

theorem ordered_cross_running (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ) :
    (Ioc 0 (s:ℝ)).indicator (fun x => (2:ℝ) • wienerL2 x.toNNReal) x +
      (Ioc (s:ℝ) (t:ℝ)).indicator (fun _ => wienerL2 s) x = crossRunning s t x := by
  by_cases hx0 : 0 < x
  · by_cases hxs : x ≤ (s:ℝ)
    · have hxt : x ≤ (t:ℝ) := hxs.trans hst
      have hns : x.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.mpr hxs
      have hnt : x.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hxt
      simp [crossRunning, hx0, hxs, hxt, not_lt.mpr hxs, min_eq_left hns, min_eq_left hnt, two_smul]
    · have hsx : (s:ℝ) < x := lt_of_not_ge hxs
      have hsn : s ≤ x.toNNReal := by
        exact_mod_cast (hsx.le.trans_eq (Real.coe_toNNReal x hx0.le).symm)
      by_cases hxt : x ≤ (t:ℝ)
      · simp [crossRunning, hx0, hxs, hxt, hsx, min_eq_right hsn]
      · simp [crossRunning, hx0, hxs, hxt, hsx]
  · have hsx : ¬(s:ℝ) < x := not_lt.mpr ((le_of_not_gt hx0).trans s.coe_nonneg)
    simp [crossRunning, hx0, hsx]

theorem crossField_slices (s t : ℝ≥0) :
    scalarCurry (crossField s t : TimeProbabilityL2) =ᵐ[volume] crossRunning s t := by
  have h := orderedCrossField_slices (min s t) (max s t)
  filter_upwards [h] with x hx
  rw [ordered_cross_running _ _ min_le_max] at hx
  change scalarCurry (crossField s t : TimeProbabilityL2) x = _ at hx
  rw [hx]
  rcases le_total s t with hst | hts
  · simp only [min_eq_left hst, max_eq_right hst]
  · simp only [min_eq_right hts, max_eq_left hts, crossRunning, add_comm]

/-- Mixed quadratic Ito for two arbitrarily ordered stopped Brownian
observations, including repeated and zero stopping times. -/
theorem stopped_product_ito (r s T : ℝ≥0) :
    (brownianProduct (min T r) (min T s) : GaussianL2) =
      itoIntegral (crossField (min T r) (min T s)) +
        ((min T (min r s) : ℝ≥0) : ℝ) • gaussianOne := by
  have h := crossField_integral (min T r) (min T s)
  have he : min ((min T r : ℝ≥0):ℝ) ((min T s : ℝ≥0):ℝ) = ((min T (min r s) : ℝ≥0):ℝ) := by
    simp only [NNReal.coe_min]
    rw [min_assoc, min_left_comm (r:ℝ) (T:ℝ), ← min_assoc, min_self]
  rw [he] at h
  exact (sub_eq_iff_eq_add.mp h.symm)

/-- Integrated mixed covariance rate of the two stopped coordinates. -/
theorem mixed_covariance_integral (r s T : ℝ≥0) :
    (∫ x in 0..(T:ℝ), (Ioc 0 (r:ℝ)).indicator (fun _ => (1:ℝ)) x *
      (Ioc 0 (s:ℝ)).indicator (fun _ => (1:ℝ)) x) = ((min T (min r s) : ℝ≥0):ℝ) := by
  rw [intervalIntegral.integral_of_le T.coe_nonneg, ← integral_indicator measurableSet_Ioc]
  have he : (Ioc 0 (T:ℝ)).indicator (fun x =>
      (Ioc 0 (r:ℝ)).indicator (fun _ => (1:ℝ)) x *
      (Ioc 0 (s:ℝ)).indicator (fun _ => (1:ℝ)) x) =
      (Ioc 0 (((min T (min r s) : ℝ≥0):ℝ))).indicator (fun _ => (1:ℝ)) := by
    funext x
    by_cases hT : x ∈ Ioc 0 (T:ℝ) <;> by_cases hr : x ∈ Ioc 0 (r:ℝ) <;>
      by_cases hs : x ∈ Ioc 0 (s:ℝ) <;>
      simp_all [mem_Ioc, NNReal.coe_min, le_min_iff]
  rw [he, integral_indicator measurableSet_Ioc]
  simp [Measure.real, ENNReal.toReal_min]

variable {ι : Type*} [Fintype ι]

/-- An independently specified nonlinear finite-dimensional function, with
arbitrary mixed quadratic coefficients (symmetry is not imposed). -/
def quadratic (c : ℝ) (a : ι → ℝ) (b : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  c + ∑ i, a i*x i + ∑ i, ∑ j, b i j*x i*x j

def firstDirectional (a : ι → ℝ) (b : ι → ι → ℝ) (x d : ι → ℝ) : ℝ :=
  ∑ i, a i*d i + ∑ i, ∑ j, b i j*(d i*x j+x i*d j)

def secondDirectional (b : ι → ι → ℝ) (v w : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, b i j*(v i*w j+w i*v j)

theorem quadratic_hasDerivAt (c : ℝ) (a : ι → ℝ) (b : ι → ι → ℝ)
    (x d : ι → ℝ) (z : ℝ) :
    HasDerivAt (fun e => quadratic c a b (fun i => x i+e*d i))
      (firstDirectional a b (fun i => x i+z*d i) d) z := by
  have hd (i : ι) : HasDerivAt (fun e => x i+e*d i) (d i) z := by
    convert (((hasDerivAt_id z).mul_const (d i )).const_add (x i)) using 1 <;> (try funext e) <;> simp
  have hlin := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hd i).const_mul (a i))
  have hquad := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ((hd i).mul (hd j)).const_mul (b i j)))
  convert ((hasDerivAt_const z c).add hlin).add hquad using 1
  · funext e
    simp only [quadratic, Pi.add_apply, Pi.mul_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [zero_add, firstDirectional]

theorem firstDirectional_hasDerivAt (a : ι → ℝ) (b : ι → ι → ℝ)
    (x v w : ι → ℝ) (z : ℝ) :
    HasDerivAt (fun e => firstDirectional a b (fun i => x i+e*w i) v)
      (secondDirectional b v w) z := by
  have hd (i : ι) : HasDerivAt (fun e => x i+e*w i) (w i) z := by
    convert (((hasDerivAt_id z).mul_const (w i )).const_add (x i)) using 1 <;> (try funext e) <;> simp
  have h := (hasDerivAt_const z (∑ i, a i*v i)).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        (((hd j).const_mul (v i)).add ((hd i).mul_const (v j))).const_mul (b i j))))
  convert h using 1
  · funext e; simp [firstDirectional, Pi.add_apply]
  · simp [secondDirectional]

theorem half_hessian_contraction (b : ι → ι → ℝ) (d : ι → ℝ) :
    (1/2:ℝ)*secondDirectional b d d = ∑ i, ∑ j, b i j*d i*d j := by
  simp only [secondDirectional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticCylinder_coeFn (c : ℝ) (a : ι → ℝ) (b : ι → ι → ℝ) (t : ι → ℝ≥0) :
    quadraticCylinder c a b t =ᵐ[gaussianProduct] fun ω => quadratic c a b (fun i => process (t i) ω) := by
  let L : GaussianL2 := ∑ i, a i • wienerL2 (t i)
  let Q (i : ι) : GaussianL2 := ∑ j, b i j • (brownianProduct (t i) (t j) : GaussianL2)
  filter_upwards [Lp.coeFn_add (c • gaussianOne + L) (∑ i, Q i),
    Lp.coeFn_add (c • gaussianOne) L, Lp.coeFn_smul c gaussianOne, gaussianOne_coeFn,
    Lp.coeFn_finsetSum Finset.univ (fun i => a i • wienerL2 (t i)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (wienerL2 (t i))),
    Lp.coeFn_finsetSum Finset.univ Q,
    ae_all_iff.mpr (fun i => Lp.coeFn_finsetSum Finset.univ
      (fun j => b i j • (brownianProduct (t i) (t j) : GaussianL2))),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      Lp.coeFn_smul (b i j) (brownianProduct (t i) (t j) : GaussianL2))),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => brownianProduct_coeFn (t i) (t j)))]
      with ω ha hb hc ho hl hs hq hqq hqs hp
  change (c • gaussianOne + L + ∑ i, Q i) ω = _
  rw [ha]
  simp only [Pi.add_apply, hb, hc, Pi.smul_apply, ho, smul_eq_mul, mul_one]
  change L ω = _ at hl
  rw [hl, hq]
  simp only [Finset.sum_apply, hs, Pi.smul_apply, smul_eq_mul]
  have hqv (i : ι) : Q i ω = ∑ j, b i j * (process (t i) ω * process (t j) ω) := by
    have hh := hqq i
    change Q i ω = _ at hh
    rw [hh]
    simp only [Finset.sum_apply, hqs, Pi.smul_apply, smul_eq_mul, hp]
  simp only [hqv, quadratic, process, mul_assoc]

/-- Mixed quadratic stopped-cylinder Ito, reusing the proved actual cross
integrands rather than replacing a terminal adjoint by a running derivative. -/
theorem stopped_quadratic_ito (c : ℝ) (a : ι → ℝ) (b : ι → ι → ℝ)
    (r : ι → ℝ≥0) (T : ℝ≥0) :
    quadraticCylinder c a b (fun i => min T (r i)) - c • gaussianOne =
      itoIntegral (quadraticCylinderIntegrand a b (fun i => min T (r i))) +
        (∑ i, ∑ j, b i j * ((min T (min (r i) (r j)) : ℝ≥0) : ℝ)) • gaussianOne := by
  have h := quadraticCylinder_representation c a b (fun i => min T (r i))
  have hm (i j : ι) : min ((min T (r i) : ℝ≥0):ℝ) ((min T (r j) : ℝ≥0):ℝ) =
      ((min T (min (r i) (r j)) : ℝ≥0):ℝ) := by
    simp only [NNReal.coe_min]
    rw [min_assoc, min_left_comm (r i:ℝ) (T:ℝ), ← min_assoc, min_self]
  simp only [quadraticCylinderMean, hm, add_smul] at h
  linear_combination (norm := module) -h

end OperatorDerivativeRewrite.Foundation.GaussianMixedStoppedIto





