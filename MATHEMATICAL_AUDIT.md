# Mathematical audit: L² multiplication

## Scope and verification status

This audit concerns `C:/Operator/OperatorDerivative.lean` and
`C:/Operator/OperatorDerivative.tex`. Line numbers below refer to those unchanged originals.
The abstract energy-space interfaces have **not** been rewritten or imported into the new
foundation. Their conditional algebraic proofs do not establish that their fields admit
pointwise interpretations on an arbitrary probability space.

The new `Foundation/LpProducts.lean` uses Mathlib's `MemLp`, `Lp`, `HolderTriple`,
`MemLp.of_bilin`, Hölder estimates, and the concrete `L2.inner_def`.
The original monolith is not claimed to compile or to have an axiom-free verification.
The counterexample and proposed operator-domain arguments below are mathematical analysis;
they are not claimed as Lean theorems of this increment.

## A precise probability-space counterexample

Let Ω = (0,1), with its Borel sigma-algebra and restricted Lebesgue measure P.
This is a probability space. Set f(x) = g(x) = x^(-1/3). Then

- ∫ |f|² dP = ∫₀¹ x^(-2/3) dx = 3, and likewise for g, so f,g ∈ L².
- fg = x^(-2/3) lies in L¹, with integral 3.
- ∫ |fg|² dP = ∫₀¹ x^(-4/3) dx = ∞, so fg ∉ L².

Consequently a total L² × L² → L² operation agreeing a.e. with pointwise
multiplication cannot exist on this space. Taking H = ℝ and u = v = f also
refutes total L² scalar–vector multiplication into L² and total pointwise
inner products of L² vectors into L². Any proposed L² representative would
have the same infinite squared integral by a.e. equality.

L² multiplication also lacks the continuity needed for an L² density extension:
f_n = n^(1/2) 1_(0,1/n²) has ‖f_n‖₂ = n^(-1/2) → 0 but ‖f_n²‖₂ = 1.
Thus a continuous bilinear L²-valued extension cannot supply the missing operation.

## Correct integrability and estimates

For 1/r = 1/p + 1/q (including 1/∞ = 0), Hölder and pointwise
Cauchy–Schwarz give, for a real inner-product space H,

    ‖fg‖_r ≤ ‖f‖_p ‖g‖_q
    ‖fu‖_r ≤ ‖f‖_p ‖u‖_q
    ‖⟨u,v⟩_H‖_r ≤ ‖u‖_p ‖v‖_q.

Membership includes a.e. strong measurability. These statements hold on arbitrary
measure spaces; finiteness or probability is unnecessary for the product estimates.

| Inputs | Output, for all three operations | Intended use |
| --- | --- | --- |
| L², L² | L¹ | Scalar or vector pairings and their expectations |
| L⁴, L⁴ | L² | Products and derivative terms in a D^{1,4} product argument |
| L∞, L² | L² | Bounded multipliers on the Hilbert energy space |
| L∞, L¹ | L¹ | Bounded weights on pointwise pairings |
| L⁸, L⁸ | L⁴ | Intermediate products when another L⁴ operation is required |

The actual L² Hilbert inner product is ∫ ⟨u(ω),v(ω)⟩_H dP, with an L¹
integrand, and its absolute value is at most ‖u‖₂‖v‖₂.
The random variable ⟨u,v⟩ is L² precisely when its square is integrable
(with measurability); a sufficient condition is u,v ∈ L⁴. The stronger
condition ‖u‖‖v‖ ∈ L² is sufficient but not necessary because of cancellation
or pointwise orthogonality. Similarly, scalar fu is L² precisely when
|f|‖u‖ ∈ L², with the appropriate measurability.
On a probability space L⁴ ⊂ L² and L² ⊂ L¹, but neither inclusion reverses.
Constants act on L² through a fixed bounded linear map, without an L⁴ assumption.

## Incorrect structure fields and their locations

The following is the complete field inventory of the three original product interfaces.
Algebraic identities are pointwise valid; the defect is their total L² typing.
Constant-only special cases are separately preservable.

| Interface and original lines | Fields | Correction |
| --- | --- | --- |
| `UnboundedEnergySpace`, 137–141 | `mul`, `smul`, `pip` | Replace total L² outputs by exponent-indexed operations or restricted L² products |
| Same, 143–153 | `inner_eq_expect_pip`, `pip_smul`, `pip_symm`, `smul_selfadj`, `smul_add_left`, `smul_mul_assoc`, `smul_add_right`, `smul_finset_sum` | Integrate L¹ pairings; restrict multipliers; type each intermediate product with its actual exponent |
| Same, 155–156 | `mul_dom` | dom(D) × dom(D) closure is not automatic; D^{1,4} requires BOTH values and derivatives in L⁴ and a proved approximation argument |
| Same, 161–165 | `inner_eq_expect_mul`, `mul_comm`, `mul_assoc`, `mul_sub` | Pairing in L¹; products and identities with compatible exponents |
| `EnergySpace`, 748–754 | `mul`, `smul`, `pip`, `inner_eq_expect_mul`, `inner_eq_expect_pip` | Same typing correction; boundedness of D does not repair multiplication |
| Same, 758, 766–773 | `mul_const_centered`, `mul_comm`, `mul_assoc`, `mul_add`, `mul_sub`, `mul_constEmb`, `pip_smul`, `pip_symm`, `smul_selfadj` | Constant multipliers are valid; general identities need restricted types and integrable pairings |
| Same, 777–789 | `smul_add_left`, `smul_mul_assoc`, `smul_add_right`, `smul_finset_sum`, `pip_finset_sum_left` | Preserve algebra only after giving the terms correct spaces |
| `ConcreteEnergyData`, 2810–2812 | `mul`, `smul`, `pip` | Despite using concrete Mathlib Lp types, the outputs remain incorrect |
| Same, 2824–2835 | `inner_eq_expect_pip`, `pip_smul`, `pip_symm`, `smul_selfadj`, `smul_add_left`, `smul_mul_assoc`, `smul_add_right`, `smul_finset_sum` | Same restricted operations and L¹ expectations |
| Same, 2836–2839, 2842–2845 | `mul_dom`, `inner_eq_expect_mul`, `mul_comm`, `mul_assoc`, `mul_sub` | Same domain and exponent corrections |
| `UnboundedCylindricalStructure`, 354–373 | `mul_cyl`, `coord_leibniz`, `ibp_formula`, `leibniz_closure` | Specify integrability of cylindrical values, coordinate derivatives and random representers; prove closure in the L⁴ graph topology |
| `CylindricalStructure`, 1437–1452 | Same four fields | Extending to all L² is invalid even if D is bounded; use a restricted core |
| `UnboundedSmoothFunc`, 493–497 | `chain_rule`, `chain_rule_deriv` | Prove composition/domain results; bounded φ',φ'' are sufficient for the scalar actions but do not prove a chain rule |
| `UnboundedStochVolAssumption`, 549–556 | `inv_σ`, `brown_leibniz`, `transfer_formula` | An L² reciprocal is not a multiplier on all L²; require a bounded reciprocal or individual product/weighted-domain membership |

`expect` on L² is not itself incorrect on a probability space. The error is using it
as though every random product were in L²; define the integral/expectation on L¹ instead.
`expect_smul` and constant embeddings do not assume general product closure.

## Affected declarations and downstream consequences

Each row identifies every direct use of the erroneous abstract operations in declarations
or proofs, together with the associated wrappers. A conditional theorem in the old abstract
interface may have a valid algebraic proof, but does not establish a theorem for concrete L².

| Original declarations (start lines) | Original claim / required correction |
| --- | --- |
| `LeibnizCondition_unbounded` 335; `ibp_rep_unbounded` 378; `cylindrical_leibniz_unbounded` 392; `cylindrical_implies_leibniz_unbounded` 407; `malliavin_deriv_unbounded` 412; `D_eq_malliavin_unbounded` 416 | Total products appear before domain hypotheses. Use a core with actual multiplier/derivative membership; membership in dom(D) alone is insufficient |
| `ProductRule_unbounded` 423; `leibniz_implies_product_rule_unbounded` 433 | hFu proves only divergence-domain membership of an already typed product. It does not justify Fδu or ⟨DF,u⟩ ∈ L². Require those separately, or sufficient L∞/L⁴ conditions |
| `intrinsic_bracket_unbounded` 500; `ito_correction_unbounded` 504; `ito_correction_from_product_rule_unbounded` 508; `operator_ito_decomposition_unbounded` 520 | Bracket is naturally L¹. Bounded φ'' times bracket is still only L¹. An L² equation needs additional bracket/cross-pairing integrability |
| `leibniz_stochastic_volatility_unbounded` 560; `transfer_preserves_pip` 581; `gubinelli_base_invariance` 595; `main_pipeline` 672 | Reciprocal-volatility products and nested cross-products need their own exponents or restricted weighted domains; algebra alone proves no integrability |
| `adjoint_prob` 806; `D_const` 817; `mul_pip_eq_pip_smul` 841; `const_perp_Im_delta` 991; `PRP_from_ker_D_subset_constants` 1032 | Adjoint/constant/representation reasoning can use Hilbert pairings directly. `mul_pip_eq_pip_smul` is a triple-product identity, not an unrestricted L² identity |
| `LeibnizCondition` 1126; `ProductRule` 1129; `leibniz_iff_product_rule` 1133 | Statements quantify over all L² inputs with false product typing. Reformulate on a proved test core and multiplier domains; no automatic equivalence on all L² |
| `chain_rule_sq` 1218; `pow'` 1224; `chain_rule_pow` 1229 | Squaring needs F ∈ L⁴ to yield L²; an nth power needs F ∈ L^{2n}. Derivative terms F^{n-1}DF need their own L² membership |
| `chain_rule_defect` 1341; `chain_rule_from_density` 1357; `leibniz_defect` 1421 | Defects are not everywhere defined on L². Need composition estimates or L⁴ value-and-derivative convergence, not only L² density/closedness |
| `ibp_rep` 1455; `cylindrical_leibniz_on_class` 1468; `cylindrical_implies_leibniz` 1482 | Coordinate derivative times representer is L² for deterministic representers or bounded coefficients; two arbitrary L² factors only give L¹ |
| `RepresentersDeterministic` 1496; `representer_rigidity` 1515; `deterministic_variance_bound` 1537 | Triple products need integrability. A deterministic κ does NOT imply expectation factorization against arbitrary random u; that is an additional, generally false assumption |
| `RepresentersNondegenerate` 1562; `stoch_vol_representers` 1569; `stoch_vol_pip` 1575; `stoch_vol_obstruction` 1590 | Nondegeneracy can be pointwise/L¹; transferred representers need restricted products. hcancel is independently false: on (0,1), F=1+x, G=1/(1+x) are bounded, F nonconstant and FG=1 with G≠0 |
| `GaussianVolterra` 1649; `leibniz_gaussian` 1659; `leibniz_fBM` 1830; `full_calculus_fBM` 1836 | Inherit/propagate the invalid universal Leibniz interface; Gaussian moments of coordinates do not apply to every L² functional |
| `gubinelli_derivative` 1689; `rough_path_lift` 1724; `is_controlled` 1731; `gubinelli_remainder` 1740; `controlled_pythagoras` 1751 | Products defining lifts, remainders and ratios/cross-products require L² membership. Pythagoras is valid once those elements exist and orthogonality is established |
| `EnergySpace.intrinsic_bracket` 1996; `EnergySpace.ito_correction` 2001; `ito_formula_bounded` 2021; `ito_formula_with_clark_ocone` 2046 | Brackets/corrections default to L¹; boundedness of δ/D or φ'' does not upgrade them to L². Projection commutation with a random multiplier is a separate hypothesis |
| `ItoProcess.bracket` 2098; `ito_formula_time_indexed` 2118; `ito_formula_integrated` 2141; `ito_from_leibniz_alone` 2207 | In addition to pointwise L² correction requirements, integrated statements need time-integrability and divergence-domain facts; these are not supplied by Hölder alone |
| `EnergySpace.numberOperator_selfadj` 2491 | Proof uses the probabilistic bridge; preserve the substantive operator theorem using adjointness directly |
| `EnergySpace.covariance` 2568; `EnergySpace.covariance_eq_inner_centered` 2572; `EnergySpace.covariance_symm` 2594; `EnergySpace.variance` 2600; `EnergySpace.ito_isometry_concrete` 2605 | Centered covariance/variance integrands are L¹. The real-valued formulas survive without a total L² multiplication operation |
| `ConcreteEnergyData.toUnboundedEnergySpace` 2856 | Forwards the bad fields; not a construction of admissible pointwise operations |
| `brownianEnergySpace` 3466, especially parameters 3475–3487 | Assumes total mul/smul/pip AND agreement a.e. Their existence is false on general probability spaces; proving algebra from these hypotheses does not construct Brownian energy data |

Representation, projection and pure adjoint results that merely inherit an energy-space
parameter need a later separation from the product interface. No integrability correction
is required for their Hilbert-space inner products themselves. The stochastic Fubini
lemmas 1944/1955 use bounded linear maps and Bochner integrability, not L² product closure.

## Correct concrete fragments to preserve

- `L2_inner_eq_integral` 2707, `L2H_inner_eq_integral` 2725,
  `L2_smul_const` 2996 and its algebra/inner-product lemmas 3020, 3738–3768, 4273:
  Hilbert pairings and multiplication by a fixed deterministic vector are correctly typed.
- `ibp_algebraic_step` 3054, `inner_eq_expect_mul_concrete` 3245:
  integrate L² pairings in L¹ rather than package them as L² products.
- `concrete_mul` 3274 and `concrete_mul_comm` 3279 already use L⁴ × L⁴ → L².
- `pip_memLp_one` 3297, `concrete_pip_L1` 3305,
  `inner_eq_expect_pip_concrete` 3312 correctly give L¹ vector pairings.
- `concrete_mul_assoc` 3337, `concrete_mul_add` 3350, `concrete_mul_const` 3359,
  `concrete_pip_smul` 3369, `concrete_pip_symm` 3381, `concrete_smul_selfadj` 3392
  are pointwise identities. They do not establish integrability of their expressions.
  The extra L⁴ membership assumptions in the pointwise associativity lemma are unused;
  quotient-valued iterated products need appropriate intermediate membership.
- `isonormal_memLp_any` 3650 and `isonormal_memLp_four` 3673 concern Gaussian
  coordinates, not arbitrary elements of dom(D). `memLp_four_mul_of_memLp_eight` 3683
  is a correctly restricted Hölder claim.
- `memLp_two_of_memLp_four` 4427, `memLp_two_mul_of_memLp_four` 4452,
  `Lp4_mul` 4460, `Lp4_mul_comm` 4468, `memLp_four_const` 4479,
  `memLp_two_const_mul` 4485, `L4_inner_mul_well_defined` 4492 have correct
  mathematical integrability types. Finite measure is unnecessary for the product
  itself, but necessary for the inclusion L⁴ ⊂ L²; constants need finite measure.
- Concrete covariance identities 4293–4305 and finite-sum cylindrical derivative
  pairings 4321 are compatible with L¹ expectations.
- `ito_adjoint_level1` 4781, `ito_adjoint_level2` 4817,
  `ito_correction_concrete` 4839 express conditional integral pairings, not universal
  L² closure. They still require their declared Stein assumptions.
- `cylindrical_compose` 4892 and `cylindrical_chain_rule` 4920 explicitly assume
  membership of each derivative product; those hypotheses must be established for
  any eventual application, and are not themselves integrability proofs.
- `bilinear_identity_extends_by_density` 4962 is valid for actual continuous bilinear
  maps; it cannot be applied to the nonexistent L²-valued pointwise product.
  `complete_stochastic_calculus` 5132 packages conditional results including a
  correctly restricted L⁴ product; it does not repair the energy-space interfaces.

## Manuscript and comments requiring correction

| Original location | Claim / consequence |
| --- | --- |
| Lean 155, 2836, 3632–3649 | dom(D) is described as D^{1,4}, or as contained in L⁴, without value AND derivative L⁴ estimates. Linear Gaussian coordinates have moments; general Sobolev functionals need not have all moments |
| Lean `cylindrical_memLp_four` 3704 | The L⁴ conclusion is exactly the hpoly hypothesis. This proves no new polynomial-growth estimate. General smooth functions can grow too quickly |
| TeX 739 | D^{1,4} = D^{1,2} ∩ L⁴ is asserted via Meyer inequalities. L⁴ values alone do not supply L⁴ derivatives; retain the definition requiring both and prove any special implication separately |
| TeX 810 | Two L² norm factors claimed to have L² product by Cauchy–Schwarz. Correct output is L¹; use both L⁴, one L∞, or an independently proved squared-product integrability condition |
| TeX 674, 711–727 | Restricted-core and L⁴ graph-convergence approach is the right direction. Stability, density, derivative identification and estimates still need proofs; this is not all-dom(D) closure |
| TeX 783–805 | Product rule hypotheses correctly include F bounded and ‖DF‖‖u‖ ∈ L², but extension from bounded tests requires a graph core for D, not just L² density. Identifying D* with δ requires δ closed (or uses its closure) |
| TeX 108–112, 777 onward | An L² Itô correction/bracket requires fourth moments or another proved L² bound; L² regularity of DY alone only gives an L¹ bracket |
| Lean 3419–3448 | L⁴→L² multiplication, deterministic-vector multiplication and L¹ pip cannot fill the old total L² fields. They have different domains/codomains |

## Proposed interface, for a later increment

1. Keep the operator layer separate: X = Lp ℝ 2 P, V = Lp H 2 P,
   a densely defined δ : V →ₗ.[ℝ] X, and D = δ*. Keep Hilbert pairings native.
2. Use `lpMul`, `lpSmul`, `lpInner` with explicit Hölder exponents. Expectation is
   the integral of an L¹ scalar random variable. General pointwise pairings land
   in L¹; real constants remain ordinary scalar actions.
3. Multipliers on all of X or V come from Lp ℝ ∞ P. For more general random
   multipliers use the restricted domain {u ∈ V : fu ∈ L²}; prove membership for
   each application. Do not extend a product by zero outside this domain.
4. Define a D^{1,4} candidate as F ∈ dom(D) with F ∈ L⁴ AND DF ∈ L⁴(H), using
   a.e.-compatible Lp representatives. This is not automatically an algebra:
   Hölder only puts FG and F DG + G DF in L². A core approximation and closedness
   of D are needed to prove FG ∈ dom(D) and identify its derivative.
5. For the divergence product rule use F ∈ dom(D) ∩ L∞, u ∈ dom(δ), and
   ⟨DF,u⟩ ∈ L² (sufficient: DF,u ∈ L⁴, or ‖DF‖‖u‖ ∈ L²).
   Then Fu and Fδu are L² by the bounded-multiplier estimate. To PROVE Fu ∈ dom(δ)
   via adjointness, prove the identity on a graph-dense core of dom(D), with
   multiplication/Leibniz compatibility there, extend it to all dom(D), and use
   δ = D* only after proving δ closed. If δ is merely closable, the conclusion
   concerns its closure. No such domain theorem is implemented in this increment.
6. Treat brackets as L¹ by default. Add explicit L⁴ estimates on ΠDY or direct
   squared-pairing estimates before any L² correction theorem. An orthogonal
   projection on L² need not be bounded on L⁴ or commute with random multiplication.
7. In weighted stochastic-volatility energy spaces, division by σ may be a
   weighted isometry even if 1/σ is unbounded. Construct those spaces/maps and their
   restricted domains; do not model division as unrestricted L² multiplication.

Unresolved mathematical questions: what concrete δ and core are intended; is δ closed;
which cylindrical approximations converge in the L⁴ graph norm; which projection has
L⁴ estimates; which bracket/time-integrability bounds hold; and whether the intended
bounded predictable adjoint or unbounded Malliavin adjoint has the desired Leibniz rule.
Integrability is necessary for these statements but does not prove any of those identities.

## Lean declarations established in this increment

Namespace: `OperatorDerivativeRewrite.Foundation`.

- `holderTripleFourFourTwo` proves the exponent arithmetic, not an axiom.
- `mul_memLp`, `smul_memLp`, `inner_memLp`: membership at exponent r for
  `HolderTriple p q r` and actual `MemLp` inputs.
- `mul_eLpNorm_le`, `smul_eLpNorm_le`, `inner_eLpNorm_le`: the three Hölder
  seminorm estimates at the same exponents.
- `lpMul`, `lpSmul`, `lpInner`: constructions on Mathlib Lp equivalence classes.
  The three `_coeFn` theorems prove agreement a.e. with pointwise operations;
  the three `_norm_le` theorems prove the corresponding real-valued Lp norm bounds.
- `mul_L2_integrable`, `inner_L2_integrable`, `smul_L2_memLp_one` establish the
  L² × L² → L¹ cases (scalar/vector pairings Bochner-integrable where stated).
- `mul_L4_memLp_two`, `smul_L4_memLp_two`, `inner_L4_memLp_two` establish
  L⁴ × L⁴ → L²; the three `*_Linfty_L2_memLp_two` establish L∞ × L² → L².
- `L2_inner_eq_integral`, `L2_integral_inner_bound` identify and bound the
  integrated vector pairing.
- `L2_bounded_multiplier_selfadj` proves symmetry of multiplication by a real
  L∞ element on L²(H). It does not identify the multiplier with an operator adjoint
  through a newly constructed continuous-linear-map interface.

Verification: `lake build` and `lake build Foundation.AxiomAudit` succeed with pinned
Lean/Mathlib v4.34.1. `#print axioms` is included for **every** new declaration.
All report only `propext`, `Classical.choice`, `Quot.sound`; none depend on `sorryAx`
or a custom axiom. Existing unused-section-variable warnings in `Adjoint.lean` remain.

## Domain reconstruction milestone (after db345dc)

### Original domain and closure inventory

| Original location | Actual Lean content | Mathematical assessment / repair |
| --- | --- | --- |
| Lean 62–80 | D = δ.adjoint, closedness and adjoint identity under dense δ-domain | Preserve; this is the actual operator and domain used in the new modules |
| Lean `UnboundedEnergySpace` 101–170, especially 110–113 | δ is a LinearPMap and δ.domain is dense; comment calls δ closable | No `IsClosable` field is present. Density gives an adjoint and closedness, but alone does not imply density of its domain |
| Lean 130, 167–170 | Proj sends every vector into dom(δ); dom(D) is dense; dense pairing nondegeneracy | These are extra analytic hypotheses, not consequences of δ-density. Projection-domain invariance needs a concrete proof; D-density needs closability of δ or a separate proof |
| Lean 155–156, 2836–2839 | `mul_dom` asserts product closure for every pair in dom(D) | Invalid as a consequence of closedness. Remove this universal closure; replace it with a proved restricted-core result |
| Lean 180–187 | U.D = U.δ.adjoint and its domain-specific identity | Preserve. Membership must refer to this adjoint, not a newly assigned derivative |
| Lean 201–208, 226, 289, 314 | PRP/isometry and factorization/orthogonality/variance with explicit δ/D domain elements and projection-domain hypotheses | Those hypotheses remain needed. They are independent of multiplication closure |
| Lean `LeibnizCondition_unbounded` 335–338 | Identity for F,G in dom(D), with separate hFG, but total L² products | hFG is logically separate, but the ambient products are already incorrectly typed. Use restricted products; do not infer hFG from closedness |
| Lean `UnboundedCylindricalStructure` 341–373 | `cyl_in_dom`, `mul_cyl`, `coord_leibniz`, `ibp_formula`; `cyl_dense` merely supplies a sequence of cylindrical elements; `leibniz_closure` assumes the extension | No smoothness or derivative relation is encoded for coordinate derivatives. There is NO convergence clause in `cyl_dense`. Neither density nor the extension is proved by these fields |
| Lean 378–416 | IBP identification and cylindrical/global Leibniz wrappers | Formal algebra under supplied hypotheses. A real coordinate derivative and verified IBP are required for mathematical identification |
| Lean `ProductRule_unbounded` 423–476 | Divergence identity requires hFu, and proof uses universal `mul_dom` | Replace with bounded/restricted multipliers, correct L² pairings and separate domain facts. The present multiplier criterion supplies a sufficient δ-domain condition, but does not identify the commutator as contraction with DF |
| Lean `UnboundedSmoothFunc` 484–497 | `app_in_dom`, `deriv1_in_dom`, two chain rules assumed | Composition-domain membership and chain identities must be separately proved for a genuine scalar function; smoothness is not encoded here |
| Lean 546–560, 672 | Reciprocal volatility and Brownian derivative transfer and Leibniz assumptions | Require an actual Brownian derivative domain and a proved weighted transfer. Scalar L² reciprocity is not an everywhere-defined multiplier |
| Lean `EnergySpace` 735–799 | δ is continuous and everywhere defined; D is its continuous adjoint | Both domains really are the whole Hilbert spaces. This does not make L² an algebra or make D a derivation |
| Lean 1126–1204 | Universal bounded `LeibnizCondition`, `ProductRule`, equivalence | Universal pointwise L² typing fails. Even on a bounded test algebra, Leibniz requires separate structure on the actual adjoint |
| Lean 1218–1411 | Powers and chain-rule approximation/continuity assumptions | Use actual bounded test products or verified moment bounds. The hypotheses called polynomial approximation do not encode polynomials. Defect continuity cannot be assumed to establish a nonexistent L² product |
| Lean `CylindricalStructure` 1429–1452 and wrappers 1455–1484 | Assumed algebraic class and IBP; `leibniz_closure` concludes Leibniz on all L² | Separate algebraic closure, actual operator membership, actual derivative identity, and the topology of extension |
| Lean 1649–1661, 1830–1841 | Gaussian/fBM structures carry or propagate the previous closure assumptions | Gaussian marginals do not supply graph density or closure of dom(D) |
| Lean `ConcreteStochasticIntegral` 2768–2788 | Dense δ-domain, centeredness and exact isometry on its entire domain | Isometry makes δ bounded on that domain and gives a bounded extension. If also closed, its dense domain must be the whole space. This is not a generic unbounded Skorokhod divergence interface |
| Lean `ConcreteEnergyData` 2806–2850 and converter 2856 | Repeats universal `mul_dom`, D-density and projection-domain assumptions | Concrete Lp types do not prove these assumptions. Use the new primitive domain statements before assembling another energy interface |
| Lean `CylindricalFunctional` 2939–2967 | Separate `f_eval`, `df_eval`, F and dF, with a.e. evaluation specifications | No `ContDiff` or derivative relation ties df_eval to f_eval; no membership of F in the actual δ* domain. Do not reuse this as a verified cylindrical derivative |
| Lean 3632–3724, 4427–4492 | Intended Sobolev/core closure comments and correct Lp product facts | L⁴ product estimates are useful, but neither identify dom(D) with D^{1,4} nor prove domain closure. `cylindrical_memLp_four` returns its own membership hypothesis |
| Lean 4712–4748, 4892–4937 | Smooth/composed cylindrical packages and formula unfolding | Some scalar derivative hypotheses are supplied, but actual δ*-domain identification and representation independence remain separate tasks |
| Lean 4943–4999 | Continuous-bilinear density theorem and commented-out domain extension | The generic theorem is valid. It does not construct a graph space or prove continuity of a defect that uses D(FG) before product-domain membership |
| TeX 208–217, 254–283 | Densely defined closable δ; adjoint domain characterized by continuous pairing | This is the intended unbounded domain. Correctly distinguish density of δ-domain, closability, closedness and density of D-domain |
| TeX 504, 674, 703–727 | C_b^∞ cylindrical class; graph-norm and L⁴-graph closure | An algebraic cylindrical class is a collection before closure. D^{1,2} and D^{1,4} are closures in DIFFERENT norms; identifying them with actual adjoint restrictions requires proof |
| TeX 739, 783–810 | Claimed Sobolev identification and divergence-domain extension | Correct the L⁴-derivative inference, use a graph core rather than mere L² density, and distinguish δ from its closure |
| TeX 984–1024, 1054 | Weighted transfer and M-cylindrical density | Weighted transfer needs correct energy spaces. The manuscript itself recognizes an additional M-cylindrical graph-density argument; coordinate generation alone does not prove it |
| TeX 1377 | Claims bounded case bypasses closure by density and invokes unavailable analysis for unbounded case | Boundedness of D only compares its graph norm with L². Product continuity still needs a stronger topology. Distinguish a missing mathematical proof from the work of implementing one |

### Three different objects

1. **Actual domain:** for the fixed δ, dom(D) = dom(δ*) consists of F such that
   u ↦ ⟨F,δu⟩ is continuous in the ambient L² norm of u. For dense δ-domain this
   is equivalent to existence of a unique vector v with ⟨v,u⟩ = ⟨F,δu⟩ for every
   u in dom(δ). The value DF is that representer. For bounded everywhere-defined
   δ, dom(D) is all of L².
2. **Algebraic test class:** finite sums and products of selected test functions.
   No density follows from this description. The chosen class in this increment
   is `Algebra.adjoin ℝ S`, where generators S satisfy the concrete divergence
   multiplier conditions below. Smooth bounded cylindrical generators are a
   future specialization, not something automatically proved admissible here.
3. **Graph core / closure:** a linear subspace C contained in dom(D) is a graph
   core if the closure of the graph of D restricted to C is the graph of D.
   Mathlib already expresses this as `LinearPMap.HasCore`. Ordinary L² density
   is insufficient. Graph convergence means both F_n → F and DF_n → v in L²;
   the new `closed_graph_limit` then proves F ∈ dom(D) and DF = v.
   No graph norm is silently placed on the domain subtype in our definitions.

A fourth-moment restriction is F ∈ dom(D), F ∈ L⁴ and DF ∈ L⁴(H).
`fourthMomentDomain` defines exactly that set of actual domain elements.
It is not defined as a closure and is not identified with classical D^{1,4}.
An L⁴ graph closure additionally requires approximating both F and DF in L⁴.
We have not constructed that closure or proved a density theorem this increment.

### Closedness does not give product closure, even when the product is L²

On (0,1) with Lebesgue probability measure let w(x)=x^(-1/5), and let
D be the maximal multiplication operator Df = wf with domain {f∈L² : wf∈L²}.
This is closed: if f_n→f and wf_n→g in L², simultaneous a.e.-convergent
subsequences give g=wf. It is densely defined: truncation to [1/n,1) approximates
any L² function and w is bounded on each such truncated set.
For f=g=x^(-1/5), wf=x^(-2/5) is L², so f,g∈dom(D).
The product fg=x^(-2/5) is also L², but wfg=x^(-3/5) is not L².
Thus fg∉dom(D). This example is a mathematical counterexample, not a Lean
formalization in this increment, and is not asserted to be a centered divergence.

### Sufficient product-closure hypotheses implemented now

Write M_f^X and M_f^V for pointwise multiplication by f on X=L²(ℝ) and V=L²(H).
For a fixed δ : V →ₗ.[ℝ] X, `IsDivergenceMultiplier δ f` means:

- f is a.e. strongly measurable and essentially bounded;
- M_f^V preserves **δ's** domain;
- there exists a bounded linear R_f : V → X such that, for all u∈dom(δ),

      δ(M_f^V u) = M_f^X(δu) − R_f u.

This is an explicit sufficient analytic condition on the GIVEN δ.
It neither assumes closure of dom(δ*) under products nor prescribes a derivative
of f. The equation determines R_f on the dense δ-domain; `divergenceCommutator_unique`
proves uniqueness of its bounded extension. For an arbitrary unbounded δ, proving
these hypotheses for nonconstant cylindrical generators remains a concrete analytic task.
The criterion is sufficient and may be stronger than needed; no necessity is claimed.

The new proofs show constants, sums and products remain admissible. In particular

    R_(fg) = M_f^X R_g + R_f M_g^V.

All scalar and vector multipliers are actual continuous linear maps constructed
using the preceding L∞ × L² → L² estimates. These are not merely assumed maps.
`boundedMultiplierAlgebra δ` is the resulting subalgebra of real functions on Ω.
Its raw functions have canonical a.e. L² classes on finite measure spaces;
`boundedToL2_mul` proves that algebraic multiplication agrees with actual L² multiplication.
The raw-function algebra is not claimed to inject into L² (null-set differences remain).

For dense δ-domain, admissibility implies M_f^X maps dom(δ*) into itself.
The proof verifies the adjoint relation with the genuine representer

    M_f^V(δ*F) + R_f*F.

If δ is centered, constant one belongs to dom(δ*). Multiplying that constant
proves each admissible f, and every product of admissible f,g, has its L² class
in the actual adjoint domain. Hence the algebraic test class generated by any
admissible generator set is product-closed in dom(δ*), without per-product
membership assumptions. The generator hypotheses must still be proved in applications.
For bounded δ on the whole space, all essentially bounded f satisfy the criterion:
R_f = M_f^X δ − δ M_f^V. This case is verified independently of any Leibniz rule.

### Operator membership is separate from the Leibniz identity

The present theorems do NOT identify R_f u with ⟨Df,u⟩ pointwise, or R_f*G
with G Df. That local identification is needed to obtain
D(fg) = f Dg + g Df. It requires a genuine derivative/IBP construction for the
specific δ, rather than an arbitrary assignment to coordinate derivatives.

For example, on a two-point equal-probability space let δ = I − E on real L²,
where E is projection onto constants. This δ is bounded, centered and self-adjoint,
so D=δ and all bounded multipliers belong to our algebra. For F taking values ±1,
DF=F but D(F²)=D1=0 while 2FDF=2. Product-domain closure therefore does not imply
Leibniz, even with a centered δ and D1=0. This is documented mathematics, not an
additional Lean counterexample theorem.

A restricted Leibniz statement should quantify over elements of a verified test
algebra already included in dom(D), and then assert the identity for the SAME D.
For an L⁴ extension, first establish product membership using known core products,
actual core Leibniz identities, L⁴ value-and-derivative approximation, Hölder
product convergence and closedness. Only then identify the value of D(FG).
Avoid defining a everywhere-valued defect involving D(FG) before its membership
is known. No such extension or cylindrical derivative is implemented here.

### Downstream repairs and remaining arguments

| Results | What this increment supplies | What remains |
| --- | --- | --- |
| D_closed, D_adjoint, adjoint uniqueness, bounded/unbounded agreement | Actual-domain characterization, bounded full-domain theorem, graph-limit criterion | Concrete δ, density and any closability/closedness assumptions |
| `mul_dom`, `mul_cyl`, cylindrical product admissibility | Proven restricted algebra product closure, including generated classes | Verify divergence multiplier conditions for intended cylindrical generators; no all-dom(D) closure |
| `ibp_rep`, D_eq_malliavin and cylindrical Leibniz | A place to state genuine identities without fake domains | True smooth derivatives, representation independence and IBP against the given δ |
| `cylindrical_implies_leibniz`, Gaussian/fBM Leibniz | Correct distinction between algebraic class and graph closure; L⁴ product-term membership | L⁴ derivative estimates, approximation of values AND derivatives, genuine core Leibniz and product-convergence implementation |
| Divergence product rule | Admissible multipliers preserve dom(δ); adjoint membership is proved separately | Identify R_f with the pointwise contraction; for weaker unbounded multipliers, prove graph-core extension and δ = D* (or use δ's closure) |
| Powers / chain rules | Finite products of admissible bounded tests stay in the algebra and actual D-domain | Actual Leibniz, smooth composition admissibility, derivative identities and convergence estimates |
| Clark–Ocone/GKW/variance | Native Hilbert domains unaffected by the erroneous algebra fields | PRP, projection-domain invariance, closed range/isometry and representation hypotheses |
| Brackets / Itô formulas / time integration | Correct prerequisites can now be stated | L⁴ estimates for derivatives/projections, correction integrability, local operator identities, time limits and Fubini; intentionally out of scope |
| Stochastic volatility | Domain restrictions cannot be hidden in total L² multiplications | Genuine weighted energy spaces, transfer domains, and M-cylindrical graph-density analysis |

Mathematical gaps: verifying the test generators against a concrete δ, identifying
its adjoint with a genuine derivative, proving graph density, and proving the required
projection/weighted estimates. Lean implementation work: packaging a known graph topology,
Lp representative compatibility, and sequential Hölder convergence once those mathematical
hypotheses are available. An implementation difficulty is not evidence for any missing
mathematical claim.

### Every new declaration and its meaning

All names are in `OperatorDerivativeRewrite.Foundation`.

| Declaration | Precise meaning |
| --- | --- |
| `mem_adjoint_domain_iff_representable` | For dense δ-domain, F∈dom(δ*) iff a vector represents ⟨F,δu⟩ against every u∈dom(δ) |
| `bounded_adjoint_domain` | The partial adjoint of an everywhere-defined continuous δ has domain ⊤ |
| `closed_graph_limit` | Convergence of both inputs and actual operator outputs for a closed D proves limit membership and identifies D's value |
| `fourthMomentDomain` | Set of elements of the actual D-domain having both value and actual output in L⁴ |
| `fourthMomentDomain_product_terms` | Two such elements yield FG, F DG, G DF in L²; no product-domain membership or identity is asserted |
| `boundedMultiplier` | Continuous linear multiplication by a given MemLp-∞ real function on L²(H) |
| `boundedMultiplier_coeFn` | That map agrees a.e. with pointwise scalar multiplication |
| `boundedMultiplier_add` | M_(f+g) = M_f + M_g |
| `boundedMultiplier_mul` | M_(fg) = M_f composed with M_g |
| `boundedMultiplier_const` | M_c = c times the identity |
| `boundedMultiplier_symmetric` | Real bounded multipliers satisfy ⟨M_fu,v⟩ = ⟨u,M_fv⟩ |
| `IsDivergenceMultiplier` | Explicit δ-domain preservation and bounded divergence commutator, plus MemLp-∞ membership |
| `isDivergenceMultiplier_const` | Constants satisfy that criterion for every linear δ |
| `IsDivergenceMultiplier.add` | Sum admissibility, derived using R_f + R_g |
| `IsDivergenceMultiplier.mul` | Product admissibility, derived using M_f R_g + R_f M_g |
| `boundedMultiplierAlgebra` | Subalgebra whose carrier is exactly the above admissibility predicate; its algebra laws are proved |
| `isDivergenceMultiplier_bounded` | Every MemLp-∞ f is admissible for a continuous δ with whole-space domain |
| `divergenceCommutator_unique` | For dense δ-domain, two bounded commutators obeying the actual equation are equal |
| `adjoin_le_boundedMultiplierAlgebra` | Admissibility of generators implies admissibility of every element of their Mathlib-generated algebra |
| `IsDivergenceMultiplier.preserves_adjoint_domain` | Admissible f preserves the actual δ* domain, for dense δ-domain and complete H |
| `boundedToL2` | Canonical L² a.e. class of an essentially bounded scalar function on a finite measure space |
| `boundedToL2_coeFn` | That class agrees a.e. with its input function |
| `boundedToL2_mul` | The L² class of fg is M_f applied to the L² class of g |
| `one_mem_adjoint_domain` | Centered δ puts constant one in its adjoint domain, on a finite measure space with complete H |
| `IsDivergenceMultiplier.mem_adjoint_domain` | With centered, densely defined δ, each admissible bounded f has its actual L² class in dom(δ*) |
| `multiplierAlgebra_product_mem_adjoint_domain` | Under those hypotheses, every product in the chosen multiplier algebra has its actual L² class in dom(δ*) |
| `generatedAlgebra_product_mem_adjoint_domain` | The same product-domain conclusion for an algebra generated by any family satisfying the explicit δ-multiplier conditions |

Verification: `lake build` and `lake build Foundation.AxiomAudit` succeed. All 27
new definitions/theorems have explicit `#print axioms` commands and report only
`propext`, `Classical.choice`, `Quot.sound`. There is no `sorryAx` or custom axiom.
No original source, existing adjoint/product theorem, full cylindrical derivative
or Itô formula has been altered or implemented by this milestone.

## Genuine Gaussian polynomial core (continuation from 519ff572)

### Original defect and manuscript scope

`OperatorDerivative.lean:2939–2960` defines `CylindricalFunctional` with
independent `f_eval`, `df_eval`, `F`, and `dF`. Neither differentiability nor an
identity relating `df_eval` to the derivative of `f_eval` is required.
`malliavin_derivative_of_cylindrical` at 3005 sums these freely supplied data.
`IsonormalIsGaussian.per_coord_stein` at 3840 and `SteinLemma.stein` at 3903
assume the desired integration-by-parts identities for every such object.
The Gaussian marginal law alone cannot justify those fields. For example, in
one standard Gaussian coordinate, choose f=0 but df=1. Both are integrable and
satisfy the structure's evaluation specifications, yet the claimed Stein identity
would be 0=1. Thus this is a mathematical defect, not an API difficulty.

`cylindrical_compose` at 4892 prescribes the new coefficient as φ'(f)df.
`cylindrical_chain_rule` at 4920 closes by unfolding and `rfl`; it does not prove
that the original df is an actual derivative. Those constructions are not reused.
The manuscript (notably lines 100–104 and its cylindrical-core discussion near
703) intends smooth bounded finite-dimensional functions, an actual IBP formula,
and analytic closure/density arguments. Its intended statements are not silently
replaced by the smaller statements below. The originals remain unchanged.

### Precisely delimited first milestone

The new modules work on Ω=ℝ with γ=gaussianReal 0 1 and H=ℝ. The coordinate
W(h)(x)=hx has law N(0,h²), including the degenerate h=0 case. This is the
rank-one Gaussian model, not an arbitrary isonormal process on an arbitrary H.
A cylinder is F=p(W(h)), where p is an actual real polynomial. Pullback along
W(h) gives `coordinatePolynomial h p = p.comp (C h * X)`.
Every polynomial pullback is smooth and belongs to every finite Lp, by Mathlib's
Gaussian moment theorem; no integrability requirement is presumed without proof.
This polynomial core includes unbounded cylinders and is not the manuscript's
C_b^∞ core. No finite-dimensional generalization or infinite-dimensional result
is claimed here.

The derivative is the classical derivative of actual evaluation, transported
into Mathlib's L² classes. Its formula is DF(x)=p'(hx)h a.e. Equality of continuous
representatives a.e. for γ implies equality everywhere: γ and Lebesgue measure
are mutually absolutely continuous and Lebesgue measure is positive on open sets.
Consequently different polynomial and coordinate representations of the same F
have equal derivatives as L² classes. This includes h=0; no division by h or
nondegeneracy assumption on the chosen coordinate is needed.

The polynomial derivative and divergence are actual `LinearPMap`s with the same
algebraic domain C=range(polynomialEmbedding), not separately specified outputs.
Their graphs are respectively {(p,p')} and {(q,xq-q')} in Gaussian L²×L². We prove
that these graphs determine functions before invoking `Submodule.toLinearPMap`
(which otherwise has a fallback zero map). Products remain in C because they
are actual polynomials with all finite Gaussian moments. Product membership is
proved separately from the derivative's Leibniz equality.

Gaussian IBP is proved by differentiating the explicit Gaussian density and
applying Mathlib's integration by parts on the real line. The hypotheses of that
analytic theorem—integrability of pρ, p'ρ, and xpρ—are all derived from the
Gaussian moment estimates. The resulting identities are

- ∫ xp dγ = ∫ p' dγ;
- ⟨Dp,q⟩ = ⟨p,δq⟩, where δq=xq-q'.

Closability of D in all of L²(γ) is proved without a polynomial-density assumption.
The IBP identity extends continuously to the closure of its graph. For a vertical
limit (0,v), it implies ⟨v,q⟩=0 for every polynomial q. Also v belongs to the
closure of the polynomial subspace, since every derivative p' is polynomial.
Continuity extends the orthogonality to that closed subspace, including v itself;
thus ⟨v,v⟩=0 and v=0. The graph closure therefore is the graph of a genuine
operator, and Mathlib's operator closure is closed.

### Exact meanings of new declarations

All names below are in `OperatorDerivativeRewrite.Foundation.GaussianCore`.

| Declaration | Verified mathematical meaning |
|---|---|
| `γ` | Standard real Gaussian probability measure |
| `polynomial_memLp` | p(x) belongs to L^r(γ) for every r≠∞, including r=0 |
| `polynomial_smooth` | Polynomial evaluation is C^∞ |
| `polynomial_hasDerivAt` | Its actual classical derivative is p'(x) |
| `continuous_representation_unique` | Continuous functions equal γ-a.e. are equal pointwise |
| `derivative_representation_independent` | Polynomial evaluations equal a.e. have identical derivative evaluations |
| `derivative_product` | Actual classical derivative of p(x)q(x) is p'q+pq' |
| `derivative_chain` | Actual derivative of p(q(x)) is p'(q(x))q'(x) |
| `density_hasDerivAt` | Standard Gaussian density has derivative -xρ(x) |
| `integrable_density_mul` | Gaussian integrability implies Lebesgue integrability after multiplication by ρ |
| `polynomial_stein` | Unconditional Stein identity for every polynomial p |
| `divergencePolynomial` | Actual polynomial xq-q' |
| `polynomial_integration_by_parts` | ∫p'q dγ = ∫p(xq-q') dγ |
| `W` | Actual coordinate function hx |
| `W_gaussian_law` | Its pushforward law is N(0,h²) |
| `coordinatePolynomial` | Actual polynomial pullback p(hx) |
| `coordinatePolynomial_eval` | Evaluation equals p(W(h)(x)) |
| `cylindrical_hasDerivAt` | Actual chain derivative is p'(W(h)(x))h |
| `coordinate_not_memLp_top` | x↦x is not in L∞(γ) |
| `GaussianL2` | Mathlib's real L²(γ) Hilbert space |
| `polynomialL2` | Canonical L² class of actual polynomial evaluation |
| `polynomialL2_coeFn` | The class agrees a.e. with polynomial evaluation |
| `polynomialEmbedding` | Linear evaluation map from real polynomials into L²(γ) |
| `polynomialEmbedding_injective` | Equality of polynomial L² classes implies equality of polynomials |
| `polynomialL2_inner` | Their Hilbert pairing is ∫pq dγ |
| `polynomialL2_integration_by_parts` | The genuine polynomial IBP in Hilbert-space notation |
| `derivativeGraph` | Linear range of p↦([p],[p']) |
| `derivativeGraph_vertical_zero` | That range has no nonzero vertical elements |
| `polynomialDerivative` | Partially defined derivative reconstructed from the verified graph |
| `polynomialDerivative_graph` | Its graph is exactly derivativeGraph, not the fallback zero construction |
| `polynomialDerivative_polynomial` | ([p],[p']) belongs to the actual derivative graph |
| `closed_graph_ibp` | IBP holds for every pair in the graph closure and every polynomial test |
| `closed_derivativeGraph_vertical_zero` | The graph closure has no nonzero vertical elements |
| `polynomialDerivative_isClosable` | Genuine closability in all of Gaussian L² |
| `polynomialDerivative_closure_isClosed` | Mathlib's graph closure of D is closed |
| `divergenceLinear` | Linearity of q↦xq-q' |
| `divergenceGraph` | Linear range of q↦([q],[xq-q']) |
| `divergenceGraph_vertical_zero` | That range also determines a genuine operator |
| `polynomialDivergence` | Genuine partially defined polynomial divergence |
| `polynomialDivergence_graph` | Its graph equals divergenceGraph |
| `polynomialDerivative_formalAdjoint` | D and δ obey the formal-adjoint identity on their actual domains |
| `polynomial_mem_divergence_adjoint_domain` | Every polynomial lies in the actual δ* domain, via its proven derivative representer |
| `polynomial_product_graph` | ([pq],[p'q]+[pq']) belongs to D's graph: genuine closure and Leibniz rule |
| `cylindricalL2` | Actual L² class F=p(W(h)) |
| `cylindricalL2_coeFn` | Its a.e. evaluation formula |
| `cylindricalDerivativeL2` | Derivative of the actual pullback polynomial as an L² class |
| `cylindrical_operator_graph` | The cylinder and this derivative belong to D's actual graph |
| `cylindricalDerivativeL2_coeFn` | DF=p'(W(h))h a.e. |
| `cylindrical_representation_independent` | Equal F represented by (h,p) and (k,q) have equal derivative L² classes |
| `coordinate_not_admissible` | x↦x fails the previous IsDivergenceMultiplier criterion |
| `constant_admissible` | Constants satisfy that criterion for the genuine polynomial divergence |
| `polynomialDerivative_domain` | dom D equals the algebraic polynomial L² range |
| `polynomialDivergence_domain` | dom δ equals that same range |

### Multiplier and adjoint conclusions; remaining analytic obligations

The polynomial algebra has genuine product closure, but does not generally
satisfy the bounded-multiplier criterion of the previous milestone. Already
W(1)=x is not essentially bounded, as proved using Gaussian full support and
continuity; hence it cannot satisfy `IsDivergenceMultiplier`. Constants do satisfy
the full criterion, including domain preservation. We do not assert that all
polynomials are bounded multipliers, or that arbitrary bounded smooth functions
preserve the polynomial δ-domain. For example, multiplication by sin(x) sends
constant 1 outside that algebraic polynomial domain. The latter observation is
mathematical explanation, not an additional Lean theorem in this milestone.
A nonconstant bounded smooth core needs an appropriate divergence test domain
and a proof of the commutator's boundedness and domain preservation.

The proven formal-adjoint identity and polynomial membership in dom δ* are
an exact connection with the adjoint foundation at this stage. Identifying
δ*([p]) with [p'] as the value of Mathlib's adjoint requires a dense δ-domain.
Polynomial density in all L²(γ) is mathematically true but is NOT proved or assumed
in these modules. This matters because Mathlib's `LinearPMap.adjoint` uses a
fallback zero value for nondense domains. Neither formal adjointness nor an
existing derivative representer alone licenses claiming equality of that value.
After proving density, the existing `LinearPMap.adjoint_apply_eq` will identify
δ* on the core. Equality of δ* with the closed derivative on its full domain
requires a further argument establishing maximality/core properties; it is not
claimed merely from an inclusion on polynomials.

Remaining work: polynomial density; exact adjoint identification on the core;
full-domain identification if intended; multivariate joint Gaussian IBP and
representation independence for arbitrary finite cylinders (including redundant
coordinates); extension to arbitrary H and isonormal processes; bounded smooth
cylinders and their genuine divergence-domain multiplier estimates; closure
chain/product rules under the proper L⁴ or bounded-factor hypotheses. No Itô,
Clark–Ocone, PRP, or stochastic Fubini assertion follows from this milestone.
The old cylindrical constructions and assumption-based Stein classes remain
unported. Original scalar–constant-vector multiplication and the adjoint
infrastructure remain reusable after the missing hypotheses are actually proved.

Verification: `lake build` and `lake build Foundation.AxiomAudit` succeed.
`lake env lean Foundation/AxiomAudit.lean` checks every declaration explicitly.
All 53 new declarations, including definitions and abbreviations, have axiom
queries. Their dependencies are contained in `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or custom axiom occurs. All 111 declarations in the
combined foundation audit report that same allowed union. A source scan finds
no `sorry`, `admit`, or custom axiom in the foundation modules. Original SHA-256
hashes remain unchanged: Lean `9B8BA956878B80F3C2AC8F239D335C0F49582C88D0693E63554F481ACBEBDF29`;
manuscript `FCA841CCA43DC712AAD2FCF02CB04010ABD7CFCDA4A231022D58A3B23D3BB983`.

## Gaussian density and adjoint inclusions (continuation from aac876f)

### Operator directions and exact domains

Write C=range(polynomialEmbedding) in L²(γ), γ=N(0,1). The original verified
operators are D₀=polynomialDerivative and δ₀=polynomialDivergence, both maps
L²(γ) ⇀ L²(γ) with domain exactly C. Their graphs contain ([p],[p']) and
([q],[xq-q']), respectively. The IBP orientation is ⟨D₀p,q⟩=⟨p,δ₀q⟩.
In particular the derivative is contained in the divergence's adjoint, not in
its own adjoint. Neither algebraic operator is identified with a closed operator
merely from its name or domain density.

### Noncircular density proof now verified

`Foundation/GaussianDensity.lean` proves `polynomialEmbedding_dense` in the whole
Gaussian L² space. The proof does not assume any adjoint identity, Hermite basis,
or density theorem for a graph norm. Searches found compact-set Weierstrass
approximation but no direct Gaussian L² polynomial-density theorem in this
Mathlib checkout. Compact approximation alone would not control polynomial growth
outside the compact set.

First, `finite_measure_eq_of_moments` proves a reusable determinacy result for
finite measures on ℝ with integrable exp(tx) for every real t. Their complex MGFs
are entire by Mathlib's `analyticAt_complexMGF`. The moments determine all complex
derivatives at zero by `iteratedDeriv_complexMGF`; the entire Taylor-series
theorem then makes the MGFs equal everywhere. Mathlib's
`Measure.ext_of_complexMGF_id_eq` turns this into equality of measures. This is
an analytic proof of moment determinacy, not an assumption of it. Requiring
exponential moments is essential: finite moments alone do not generally determine
a measure.

For f∈L²(γ) orthogonal to polynomials, define w₊=max(f,0) and w₋=max(-f,0), and
finite positive measures ν₊=w₊γ and ν₋=w₋γ. The weights belong to L² and L¹.
Gaussian exp(tx) belongs to L² because its squared norm integrates exp(2tx),
whose integrability is already proved in Mathlib. The previous foundation's
`mul_L2_integrable` therefore proves every exponential moment of ν₊ and ν₋.
The same estimate proves integrability of w₊xⁿ and w₋xⁿ. Orthogonality to xⁿ
makes their moments equal. Moment determinacy gives ν₊=ν₋; uniqueness of
withDensity densities gives w₊=w₋ a.e., hence f=0. Finally, the orthogonal
complement of the closed polynomial subspace is zero, so Hilbert projection
implies that subspace is all L²(γ). No desired operator equality appears in this
argument or its hypotheses.

### Exact proved operator conclusions

Define D̄=closure(D₀) and δ̄=closure(δ₀), meaning closure of their graphs in
L²(γ)×L²(γ), reconstructed as genuine single-valued operators. D₀'s closability
was proved in the previous milestone. δ₀'s closability is now proved from its
inclusion in the closed operator D₀*. All four operators D₀, δ₀, D̄, δ̄ have
dense domains; D̄ and δ̄ are closed.

The following are verified inclusions of `LinearPMap`s, so each includes both
operator-domain inclusion and equality of the values on the smaller domain:

- D₀ ⊆ δ₀* and δ₀ ⊆ D₀*;
- D̄ ⊆ δ₀* and δ̄ ⊆ D₀*;
- D̄ ⊆ δ̄* and δ̄ ⊆ D̄*.

The following equalities are also verified: D̄*=D₀* and δ̄*=δ₀*. These are
invariance of each operator's adjoint under its own graph closure. They are not
an identification of D̄ with δ₀*, or of δ̄ with D₀*.
Integration by parts extends to the two closed domains:
∀f∈dom D̄, ∀u∈dom δ̄, ⟨D̄f,u⟩=⟨f,δ̄u⟩.

Every polynomial belongs to dom D̄ and D̄[p]=[p']. It also belongs to dom δ̄
with δ̄[p]=[xp-p']. The actual values δ₀*[p]=[p'] and D₀*[p]=[xp-p'] are now
established on the polynomial core via graph membership; the nondense-domain
fallback previously noted is ruled out by the new density proof. For a genuine
cylinder F=p(W(h)), membership in dom D̄ is proved separately, and D̄F agrees
a.e. with p'(W(h))h for any chosen proof of that membership.

### Why full identification is not claimed

D₀⊆δ₀* follows from IBP and dense δ₀-domain. Since δ₀* is closed, closability
then gives D̄⊆δ₀*. Neither step proves the reverse inclusion δ₀*⊆D̄.
The missing statement is polynomial graph-norm density in dom δ₀*: for every
(f,v)∈graph δ₀*, polynomial pairs ([pₙ],[pₙ']) must converge to (f,v).
Similarly, δ̄=D₀* requires polynomial divergence pairs ([qₙ],[xqₙ-qₙ']) to
approximate every graph pair of D₀*.

The polynomial domain is proved to be a core of D̄ and δ̄, their own closures.
That fact is a consequence of the definition of graph closure. It does NOT prove
that it is a core of δ₀* or D₀*, which may have larger graph domains. Ordinary
L² density concerns only first components and does not prove either graph
approximation. The three assertions D₀⊆δ₀*, D̄=δ₀*, and δ̄=D₀* are therefore
not substituted for one another. General biadjoint/closure duality can relate
the two equality assertions under suitable densely defined closable hypotheses,
but that is additional reasoning, not a consequence of formal adjointness alone.

A concrete route to full one-dimensional identification is normalized Hermite
expansion. Mathlib contains the probabilists' Hermite polynomials and their
Gaussian differentiation formula (`RingTheory/Polynomial/Hermite`), but those
files do not supply Gaussian orthogonality, an L² Hermite Hilbert basis, or the
needed graph approximation theorem. A next development could prove
hₙ=Heₙ/√(n!) is a complete orthonormal family, D₀hₙ=√n hₙ₋₁, and
δ₀hₙ=√(n+1) hₙ₊₁. Adjointness would determine weighted coefficient sequences;
finite Hermite truncations would then converge in both graph components. This
would supply the missing reverse inclusions. This paragraph is a proof strategy,
not a list of already verified Hermite theorems.

The milestone stops at the proved closed inclusions; no equality D̄=δ₀* or
δ̄=D₀* is asserted as Lean-verified. No arbitrary-domain assumption equivalent
to either equality has been introduced.

### New declaration meanings

All Gaussian names are in `OperatorDerivativeRewrite.Foundation.GaussianCore`.
The four general lemmas are in `OperatorDerivativeRewrite.Foundation`.

| Declaration | Exact meaning |
|---|---|
| `finite_measure_eq_of_moments` | Finite real measures with every exponential moment and equal polynomial moments are equal |
| `gaussian_exp_memLp_two` | exp(tx)∈L²(γ) for every t |
| `weightedMeasure` | Positive measure μ.withDensity(ofReal w) |
| `weighted_integrable_iff` | For measurable w≥0, g is integrable for wμ iff wg is integrable for μ |
| `weighted_integral` | For such w, ∫g d(wμ)=∫wg dμ |
| `weighted_finite` | A measurable nonnegative integrable density defines a finite measure |
| `eq_zero_of_polynomial_orthogonal` | An L²(γ) function orthogonal to every polynomial is zero |
| `polynomialEmbedding_dense` | The polynomial range is dense in all Gaussian L² |
| `operatorClosure_le_closed` | A closable operator's graph closure lies in every given closed extension |
| `operatorClosure_dense_domain` | Dense original domain implies dense closure domain |
| `formalAdjoint_closure_left` | A genuine formal-adjoint identity extends to the closure of the first operator |
| `operatorClosure_adjoint_eq` | Closing a densely defined closable real Hilbert-space operator leaves its adjoint unchanged |
| `polynomialDerivative_dense_domain` | dom D₀ is dense |
| `polynomialDivergence_dense_domain` | dom δ₀ is dense |
| `polynomialDerivative_le_divergence_adjoint` | D₀⊆δ₀* as actual operators |
| `polynomialDivergence_le_derivative_adjoint` | δ₀⊆D₀* as actual operators |
| `polynomialDivergence_isClosable` | δ₀ has a single-valued graph closure |
| `closedDerivative`, `closedDivergence` | Graph closures D̄ and δ̄ of the actual polynomial operators |
| `closedDerivative_isClosed`, `closedDivergence_isClosed` | Both graph closures are closed operators |
| `closedDerivative_dense_domain`, `closedDivergence_dense_domain` | Both closed operators have dense domains |
| `closedDerivative_le_divergence_adjoint` | D̄⊆δ₀* |
| `closedDivergence_le_derivative_adjoint` | δ̄⊆D₀* |
| `closedDerivative_formalAdjoint` | IBP between all members of the two closed domains |
| `closedDerivative_polynomial_graph` | ([p],[p'])∈graph D̄ |
| `closedDivergence_polynomial_graph` | ([p],[xp-p'])∈graph δ̄ |
| `divergence_adjoint_polynomial_graph` | ([p],[p'])∈graph δ₀* |
| `derivative_adjoint_polynomial_graph` | ([p],[xp-p'])∈graph D₀* |
| `closedDerivative_has_polynomial_core` | C is a graph core for D̄ itself |
| `closedDivergence_has_polynomial_core` | C is a graph core for δ̄ itself |
| `closedDerivative_adjoint_eq` | D̄*=D₀* |
| `closedDivergence_adjoint_eq` | δ̄*=δ₀* |
| `closedDerivative_le_closedDivergence_adjoint` | D̄⊆δ̄* |
| `closedDivergence_le_closedDerivative_adjoint` | δ̄⊆D̄* |
| `closedDerivative_polynomial_mem` | Membership of every polynomial in dom D̄ |
| `closedDerivative_polynomial_apply` | D̄[p]=[p'] for any proof of membership |
| `closedDerivative_cylindrical_mem` | Membership of every existing one-coordinate polynomial cylinder in dom D̄ |
| `closedDerivative_cylindrical_coeFn` | Its closed derivative is p'(W(h))h a.e. |

The closure/formal-adjoint lemmas apply to general real inner-product spaces
(and complete spaces where actual adjoints are used), so are reusable for scalar
and vector-valued multivariate domains. Moment determinacy applies to arbitrary
finite measures on ℝ with exponential moments, not only γ. Multivariate density,
Hermite tensor bases, and their graph norms remain future work.

Verification for this milestone: `lake build` and `lake build Foundation.AxiomAudit`
both succeed. All 40 new declarations have explicit axiom queries; the combined
151-declaration audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorryAx`, custom axioms, `sorry`, or `admit` occur. The new modules emit no
compiler or linter warnings; the pre-existing unused-section-variable warnings
in `Foundation.Adjoint` remain. The original Lean and manuscript hashes are
unchanged, and the prior verified Gaussian core modules have not been modified.

## Hermite spectral identification (continuation of 68d3189)

This section resolves the one-dimensional graph-core and adjoint-identification
obligations recorded in the preceding milestone. The underlying measure is still
γ = N(0,1), and the original polynomial operators are unchanged:

- dom D₀ = dom δ₀ = C = polynomialEmbedding.range;
- D₀[p] = [p']; δ₀[p] = [xp-p'];
- D̄ and δ̄ are their actual graph closures as Mathlib `LinearPMap`s.

### Construction and proof dependencies

`Foundation/GaussianHermite.lean` maps Mathlib's integer-coefficient
`Polynomial.hermite n` to real coefficients. Its recursion is precisely
H₀ = 1, Hₙ₊₁ = xHₙ-Hₙ'. The lowering formula Hₙ₊₁' = (n+1)Hₙ is proved
by induction using the actual polynomial commutator Dδp = p+δDp.
Gaussian integration by parts then yields
⟨Hₙ,Hₘ⟩ = 1_{n=m} n!, including the probability normalization at degree zero.
No Rodrigues formula, Gaussian orthogonality, or spectral identity is assumed.

Define eₙ = [Hₙ]/√(n!). Positivity of n! proves that these normalizers are
nonzero. The eₙ are orthonormal. Monicity and degree Hₙ = n give an algebraic
polynomial sequence spanning all real polynomials via Mathlib
`Polynomial.Sequence.span`. Consequently span{eₙ} = C. The independently
proved `polynomialEmbedding_dense` supplies completeness; Mathlib
`HilbertBasis.mk` gives a genuine isometric coefficient representation in ℓ².
In particular, cₙ(f) = ⟨eₙ,f⟩, and f = Σ cₙ(f)eₙ in L².

The verified actual polynomial graph actions are
D₀e₀ = 0, D₀eₙ₊₁ = √(n+1)eₙ, δ₀eₙ = √(n+1)eₙ₊₁.
All these vectors already have justified L² integrability from the polynomial
moment theorem. Coefficients and derivative values are never prescribed
independently of the functions.

### Spectral argument for the missing graph cores

Let P_N f = Σ_{n<N} cₙ(f)eₙ. These truncations converge to f in L² for every
f, without any operator assumption.

For (f,g) in graph δ₀*, test the actual adjoint identity against eₙ in dom δ₀.
It forces cₙ(g) = √(n+1)cₙ₊₁(f). The lowering actions give, by finite induction,
(P_{N+1}f, P_N g) in graph D₀. Both components converge to (f,g), so this pair
belongs to graph D̄. This proves δ₀* ⊆ D̄; combine with the already proved
opposite inclusion to obtain D̄ = δ₀*.

For (f,g) in graph D₀*, testing e₀ and eₙ₊₁ forces c₀(g)=0 and
cₙ₊₁(g)=√(n+1)cₙ(f). The raising actions give
(P_N f, P_{N+1}g) in graph δ₀, converging to (f,g). Hence D₀* ⊆ δ̄ and,
using the previous opposite inclusion, δ̄ = D₀*.

These are separate verified approximation arguments in the two directions.
They use only Hilbert-basis completeness, the true adjoint graph equation, and
the actual ladder actions. Graph-norm density is a conclusion, never a
hypothesis. The conditional coefficient-to-graph lemmas are sufficiency
proofs by explicit approximation; necessity is proved by adjoint testing.
Together they give exact graph characterizations, not a conditional operator
interface. Product-topology convergence of input and output is equivalent to
convergence in the Hilbert graph norm √(‖input‖²+‖output‖²).

Closing either densely defined operator leaves its adjoint unchanged, so the
strongest proved identities are

    D̄ = δ₀* = δ̄*,       δ̄ = D₀* = D̄*.

The pre-existing polynomial graph and application theorems still identify
D̄[p]=[p'] and δ̄[p]=[xp-p']; the equalities therefore preserve exactly the
original polynomial operators. The previous classical cylindrical derivative
formula also remains valid. No original source or manuscript was edited.

### Exact weighted domains and norms

Parseval is proved as `HasSum (fun n => cₙ(f)^2) ‖f‖²`. Conversely, every
square-summable real sequence is realized by the inverse Hilbert-basis
isometry. This is a theorem, not an existence or integrability assumption.

The closed graph characterizations imply, for f already in Gaussian L²,

    f ∈ dom D̄  ↔  Σ n cₙ(f)² < ∞,
    f ∈ dom δ̄  ↔  Σ (n+1)cₙ(f)² < ∞.

Lean expresses these convergent real series with `Summable`. The two domains
are proved equal because Σ cₙ(f)² is already finite. Their output norms and
Hilbert graph norms are exactly

    ‖D̄f‖² = Σ n cₙ(f)²,
    ‖δ̄f‖² = Σ (n+1)cₙ(f)²,
    ‖f‖² + ‖D̄f‖² = Σ (n+1)cₙ(f)²,
    ‖f‖² + ‖δ̄f‖² = Σ (n+2)cₙ(f)².

`HasCore` is established for span{eₙ} in each full adjoint domain. The two
explicit approximation theorems additionally exhibit the polynomial graph
sequences and their convergence for every adjoint graph pair.

### Meaning of all new public declarations

All names below are in `OperatorDerivativeRewrite.Foundation.GaussianCore`.
The two private inner-product recurrence lemmas are proved by IBP and are
included transitively in the axiom audit of `hermiteVector_inner`.

| Declaration | Precise meaning |
|---|---|
| `hermitePolynomial` | Real-coefficient image of Mathlib's probabilists' Hₙ |
| `hermitePolynomial_zero` | H₀=1 |
| `hermitePolynomial_succ` | Hₙ₊₁=δHₙ for the original differential expression |
| `derivative_divergencePolynomial` | (xp-p')'=p+xp'-p'' |
| `hermitePolynomial_derivative` | Hₙ₊₁'=(n+1)Hₙ |
| `hermitePolynomial_monic`, `hermitePolynomial_degree` | Hₙ is monic of degree n |
| `hermiteSequence` | The Hermites as Mathlib's degree-indexed polynomial sequence |
| `hermitePolynomial_span` | All real polynomials are finite algebraic Hermite expansions |
| `hermiteVector` | Hₙ evaluated as a Gaussian L² equivalence class |
| `hermiteVector_inner` | ⟨Hₙ,Hₘ⟩=1_{n=m}n! |
| `normalizedHermite` | eₙ=[Hₙ]/√(n!) |
| `hermite_normalizer_pos`, `hermite_normalizer_succ` | Positive √(n!) and its square-root recursion |
| `normalizedHermite_orthonormal` | The eₙ form an orthonormal family |
| `hermiteVector_span`, `normalizedHermite_span` | Each algebraic vector span is exactly C |
| `normalizedHermite_dense_span` | Density of that span in Gaussian L² |
| `hermiteBasis` | The complete normalized Hermite Hilbert basis |
| `hermiteBasis_apply` | Its vectors are precisely eₙ |
| `hermiteBasis_coefficient` | Its isometry coordinates equal ⟨eₙ,f⟩ |
| `hermiteBasis_hasSum` | The coefficient expansion converges unconditionally to f in L² |
| `normalizedHermite_derivative_graph` | (eₙ₊₁,√(n+1)eₙ) belongs to graph D₀ |
| `normalizedHermite_derivative_zero_graph` | (e₀,0) belongs to graph D₀ |
| `normalizedHermite_divergence_graph` | (eₙ,√(n+1)eₙ₊₁) belongs to graph δ₀ |
| `hermiteCoefficient` | The actual real Hilbert pairing cₙ(f) |
| `hermiteTruncation` | P_N f, its actual finite expansion |
| `hermiteTruncation_zero`, `hermiteTruncation_succ` | Empty sum and addition of the next Hermite term |
| `hermiteTruncation_tendsto` | P_N f→f in L² for every f |
| `divergence_adjoint_coefficients` | Necessary lowering coefficient equation for graph δ₀* |
| `derivative_adjoint_coefficient_zero` | Necessary zero-mode equation c₀(g)=0 for graph D₀* |
| `derivative_adjoint_coefficients` | Necessary raising coefficient equation for graph D₀* |
| `hermiteTruncation_derivative_graph` | Lowering coefficient equations produce actual finite D₀ graphs |
| `hermiteTruncation_divergence_graph` | Raising equations and the zero mode produce actual finite δ₀ graphs |
| `closedDerivative_graph_of_coefficients` | Those lowering equations suffice for membership in graph D̄ |
| `closedDivergence_graph_of_coefficients` | Those raising equations and the zero mode suffice for graph δ̄ |
| `closedDerivative_eq_divergence_adjoint` | Full operator equality D̄=δ₀* |
| `closedDivergence_eq_derivative_adjoint` | Full operator equality δ̄=D₀* |
| `closedDerivative_eq_closedDivergence_adjoint` | Full operator equality D̄=δ̄* |
| `closedDivergence_eq_closedDerivative_adjoint` | Full operator equality δ̄=D̄* |
| `closedDerivative_graph_iff`, `closedDivergence_graph_iff` | Exact necessary-and-sufficient spectral graph equations |
| `hermiteCoefficient_hasSum_sq` | Parseval, including square summability and the L² norm |
| `exists_hermite_coefficients` | Existence of an L² vector for any square-summable real sequence |
| `hermite_weight_square` | (√(n+1)a)²=(n+1)a² |
| `closedDerivative_domain_iff` | dom D̄ is exactly the n-weighted coefficient domain |
| `closedDivergence_domain_iff` | dom δ̄ is exactly the (n+1)-weighted coefficient domain |
| `closedDerivative_domain_eq_closedDivergence_domain` | These two closed domains coincide |
| `closedDerivative_norm_sq`, `closedDivergence_norm_sq` | Exact output-norm squared formulas on each closed graph |
| `closedDerivative_graph_norm_sq`, `closedDivergence_graph_norm_sq` | Exact Hilbert graph-norm squared formulas |
| `divergence_adjoint_has_hermite_core`, `derivative_adjoint_has_hermite_core` | Finite Hermite expansions are graph cores for the two full adjoints |
| `divergence_adjoint_hermite_approximation` | Explicit D₀ graph approximants and their joint convergence for each δ₀* graph pair |
| `derivative_adjoint_hermite_approximation` | Explicit δ₀ graph approximants and their joint convergence for each D₀* graph pair |

### Downstream consequences and remaining scope

The one-dimensional adjoint and graph-core gaps are fully resolved for the
standard-Gaussian polynomial operators. They can now serve as actual closed
operators in the existing adjoint framework. This does not prove that the
common closed domain is an algebra, that its functions are bounded, or that
polynomial multiplication is an admissible bounded commutator. The verified
L² product restrictions and the obstruction for the unbounded coordinate
continue to apply.

Multivariate Gaussian tensor bases, directional/vector-valued operators,
representation independence across arbitrary finite Gaussian coordinate
systems, bounded smooth cylindrical domains, admissible nonconstant
multipliers, and the Itô formula remain distinct future obligations. A tensor
Hermite basis and the corresponding directional weighted sums are the natural
next step. No such multivariate or stochastic claims are asserted here.

Verification: the complete `lake build`, `lake build Foundation.AxiomAudit`,
and a fresh `lake env lean Foundation/AxiomAudit.lean` all succeed. The 57 new
public declarations have explicit `#print axioms` queries;
together with the existing 151 queries, the audit covers 208 declarations and
all their transitive proof dependencies. The audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms occur.
The new modules have no compiler/linter warnings; the
pre-existing unused-section-variable warnings in `Foundation.Adjoint` remain.

## Finite-dimensional Gaussian cylinder foundation (continuation of a2ccf4b)

This is a deliberately bounded first finite-dimensional milestone: actual
Gaussian coordinates, a representation-independent polynomial L² gradient,
and independent tensor Hermite orthogonality. It does not assert multivariate
polynomial density, tensor completeness, gradient closability, or any
multivariate adjoint identity. Those remain proof obligations, not hypotheses
of an abstract interface. No existing result or original source was changed.

### Ambient measure and mathematical assumptions

Let E be a finite-dimensional real inner-product space with its Borel measurable
structure. No positive dimension or nondegeneracy of a coordinate family is
required. `gaussianMeasure E` is Mathlib's `ProbabilityTheory.stdGaussian E`;
it is not a new axiomatic Gaussian process. For h in E, define W(h)(x)=⟨h,x⟩.
The exact marginal is N(0,‖h‖²), and Cov(W(h),W(k))=⟨h,k⟩. The finite
coordinate family is a continuous linear map, and its pushforward measure is
proved Gaussian. Finite linear relations among the hᵢ hold pointwise among
W(hᵢ). This includes zero vectors, duplicate coordinates, and singular Gram
matrices without pretending they have nondegenerate densities.

For an orthonormal basis b, the coordinate vector (W(bᵢ)) has exactly the
independent product law ∏ᵢγ. This theorem is restricted to orthonormal
coordinates. The law of an arbitrary finite family h has Gram covariance
⟨hᵢ,hⱼ⟩ and may be correlated or supported on a proper linear subspace;
independent tensor formulas are not transferred to that law without proof.

The ambient measure stdGaussian E does have full support. This is proved from
Mathlib's orthonormal product realization, positivity of one-dimensional
Gaussian measure on nonempty open sets, positivity of finite products, and
surjectivity/continuity of orthonormal synthesis. It is used on E, never on a
potentially singular coordinate image.

The scalar polynomial and analytic lemmas do not require finite-dimensional E.
Actual Gaussian statements here do require finite-dimensional E: there is no
standard Gaussian measure on an arbitrary infinite-dimensional Hilbert space
with identity covariance. An isonormal process over an infinite-dimensional
space requires a different probability-space construction and consistency
arguments. No such process or infinite-dimensional Malliavin operator is
claimed by these definitions.

### Genuine derivatives and representation independence

For any finite family h:ι→E and actual `MvPolynomial ι ℝ` p, define

    F(x) = p(W(h₁)(x),...,W(hₙ)(x)),
    G(x) = Σᵢ (∂ᵢp)(W(h)(x)) hᵢ.

The formal partial derivatives are Mathlib's `MvPolynomial.pderiv`, and are
not independently supplied values. Induction on the polynomial proves
`HasFDerivAt F (innerSL ℝ (G x)) x` for every x. Thus G is verified as the
actual Hilbert gradient. Smoothness of F and the analytic product rule are
proved from actual polynomial evaluation and continuous linear coordinates.
The polynomial gradient formula is not itself used as an assumed chain rule.

For cylinders using a common finite family, the gradient product identity is

    ∇(FG) = F∇G + G∇F.

All finite Lp moments of coordinates, cylinders, and their Hilbert-valued
gradients are proved. The multiplication step uses the verified Hölder
infrastructure at exponents 2r,2r→r. Scalar multiplication by the fixed hᵢ
uses Lr×L∞→Lr, and the finite sum gives gradient membership. In particular,
F,G,∇F,∇G are in L⁴ and the product expressions above are in L². No closure
of arbitrary L² under multiplication is invoked. No L∞ membership of a
nonconstant polynomial is asserted.

Suppose p(W(h)) and q(W(k)) agree stdGaussian E-almost everywhere, with
possibly different finite index sets and dependent families. Their continuous
ambient representatives agree everywhere by the proved full support.
Their actual Fréchet derivatives therefore agree; injectivity of the real
Hilbert-to-dual isometry gives equality of the ambient gradients everywhere.
The result is also proved for the actual scalar/vector L² equivalence classes.
This establishes well-defined gradient values independently of any choice of
cylindrical representation.

For example, if h₁=h₂, p(z₁,z₂)=z₁-z₂ represents the zero variable although
its formal coordinate partials are (1,-1). Its genuine ambient gradient is
h₁-h₂=0. Equality of raw coordinate partial arrays is not the required notion
of representation independence. The theorem proves equality of the weighted
ambient vector, so it handles exactly this degeneracy.

### Independent tensor polynomial construction

`FiniteGaussianTensor.lean` defines Hₙ/√(n!) as an actual real polynomial
whose one-dimensional L² class is the previously verified normalized Hermite
basis vector. For finite multi-index α:ι→ℕ, define

    e_α(x) = ∏ᵢ H_{αᵢ}(xᵢ)/√(αᵢ!),    x ∈ ℝ^ι,    measure ∏ᵢγ.

Every partial product has all finite moments by Hölder induction; every full
tensor is therefore a justified L² vector. Product-measure Fubini and the
verified one-dimensional Hermite integrals give

    ⟨e_α,e_β⟩ = 1_{α=β}.

This proves an orthonormal family, including the empty-index case. It does
not prove that this family is a Hilbert basis. No `HilbertBasis.mk` is applied
with an unproved density assumption. The one-dimensional complete basis is
reused for its exact normalization and orthogonality, while its completeness
has not yet been lifted through product L².

### Meaning of all new declarations

All names below are in `OperatorDerivativeRewrite.Foundation.FiniteGaussian`.

| Declaration | Mathematical meaning |
|---|---|
| `gaussianMeasure` | Mathlib's basis-independent standard Gaussian on finite-dimensional E |
| `coordinate`, `coordinate_apply` | The continuous linear functional W(h)=⟨h,·⟩ and its pointwise value |
| `gaussianMeasure_openPos` | Positivity of the ambient Gaussian on every nonempty open set |
| `continuous_ae_eq` | Continuous scalar ambient representatives equal a.e. are equal everywhere |
| `coordinate_memLp` | Every W(h) has every finite Lp moment |
| `coordinate_gaussian_law` | W(h) has the exact possibly degenerate marginal N(0,‖h‖²) |
| `coordinate_covariance` | Cov(W(h),W(k))=⟨h,k⟩ |
| `coordinate_add`, `coordinate_smul`, `coordinate_linear_relation` | True pointwise linear relations among coordinates |
| `gaussianMeasure_eq_product_map` | Product-Gaussian realization through any orthonormal basis |
| `coordinateFamily` | The finite joint coordinate continuous linear map |
| `coordinateFamily_isGaussian` | Gaussianity of its pushforward, with no rank assumption |
| `orthonormal_coordinates_joint_law` | Exact independent product law for an orthonormal basis family |
| `cylinder` | Actual multivariate polynomial evaluation at W(h) |
| `cylinderGradient` | The computed vector Σᵢ(∂ᵢp)(W(h))hᵢ |
| `cylinder_C`, `cylinder_X`, `cylinder_add`, `cylinder_mul` | Evaluation respects constants, variables, addition, and multiplication |
| `cylinderGradient_C`, `cylinderGradient_X`, `cylinderGradient_add` | Computed constant/coordinate gradients and additivity |
| `cylinderGradient_mul` | Polynomial vector product identity, subsequently verified analytically |
| `cylinder_hasFDerivAt`, `cylinder_fderiv` | The computed vector represents the actual Fréchet derivative |
| `cylinder_smooth`, `cylinder_continuous` | Actual smoothness and continuity of the evaluated cylinder |
| `cylinder_product_rule` | Analytic Fréchet derivative product rule for actual cylinders |
| `doubled_holderTriple` | Proved arithmetic (2r)⁻¹+(2r)⁻¹=r⁻¹, not a closure axiom |
| `cylinder_memLp`, `cylinderGradient_memLp` | Actual finite-moment integrability of the scalar function and vector gradient |
| `cylinderGradient_representation_independent` | Ambient gradient equality across a.e.-equal finite representations |
| `cylinderL2`, `cylinderGradientL2` | Actual scalar/vector L² equivalence classes with integrability already proved |
| `cylinderL2_coeFn`, `cylinderGradientL2_coeFn` | Their a.e. representatives are the actual functions above |
| `cylinderGradientL2_representation_independent` | Equal scalar L² cylinders have equal vector L² gradients |
| `normalizedHermitePolynomial` | Actual normalized real Hermite polynomial |
| `normalizedHermitePolynomial_L2` | Its one-dimensional class is the previously verified Hermite basis vector |
| `normalizedHermitePolynomial_integral` | Exact integral orthogonality of those scalar representatives |
| `productGaussian` | Actual independent finite product measure ∏ᵢγ |
| `tensorHermiteFunction` | Actual finite product e_α of normalized Hermite representatives |
| `tensorHermite_partial_memLp`, `tensorHermite_memLp` | Proved finite moments of partial and full tensor products |
| `tensorHermite`, `tensorHermite_coeFn` | Actual product Gaussian L² vectors and their a.e. representatives |
| `tensorHermite_inner`, `tensorHermite_orthonormal` | Exact tensor inner products and orthonormality; no completeness assertion |

### Remaining analytic obligations and adjoint investigation

The next formalization task is tensor completeness and finite-dimensional
polynomial density. A valid route is to lift the existing one-dimensional
complete Hermite basis using a proved product/iterated-L² identification and
Fubini, or to prove that a vector orthogonal to all tensor products is zero.
The inspected Mathlib tensor basis API concerns finite algebraic tensor
products and finite-dimensional orthonormal bases; it does not by itself give
this Hilbert completion/density theorem for infinite-dimensional Gaussian L².
The missing result is an implementation/proof obligation for a true theorem,
not a mathematical failure of polynomial density. A fixed family spanning a
proper subspace cannot be assumed dense in the whole ambient L² space.

After density, multivariate IBP still needs a proof by integrable slices and
finite-product Fubini, starting from the verified one-dimensional polynomial
IBP. The intended ambient identity is

    E[⟨∇F,k⟩ G] = E[F (W(k)G-⟨∇G,k⟩)].

It does not require a Gram-matrix inverse. It is not currently a Lean theorem
in these modules. Vector-valued test-core density and this identity should
then prove closability of the actual finite-dimensional gradient. No
closability, dense operator domain, or full divergence adjoint is assumed now.

For future independent Hermite coordinates, the expected closed gradient
domain condition is Σ_α |α| |c_α|²<∞. The divergence output coefficients
should be Σᵢ √(αᵢ) u_{i,α-eᵢ}, with absent/negative indices contributing zero.
Its maximal adjoint domain must control the square-summability of that SUM;
requiring each separate weighted coordinate derivative to be square summable
can be stronger because terms can cancel. These are mathematical targets
only, not verified declarations or asserted domain identities. The existing
one-dimensional domains cannot simply be intersected to obtain the strongest
vector-divergence domain without a new spectral proof.

The original cylindrical interfaces (`OperatorDerivative.lean:340–360` and
the manuscript's cylindrical-reduction discussion) remain untouched. The
actual polynomial derivative and representation-independent L² value now
supply concrete ingredients for repair, but their asserted IBP and closed
operator identifications still require the finite-dimensional analytic steps
above. General bounded smooth cylinders, consistency across growing ambient
spaces, and infinite-dimensional limits remain future work.

Verification for this milestone comprises `lake build`,
`lake build Foundation.AxiomAudit`, and a fresh
`lake env lean Foundation/AxiomAudit.lean`. There are 50 new explicit axiom
queries, for 258 audited declarations in total. The fresh audit reports only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom
axioms. The original Lean/manuscript hashes and all previous foundation source
files are checked unchanged before committing. Only pre-existing warnings in
`Foundation.Adjoint` remain; the new modules have no compiler/linter warnings
and no suppressed linters.

## Finite Gaussian polynomial density and tensor completeness (after 0347f06)

This milestone proves scalar L² completeness, not graph-norm density or a
multivariate adjoint identity. The original Lean and manuscript are unchanged.
The original `UnboundedCylindricalStructure.cyl_dense` at
`OperatorDerivative.lean:347–350` describes graph convergence in a comment but
its field supplies only a sequence of cylindrical functions, with no convergence
condition. The manuscript's cylindrical reduction and closure discussion
(e.g. lines 52, 84 and 165) also needs genuinely proved density and IBP results.
The new theorems below supply the scalar L² density prerequisite; they do not
validate that original graph-density claim.

### Precise setting and noncircular proof

For any finite index type I, μ = ∏ᵢ γ on I → ℝ, with γ = N(0,1). All results
hold for I = Fin n, for every n, with no positivity-of-dimension hypothesis.
The underlying Pi space uses its ordinary finite-product Borel structure;
no correlated-coordinate law is substituted for this independent product.

`Foundation/FiniteGaussianDensity.lean` proves polynomial density without
assuming tensor completeness. If f ∈ L²(μ) is orthogonal to all polynomials,
its positive and negative parts define finite positive measures ν₊ and ν₋.
For every continuous real linear functional L and t ∈ ℝ,
exp(t L(x)) ∈ L²(μ): decompose L into finitely many coordinate functionals,
factor the exponential, and apply the proved one-dimensional exponential
moments and Hölder with doubled exponents. Cauchy–Schwarz then proves all
exponential moments of the pushforwards L_*ν₊ and L_*ν₋. Orthogonality to (L(x))ⁿ gives equal
moments of these projected measures. The previously verified
`GaussianCore.finite_measure_eq_of_moments` makes every pair of projections
equal; Mathlib's `Measure.ext_of_charFunDual` makes ν₊ = ν₋. Uniqueness of
nonnegative densities gives f = 0. Orthogonal-complement theory yields
polynomial density. This also works in dimension zero, where the zeroth
moment fixes the total mass.

`Foundation/FiniteGaussianCompleteness.lean` uses the existing one-dimensional
Hermite polynomial sequence basis, rescaled by 1/√(n!), to expand every
separable polynomial into a finite Hermite tensor sum. Mathlib's
`MultilinearMap.map_sum_finset` performs the finite distributive expansion.
Every multivariate monomial is a scalar multiple of a separable polynomial,
so normalized tensor polynomials span the entire multivariate polynomial
space. Their Gaussian L² classes span exactly the algebraic polynomial core.
Independent polynomial density and the previously verified tensor
orthonormality then construct an actual `HilbertBasis (I → ℕ)`.

The existing one-dimensional complete Hermite basis is preserved and its
agreement with the one-coordinate tensor basis is explicitly verified by
`tensorHermite_unique_coordinate`. The proof of higher-dimensional density
uses the verified one-dimensional moment-uniqueness infrastructure rather
than an unproved Hilbert tensor-completion identification. The inspected
Mathlib algebraic tensor/finite-dimensional orthonormal-basis APIs alone do
not supply that analytic identification. This is an alternative proof of the
requested full completeness theorem, not a conditional or weaker replacement.

### Meanings of all new public declarations

All names below are in `OperatorDerivativeRewrite.Foundation.FiniteGaussian`.
Private helpers establish arbitrary finite exponential moments of γ, finite
products of these exponentials, nonnegative weighted-measure integrability,
integral transfer, finiteness, and the rescaled one-dimensional polynomial
basis. None are postulates.

| Declaration | Verified mathematical meaning |
| --- | --- |
| `productPolynomial_memLp` | Every multivariate polynomial has every finite moment under μ |
| `productPolynomialL2` | The actual L² class of polynomial evaluation, with proved integrability |
| `productPolynomialL2_coeFn` | Its representative equals polynomial evaluation μ-a.e. |
| `productPolynomialEmbedding` | Linear evaluation into L²; its range is the algebraic polynomial core |
| `productGaussian_exp_linear_memLp` | exp(t L(x)) belongs to L²(μ) for every real continuous linear functional L and t |
| `eq_zero_of_productPolynomial_orthogonal` | A vector orthogonal to every polynomial is zero, by the weighted-measure argument |
| `productPolynomialEmbedding_dense` | The algebraic multivariate polynomial core is dense in L²(μ) |
| `tensorPolynomialMap` | The genuine multilinear map (pᵢ) ↦ ∏ᵢ pᵢ(Xᵢ) |
| `tensorHermitePolynomial` | ∏ᵢ H_{αᵢ}(Xᵢ)/√(αᵢ!), an actual multivariate polynomial |
| `tensorPolynomialMap_mem_span` | Every separable polynomial is in the algebraic span of these tensors |
| `tensorHermitePolynomial_span` | Their algebraic polynomial span is the whole multivariate polynomial space |
| `tensorHermitePolynomial_eval` | Evaluation gives the already verified tensor representative e_α(x) |
| `tensorHermitePolynomial_L2` | Its polynomial L² class is exactly the existing tensor vector |
| `tensorHermite_span` | The algebraic tensor-vector span equals the polynomial embedding range |
| `tensorHermite_dense_span` | That span is dense in the full product Gaussian L² space |
| `tensorHermiteBasis` | Complete orthonormal Hilbert basis indexed by I → ℕ |
| `tensorHermiteBasis_apply` | Its basis vector at α is the previously defined tensorHermite α |
| `tensorHermiteBasis_hasSum` | Every f equals the unconditionally convergent sum Σ_α ⟨e_α,f⟩e_α |
| `tensorHermiteFunction_empty` | In dimension zero the sole tensor representative is the constant 1 |
| `tensorHermite_empty_expansion` | Every zero-dimensional L² vector is its vacuum coefficient times the vacuum vector |
| `tensorHermite_unique_coordinate` | For a singleton coordinate index, the tensor vector is the measure-preserving pullback of the existing one-dimensional Hermite Hilbert-basis vector |
| `orthonormal_coordinates_measurePreserving` | Coordinates in an orthonormal basis of the ambient finite Hilbert space preserve its standard Gaussian measure to μ |
| `productPolynomialL2_pullback` | Pullback of polynomial L² evaluation is exactly the existing cylinderL2 b p |
| `tensorHermite_pullback` | Pullback of each tensor vector is the genuine cylinder of its tensorHermitePolynomial |

### Independent, correlated, and degenerate families

The basis and density theorems above concern the independent standard
coordinate space. Compatibility with ambient standard Gaussian cylinders is
proved through orthonormal-basis coordinates. The earlier representation
independence theorems for arbitrary correlated/dependent families remain
unchanged. Their joint law has Gram covariance and may lie on a proper linear
subspace. No tensor orthogonality for such a family, density of its functions
in the entire ambient L² space, or invertible Gram matrix is asserted here.
Density with respect to a degenerate family's own image law and a transported
complete ambient Hilbert basis can be treated separately if needed.

### Remaining analytic prerequisites and downstream consequences

There is no unresolved obstruction to scalar polynomial density or tensor
completeness in this milestone. Their proofs are completed.

* Multivariate polynomial Gaussian IBP still needs integrable slices and
  finite-product Fubini using the verified one-dimensional IBP. The intended
  formula is E[⟨∇F,k⟩G] = E[F(W(k)G−⟨∇G,k⟩)]. Scalar/vector polynomial moments
  are already proved; this integral identity has not yet been formalized.
* Gradient closability needs this IBP identity plus density of an actual
  vector-valued polynomial test core. Scalar L² density alone is not a proof
  of either statement. The actual gradient is already representation
  independent, so no independently prescribed derivative data are needed.
* Divergence adjoints require a genuine densely defined vector-to-scalar
  operator, the adjoint pairing, and new graph-domain/spectral arguments.
  Neither graph-norm density nor full adjoint identification follows merely
  from this scalar Hilbert basis.
* The expected gradient weight Σ_α |α| |c_α|² and divergence coefficient
  Σᵢ√(αᵢ)u_{i,α−eᵢ} remain targets. The divergence domain must control the
  square-summability of the sum, allowing cancellation between coordinates.
* The original scalar cylindrical-density premise can now be replaced by an
  actual theorem on the standard finite product. Original D^{1,4} graph-core
  claims, closed Leibniz extensions, smooth nonpolynomial cylinders, Itô
  formulas, and infinite-dimensional limits still need new analytic proofs.

Verification: full `lake build`, `lake build Foundation.AxiomAudit`, and a fresh
`lake env lean Foundation/AxiomAudit.lean`. The 24 new public declarations are
explicitly queried, bringing the audit to 282 declarations. Dependencies are
only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom
axioms. Prior foundation proofs and original Lean/manuscript hashes are
checked unchanged. Only the two pre-existing unused-section-variable warnings
in `Foundation.Adjoint` remain; no new warnings or suppressed linters.

## Finite Gaussian gradient/divergence: dense closable polynomial operators (after 9fc7fbb)

This is a complete operator-core milestone: polynomial Gaussian IBP, genuine
scalar-to-vector gradient and vector-to-scalar divergence, both dense domains,
proved closability, closed extensions and adjoint inclusions, and actual tensor
Hermite lowering/raising. Full maximal-adjoint identification and spectral
domain characterizations are **not** claimed in this milestone.

The original `UnboundedCylindricalStructure` (`OperatorDerivative.lean:341–374`)
requires a cylindrical IBP formula and an extension from a purported graph core.
Its earlier `cyl_dense` field does not actually express convergence. The
manuscript's cylindrical reduction and Sobolev closure discussion likewise
needs analytic proofs. The new finite independent Gaussian model now supplies
a genuine polynomial IBP identity and closable operators. It does not establish
the original D^{1,4} graph-density or closed Leibniz extension claims. Original
sources and every previously verified foundation module remain unchanged.

### Spaces, domains, definitions, and sign convention

For every finite index type I, including the empty type, let μ = ∏ᵢ N(0,1) on
I → ℝ. The scalar Hilbert space is Hₛ = L²(μ;ℝ). The vector Hilbert space is
Hᵥ = L²(μ;EuclideanSpace ℝ I), with the Euclidean ℓ² fiber norm and inner
product, not the supremum norm on a plain Pi space.

Scalar and vector polynomial embeddings evaluate actual multivariate
polynomials, with all finite moments proved. Both embeddings are injective:
full support of μ converts equality a.e. of continuous polynomials into
equality everywhere, and polynomial extensionality gives equality of the
polynomials. Vector injectivity follows from the scalar coordinate maps.

The operator graphs are ranges of linear maps from actual polynomials:

    ∇₀[p] = [x ↦ (∂ᵢp(x))ᵢ],       dom(∇₀) = scalar polynomial embedding range;
    δ₀[u] = [Σᵢ(Xᵢuᵢ − ∂ᵢuᵢ)],  dom(δ₀) = vector polynomial embedding range.

Vertical uniqueness is proved from the injectivity of the input embeddings.
No derivative/output data are independently prescribed. The polynomial
vector used for ∇₀ is additionally verified to be the actual Fréchet gradient
on the Euclidean coordinate model. In particular δ₀ has the positive
Gaussian-adjoint sign convention, rather than the ordinary positive divergence.

The scalar polynomial domain is dense by the existing proved finite Gaussian
density theorem. Vector polynomial density is now proved separately:
orthogonality to fields with one polynomial component forces each scalar L²
component to vanish; the vector therefore vanishes a.e. Orthogonal-complement
theory gives density. There is no vector-density hypothesis and no assumption
about graph-norm density.

### Integration by parts, closability, and exact inclusions

`Foundation/FiniteGaussianIBP.lean` first proves the actual coordinate identity

    ∫ xᵢ p(x) dμ = ∫ ∂ᵢp(x) dμ.

Partial differentiation of a separable polynomial product differentiates
precisely its i-th factor. Finite-product Fubini and the previously verified
one-dimensional Stein identity prove the identity for every separable product.
Linearity and the already proved algebraic tensor Hermite spanning extend it
to every multivariate polynomial. Applying it to pq, with genuine product
integrability, gives

    ∫ (∂ᵢp)q dμ = ∫ p(Xᵢq−∂ᵢq) dμ.

Coordinate summation yields, for every scalar polynomial p and polynomial
vector field u,

    ⟨∇₀[p],[u]⟩_{Hᵥ} = ⟨[p],δ₀[u]⟩_{Hₛ}.

Both dense-domain hypotheses are proved independently. Mathlib's formal
adjoint theorem gives actual operator inclusions, including domains and values:

    ∇₀ ⊆ δ₀*,    δ₀ ⊆ ∇₀*.

The adjoints of these densely defined operators are closed. Their closed
extensions therefore prove closability of both polynomial operators. Their
actual graph closures, denoted `closedGradient` and `closedVectorDivergence`,
are closed, densely defined operators satisfying

    closure(∇₀) ⊆ δ₀*,    closure(δ₀) ⊆ ∇₀*.

Classical polynomial values are preserved on both closed graphs and for every
proof of polynomial domain membership. Polynomial domains are graph cores
for their own closures, by the definition and verified properties of graph
closure. This statement does NOT make them graph cores for the maximal
adjoints on the right. No equality between a closure and the opposite adjoint
has been inferred from scalar or vector L² density.

### Tensor actions and the outstanding spectral argument

`Foundation/FiniteGaussianLadders.lean` reuses the actual one-dimensional
polynomial operator graph actions to prove normalized polynomial lowering
and raising. These determine actual multivariate polynomial identities. For
e_α = ∏ᵢ H_{αᵢ}/√(αᵢ!) and eᵢ the coordinate unit multi-index:

    ∂ᵢe_α = √(αᵢ)e_{α−eᵢ} when αᵢ>0; ∂ᵢe_α = 0 when αᵢ=0;
    (Xᵢ−∂ᵢ)e_α = √(αᵢ+1)e_{α+eᵢ}.

These are proved for actual normalized polynomial representatives and their
operator L² graphs, not stipulated coefficient transformations. A vector
Hermite field with its sole nonzero component i equal to e_α belongs to δ₀'s
domain, and its output is exactly √(αᵢ+1)e_{α+eᵢ}. The corresponding tensor
scalar belongs to ∇₀'s domain, and each positive-degree gradient component
has the exact lowering weight above.

**Remaining unproved targets, not declaration meanings:** for scalar Hermite
coefficients c_α and vector-component coefficients u_{i,β}, the expected
closed-gradient criterion is

    Σ_α |α| |c_α|² < ∞,

and the expected maximal divergence criterion is square-summability of the
scalar sequence

    d_α = Σ_{i:αᵢ>0} √(αᵢ) u_{i,α−eᵢ}.

The divergence criterion controls the SQUARE OF THE SUM, allowing cancellation
between coordinates. Requiring each coordinate raising operator separately
to have finite weighted norm is generally stronger and is not used here. The
one-dimensional fact that derivative and divergence have the same domain
does not identify these different scalar/vector multivariate domains.

The next proof obligations are precise:

1. Derive and prove sufficient as well as necessary Hermite coefficient
   relations for both maximal adjoint graphs, using the complete scalar basis
   and a proved componentwise vector expansion/Parseval identity.
2. Prove square-summable coefficient realization in the required vector space,
   and the weighted norm formulas that characterize the scalar gradient.
3. Use **finite total-degree cutoffs** {|α|≤N}. Lowering changes total degree
   by −1; raising changes it by +1 for every coordinate. Thus the appropriate
   shifted output cutoff can retain all contributions to each divergence
   coefficient, including cancellations. Finiteness and both graph-limit
   convergence statements must be proved in Lean; they are not assumed.
4. Establish that these approximations are graph dense in δ₀* and ∇₀*, then
   deduce closure(∇₀)=δ₀* and closure(δ₀)=∇₀*. Until then only the displayed
   inclusions are established. Rectangular coordinate cutoffs must not be
   substituted without checking that boundary cancellations are preserved.

This is missing formalized spectral/approximation infrastructure, not a
counterexample to the finite Gaussian operator identifications. No infinite-
dimensional limit, Itô formula, or full Malliavin operator is claimed.

### Compatibility and correlated-coordinate limits

`gradientPolynomial_hasFDerivAt` proves that the computed Euclidean-valued
polynomial gradient represents the actual Fréchet derivative. It specializes
the existing genuine cylindrical derivative at the standard orthonormal basis.
All earlier arbitrary-family results remain preserved: for hᵢ in a finite real
Hilbert space, including linearly dependent vectors, the actual derivative is
Σᵢ ∂ᵢp(W(h))hᵢ and is independent of its polynomial cylinder representation.
These are geometric chain-rule statements and do not assert tensor
orthogonality for correlated coordinates.

The new Hilbert operators live on the independent product model. An
orthonormal change of ambient coordinates has the already proved
measure-preserving scalar polynomial pullback. Transporting the **closed**
vector operators and identifying their domains on an arbitrary ambient Hilbert
space requires a further vector L² transport theorem. A correlated or
rank-deficient family is not a measure-preserving identification with the full
independent product space; no such claim is made or used.

### Public declaration meanings and verification

All new names are in `OperatorDerivativeRewrite.Foundation.FiniteGaussian`.
The named `DecidableEq I` parameters on coordinate-update theorems are solely
computational decidability for finite-index updates, not analytic assumptions.

| Declarations | Mathematical meaning |
| --- | --- |
| `productPolynomialIntegral` | Integration as a linear functional on genuinely integrable polynomials |
| `polynomial_coordinate_eval`, `pderiv_coordinate_polynomial` | Genuine evaluation/substitution and coordinate polynomial differentiation |
| `tensorPolynomialMap_eval`, `tensorPolynomialMap_pderiv` | Product evaluation and differentiation of precisely one tensor factor |
| `productPolynomial_stein` | Multivariate coordinate Gaussian Stein identity |
| `coordinateDivergencePolynomial` | The actual expression Xᵢq−∂ᵢq |
| `productPolynomial_integration_by_parts` | Genuine integrable polynomial coordinate IBP |
| `ScalarGaussianL2`, `VectorGaussianL2` | The scalar and Euclidean-valued Gaussian L² Hilbert spaces |
| `productGaussian_openPos` | Proved full support of the independent product |
| `productPolynomialEmbedding_injective` | Uniqueness of actual scalar polynomial evaluation in L² |
| `vectorPolynomialFunction`, `vectorPolynomial_memLp` | Genuine Euclidean-valued polynomial functions with all finite moments |
| `vectorPolynomialL2`, `vectorPolynomialL2_coeFn` | Their actual L² classes and a.e. representatives |
| `vectorPolynomialEmbedding`, `vectorPolynomialEmbedding_injective` | Linear injective evaluation of actual polynomial fields |
| `vectorL2Component`, `vectorL2Component_coeFn`, `vectorPolynomialL2_component` | Genuine scalar L² coordinate projection and its polynomial compatibility |
| `vectorPolynomialL2_inner` | Proved decomposition of the vector Hilbert pairing into integrable component pairings |
| `eq_zero_of_vectorPolynomial_orthogonal`, `vectorPolynomialEmbedding_dense` | Independent proof of full vector polynomial L² density |
| `gradientPolynomial`, `divergencePolynomial` | Actual partial-derivative family and Σᵢ(Xᵢuᵢ−∂ᵢuᵢ) |
| `gradientPolynomialL2` | The actual Euclidean-valued polynomial gradient L² class |
| `productPolynomialL2_inner`, `gradient_divergence_polynomial_pairing` | Genuine scalar Hilbert pairing and full scalar/vector IBP |
| `polynomialGradientGraph`, `polynomialDivergenceGraph` | Linear ranges of genuine input/output polynomial evaluations |
| `polynomialGradientGraph_vertical_zero`, `polynomialDivergenceGraph_vertical_zero` | Proven single-valuedness of these graphs |
| `polynomialGradient`, `polynomialDivergence` | Genuine partial linear operators with exactly the polynomial domains |
| `polynomialGradient_graph`, `polynomialDivergence_graph` | Their graphs equal the proved single-valued polynomial graphs |
| `polynomialGradient_polynomial_graph`, `polynomialDivergence_polynomial_graph` | Actual polynomial input/output domain membership and values |
| `polynomialGradient_domain`, `polynomialDivergence_domain` | Exact algebraic scalar/vector polynomial domains |
| `polynomialGradient_dense_domain`, `polynomialDivergence_dense_domain` | Both domains are proved dense in their respective Hilbert spaces |
| `polynomialGradient_formalAdjoint` | IBP on the actual two operator domains |
| `polynomialGradient_le_divergence_adjoint`, `polynomialDivergence_le_gradient_adjoint` | ∇₀⊆δ₀* and δ₀⊆∇₀*, with domains and values |
| `polynomialGradient_isClosable`, `polynomialDivergence_isClosable` | Genuine closability from closed adjoint extensions |
| `closedGradient`, `closedVectorDivergence` | Actual graph closures of the polynomial operators |
| `closedGradient_isClosed`, `closedVectorDivergence_isClosed` | Proved closedness of those extensions |
| `closedGradient_dense_domain`, `closedVectorDivergence_dense_domain` | Their domains remain dense |
| `closedGradient_le_divergence_adjoint`, `closedVectorDivergence_le_gradient_adjoint` | The strongest closed-operator inclusions established here |
| `closedGradient_polynomial_graph`, `closedVectorDivergence_polynomial_graph` | Closed graphs preserve the classical polynomial values |
| `closedGradient_has_polynomial_core`, `closedVectorDivergence_has_polynomial_core` | Polynomial graph cores for their own closures, not for unproved maximal adjoint identifications |
| `gradientPolynomial_hasFDerivAt` | The computed gradient is the actual Euclidean Fréchet derivative |
| `closedGradient_polynomial_apply`, `closedVectorDivergence_polynomial_apply` | Actual polynomial values for every proof of closed-domain membership |
| `normalizedHermitePolynomial_derivative`, `normalizedHermitePolynomial_divergence` | Actual normalized one-dimensional polynomial ladder identities recovered from the verified operators |
| `tensorHermitePolynomial_lowering`, `tensorHermitePolynomial_lowering_zero` | Actual positive-degree lowering and zero-degree vanishing |
| `tensorPolynomialMap_coordinateDivergence`, `tensorHermitePolynomial_raising` | True separable-factor divergence and normalized tensor raising |
| `tensorHermiteVector`, `tensorHermiteVector_divergence_graph` | Actual one-component vector tensor field and its δ₀ graph action |
| `tensorHermite_gradient_graph`, `tensorHermite_gradient_component` | Actual ∇₀ tensor graph membership and normalized component lowering |

Verification consists of the full Lake build, the AxiomAudit target build,
and a fresh `lake env lean Foundation/AxiomAudit.lean`. All 73 new public
statements/definitions/instances are explicitly queried, for 355 audited
declarations in total. Only `propext`, `Classical.choice`, and `Quot.sound`
appear: no `sorryAx`, `admit`, or custom axioms. All prior foundation sources
and original Lean/manuscript hashes are checked unchanged. Only the two
pre-existing `Foundation.Adjoint` warnings remain; no new warnings or
suppressed linters.

## Finite Gaussian spectral domains and full adjoint identification (after a077fd6)

This milestone completes the finite independent Gaussian operator identification.
The earlier section describes the results at a077fd6; its outstanding spectral
and graph-core obligations are discharged here. The four new modules are
`FiniteGaussianSpectral`, `FiniteGaussianTruncation`, `FiniteGaussianAdjoints`,
and `FiniteGaussianDomains`. Original sources and all existing proof modules
remain unchanged. The root import and explicit axiom audit include the new work.

### Exact operator statements

For every finite index type I, set μ = ∏ᵢ N(0,1), Hₛ = L²(μ;ℝ), and
Hᵥ = L²(μ;EuclideanSpace ℝ I). These are the existing actual L² spaces and
polynomial operators, with the previously proved Gaussian integration by parts.
Write eα for the complete normalized tensor Hermite basis, and define

    cα(f) = ⟨eα,f⟩,
    uᵢ,α = ⟨eα, componentᵢ(u)⟩,
    aᵢ,α(f) = √(αᵢ+1) cα+eᵢ(f),
    bβ(u) = Σᵢ:βᵢ>0 √βᵢ uᵢ,β−eᵢ,
    |α| = Σᵢ αᵢ.

`Function.update` raises or lowers the indicated coordinate and retains every
other coordinate. All coefficients come from the actual L² input, not from
independently supplied derivative data. `DecidableEq I`, when present in a
coordinate-update statement, is an implementation requirement for finite index
operations, not a regularity or graph-density assumption. Statements whose
types do not need it omit it and use local classical decidability in proofs.

The verified exact closed graph and domain statements are:

- `closedGradient_graph_iff`: (f,g) belongs to closure(∇₀)'s graph iff
  uᵢ,α(g) = aᵢ,α(f) for every i and α.
- `closedGradient_domain_iff`: f belongs to closure(∇₀)'s domain iff
  Σα |α| |cα(f)|² is summable (equivalently finite, since terms are nonnegative).
- `closedVectorDivergence_graph_iff`: (u,g) belongs to closure(δ₀)'s graph iff
  cβ(g) = bβ(u) for every β.
- `closedVectorDivergence_domain_iff`: u belongs to closure(δ₀)'s domain iff
  Σβ |bβ(u)|² is summable. No individual component derivative domain is required.
- `closedVectorDivergence_norm_sq`: its output satisfies
  ‖g‖² = Σβ |bβ(u)|².
- `closedGradient_eq_divergence_adjoint`: closure(∇₀) = δ₀*.
- `closedVectorDivergence_eq_gradient_adjoint`: closure(δ₀) = ∇₀*.
- The two closed operators are also mutual adjoints, via the proved invariance
  of adjoints under closure of a densely defined closable operator.

The vector divergence condition combines coordinates **before squaring**.
Replacing it by Σᵢ,α (αᵢ+1)|uᵢ,α|² < ∞ would discard legitimate cancellations.
The proofs never use that stronger condition. Square summability of b is proved
sufficient by scalar coefficient realization and the whole polynomial adjoint
identity, then by actual polynomial graph approximation. It is not assumed as
proof of any componentwise integrability or domain membership.

### Noncircular realization and proof dependencies

1. The previously verified one-dimensional Hermite completeness and noncircular
   multivariate polynomial density supply `tensorHermiteBasis` and algebraic
   `tensorHermitePolynomial_span`.
2. Parseval follows from Mathlib's ℓ² norm theorem applied to that Hilbert basis.
   Its inverse representation realizes every square-summable real coefficient
   family as an actual scalar Gaussian L² class.
3. `tensorHermite_gradient_pairing` uses the already verified genuine partial
   derivatives and lowering identities to compute bβ for any vector L² input.
   Testing the adjoint equation on these polynomial tensors proves necessity.
4. Sufficiency for ∇₀* is proved by a linear pairing functional on actual
   multivariate polynomials. Its kernel contains every Hermite tensor polynomial;
   algebraic spanning proves the adjoint equation on the entire polynomial
   gradient domain. This does not assume maximal-domain membership or graph density.
5. Continuous coordinate insertions reconstruct every vector L² class from its
   actual scalar components. They also realize square-summable component
   coefficient families as genuine vector L² classes.
6. Raising a coordinate is an injective map onto the positive-coordinate modes.
   The coordinate weighted series vanishes on the complement of that image.
   Mathlib's injective summability reindexing proves the exact coordinate weight,
   and a finite sum of nonnegative coordinate weights gives |α|. This proves
   both directions of the scalar weighted-domain statement, with output graph
   membership established by the true polynomial approximants.

### Actual total-degree graph approximants

`hermiteDegreeCutoff N` is the finite set {|α| ≤ N}. It is constructed inside a
finite coordinate box and filtered by total degree. Its exact membership theorem
and cofinality in the finite-subset filter are proved, not assumed. Scalar
truncation P_N f is Σ|α|≤N cα(f)eα; vector truncation P_N u applies this same
projection in every component. Both are explicitly evaluated polynomial classes
and converge in their respective actual L² spaces by completeness and continuous
coordinate insertion.

The verified graph approximants are:

    (P_(N+1) f, P_N g) ∈ graph(∇₀)  for every (f,g) ∈ graph(δ₀*),
    (P_N u, P_(N+1) g) ∈ graph(δ₀)  for every (u,g) ∈ graph(∇₀*).

For divergence output index β, every nonzero summand uses input degree |β|−1.
Consequently all coordinates contributing to bβ survive the cutoff together:

    bβ(P_N u) = 1_{|β|≤N+1} bβ(u).

This is the proved `divergenceCoefficient_truncation`, and it is the exact lemma
that protects cancellation. The complementary lowering projection identity is
proved for gradient coefficients. The graph membership of each approximation
comes from the original polynomial operator; equality of its output with the
projected adjoint output is established by coefficient completeness.

Both approximation pairs converge in the product L² topology. Additionally,
`gradient_adjoint_truncation_graphNorm_tendsto` and
`divergence_adjoint_truncation_graphNorm_tendsto` prove explicitly that the
squared Hilbert graph error, ‖input error‖² + ‖output error‖², tends to zero.
Actual graph closure then yields each reverse adjoint inclusion. The two
identifications have separate approximation proofs; neither is inferred merely
from the formal adjoint inclusion or L² polynomial density. Polynomial graph
cores for the full maximal adjoints follow only after these equalities.

### Zero dimension, classical values, and cylindrical compatibility

For an empty index type, |α|=0 and the cutoff is the sole vacuum index for every N.
Scalar and vector projections are the identity. The closed gradient domain is
all Hₛ and its value is the unique zero vector. The closed divergence domain is
all Hᵥ and its value is zero in Hₛ. These are explicit Lean theorems, not an
implicit restriction to positive dimensions. All domain and graph theorems also
work for arbitrary finite dimension, in particular `Fin n` for every n.

The definitions of ∇₀, δ₀, and their closures have not changed. Existing
`closedGradient_polynomial_apply` and `closedVectorDivergence_polynomial_apply`
therefore retain the actual classical values ∂ᵢp and Σᵢ(Xᵢuᵢ−∂ᵢuᵢ). Their
previous axiom queries are rerun together with the new identifications.
`gradientPolynomial_hasFDerivAt` still identifies the gradient as the actual
Fréchet gradient on the Euclidean coordinate model. Earlier orthonormal-coordinate
pullback compatibility and correlated-cylinder representation independence,
product rules, and integrability proofs are preserved unchanged.

Tensor orthogonality and these coefficient formulas apply to the independent
standard-coordinate model. They do not assert tensor orthogonality for an
arbitrary correlated or linearly dependent coordinate family. Transport of full
closed scalar/vector operators to an arbitrary finite Hilbert Gaussian model,
and an explicit transformation of maximal domains for redundant correlated
representations, remain separate obligations. No infinite-dimensional limit,
infinite-dimensional cylindrical graph density, smooth nonpolynomial core,
D^{1,4} multiplier graph density, closed Leibniz extension, or Itô formula is
claimed here. There is no remaining analytic gap in the stated finite independent
Gaussian adjoint identifications or spectral domain criteria.

### Declaration meanings

All 80 new public definitions and theorems are explicitly queried by the axiom
audit. Each is covered below; supporting statements are recorded to make the
proof scope reviewable.

| Declarations | Precise meaning |
| --- | --- |
| `scalarHermiteCoefficient`, `vectorHermiteCoefficient` | Actual scalar tensor coefficients and component coefficients of a vector L² class |
| `gradientCoefficient`, `divergenceCoefficient` | Actual spectral lowering formula and combined raising formula |
| `scalarHermiteCoefficient_hasSum_sq` | Parseval with the scalar L² norm |
| `exists_scalarHermite_coefficients`, `scalarHermiteCoefficient_ext` | Genuine scalar coefficient realization and uniqueness |
| `tensorHermite_gradient_component_zero`, `tensorHermite_gradient_pairing` | Genuine zero-mode vanishing and gradient pairing with an arbitrary L² field |
| `gradient_adjoint_coefficients`, `gradient_adjoint_graph_of_coefficients`, `gradient_adjoint_graph_iff` | Necessary and sufficient combined coefficients for the full graph of ∇₀* |
| `gradient_adjoint_domain_iff`, `gradient_adjoint_norm_sq` | Exact maximal divergence domain and output norm |
| `closedGradient_adjoint_eq`, `closedVectorDivergence_adjoint_eq` | Adjoints of the closures equal the corresponding polynomial adjoints |
| `closedVectorDivergence_coefficients`, `polynomialDivergence_coefficients` | Combined coefficients for the existing closed and classical polynomial divergence values |
| `divergenceCoefficient_empty`, `gradient_adjoint_domain_empty`, `gradient_adjoint_graph_empty` | Zero coefficients and full zero-valued maximal divergence in dimension zero |
| `hermiteDegree`, `hermiteDegreeCutoff` | Total multi-index degree and its actual finite cutoff |
| `mem_hermiteDegreeCutoff`, `hermiteDegreeCutoff_tendsto` | Exact cutoff membership and exhaustion of the finite-subset filter |
| `scalarHermiteTruncationPolynomial`, `scalarHermiteTruncation` | Genuine polynomial representative and its scalar Hermite projection |
| `scalarHermiteTruncationPolynomial_L2`, `scalarHermiteTruncation_coefficient`, `scalarHermiteTruncation_tendsto` | Actual polynomial membership, exact cutoff coefficients, and unconditional L² convergence |
| `vectorL2Insert`, `vectorL2Insert_polynomial`, `vectorL2_reassemble` | Continuous coordinate insertion, genuine polynomial compatibility, and exact reconstruction of any vector L² class |
| `vectorHermiteTruncationPolynomial`, `vectorHermiteTruncation` | Genuine polynomial vector representative and its common total-degree projection |
| `vectorHermiteTruncation_component`, `vectorHermiteTruncation_coefficient`, `vectorHermiteTruncation_tendsto` | Exact component projections and coefficients, with vector L² convergence |
| `hermiteDegree_lower`, `hermiteDegree_raise` | Coordinate lowering/raising changes total degree by exactly one |
| `divergenceCoefficient_truncation`, `gradientCoefficient_truncation` | Exact shifted spectral projections; divergence cancellations are retained |
| `gradient_adjoint_truncation_graph`, `gradient_adjoint_truncation_tendsto` | Genuine polynomial divergence graph approximants of every ∇₀* pair and their convergence |
| `closedVectorDivergence_graph_of_coefficients` | Combined coefficient realization in the actual polynomial divergence graph closure |
| `closedVectorDivergence_eq_gradient_adjoint`, `closedVectorDivergence_domain_iff` | Full divergence adjoint identification and its exact combined square-sum domain |
| `tensorHermiteVector_inner`, `divergence_adjoint_coefficients` | Actual vector tensor coefficient pairing and necessary coefficients of the full δ₀* graph |
| `vectorHermiteCoefficient_ext` | Uniqueness of vector L² classes from their component tensor coefficients |
| `divergence_adjoint_truncation_graph`, `divergence_adjoint_truncation_tendsto` | Genuine polynomial gradient graph approximants of every δ₀* pair and their convergence |
| `closedGradient_graph_of_adjoint`, `closedGradient_eq_divergence_adjoint` | Reverse gradient graph inclusion and full gradient adjoint identification |
| `closedGradient_eq_closedVectorDivergence_adjoint`, `closedVectorDivergence_eq_closedGradient_adjoint` | Mutual adjoint identities for the closed operators |
| `divergence_adjoint_has_polynomial_core`, `gradient_adjoint_has_polynomial_core` | Polynomial graph cores of the actual full maximal adjoints |
| `vectorL2Component_insert`, `exists_vectorHermite_coefficients` | Exact coordinate insertion/projection and genuine vector coefficient realization |
| `gradient_coefficients_truncation_graph`, `closedGradient_graph_of_coefficients`, `closedGradient_graph_iff` | Genuine gradient graph construction from coefficients and exact closed gradient graph |
| `hermiteRaise_injective`, `mem_range_hermiteRaise`, `gradientCoefficient_summable_iff` | Noncircular reindexing of positive-coordinate modes into the exact coordinate weight |
| `hermiteDegree_weight_summable_iff`, `closedGradient_domain_iff` | Finite-sum equivalence of coordinate and total weights, then the exact scalar gradient domain |
| `closedGradient_domain_empty`, `closedGradient_graph_empty` | Full zero-dimensional scalar domain and actual zero gradient |
| `closedVectorDivergence_graph_iff`, `closedVectorDivergence_norm_sq` | Exact closed divergence graph and combined output norm |
| `closedVectorDivergence_graph_empty`, `closedVectorDivergence_domain_empty` | Actual zero divergence and full vector domain in zero dimensions |
| `divergence_adjoint_graph_iff` | Exact coefficient characterization of the full maximal gradient δ₀* |
| `divergence_adjoint_truncation_graphNorm_tendsto`, `gradient_adjoint_truncation_graphNorm_tendsto` | Explicit squared Hilbert graph-error convergence for both total-degree approximation schemes |
| `hermiteDegreeCutoff_empty`, `scalarHermiteTruncation_empty`, `vectorHermiteTruncation_empty` | Sole vacuum cutoff and identity projections in dimension zero |

Verification completed successfully: full `lake build` (3219 jobs),
`lake build Foundation.AxiomAudit` (3218 jobs), and a fresh
`lake env lean Foundation/AxiomAudit.lean`. The fresh output contains exactly
435 declarations (355 existing plus 80 new). Its only axiomatic dependencies
are `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or
custom axiom. The complete raw output is saved at
`.lake/build/finite-gaussian-spectral-axioms.log` (ignored build artifact).
Only the two pre-existing `Foundation.Adjoint` section-variable warnings remain;
all four new modules compile without warnings or suppressed linters.
Every pre-existing proof module except the extended axiom query file is
unchanged from a077fd6. SHA-256 verification confirms both original sources
are unchanged. No theorem statement was weakened and no environment dependency
or toolchain was changed.

## Countable Gaussian probability space and first-chaos L² extension (after 9330547)

This milestone constructs an actual probability space of countably many independent
standard Gaussian coordinates and a genuine L² extension of their finite linear
combinations. It does **not** complete an isonormal Gaussian process: Gaussianity
of every infinite-series limit is still a separate analytic obligation.

The sample space is Ω = ℝ^ℕ with its product measurable space and probability
measure μ = infinitePi (n ↦ gaussianReal 0 1). It is not ℓ² and is not an
identity-covariance Gaussian Radon measure on an infinite-dimensional Hilbert
space. The coefficient Hilbert space ℓ² is distinct from this sample space.
No assertion that sample sequences are square summable is used.

### Exact definitions and verified declarations

All names below are in `OperatorDerivativeRewrite.Foundation.InfiniteGaussian`.
The two source modules introduce only the following declarations:

| Declaration | Precise mathematical meaning |
| --- | --- |
| `SampleSpace` | Real sequences ℕ → ℝ, equipped with the existing product measurable space. |
| `gaussianProduct` | Mathlib's countable product of the verified standard real Gaussian measure. |
| `gaussianProduct_probability` | This product measure has total mass one. |
| `GaussianL2` | The actual real L² space of this probability measure. |
| `coordinate` | Evaluation Xₙ(ω) = ωₙ. |
| `coordinate_measurePreserving` | Xₙ pushes μ forward to the standard real Gaussian measure. |
| `coordinate_law` | Exact equality μ.map Xₙ = gaussianReal 0 1. |
| `coordinate_hasGaussianLaw` | Each actual evaluation variable has Gaussian law. |
| `coordinates_independent` | The entire coordinate family is jointly independent in Mathlib's `iIndepFun` sense. |
| `coordinate_memLp` | Xₙ belongs to every finite Lp, including the exponent-zero convention of Mathlib. |
| `finiteProjection` | Restriction ω ↦ (ωᵢ)ᵢ∈s for any finite set s of natural indices. |
| `finiteProjection_measurePreserving` | Its law is the previously verified finite independent product Gaussian, also when s is empty. |
| `finitePullback` | An actual linear isometry L²(ℝˢ, γˢ) → L²(Ω, μ) by composition with restriction. |
| `finitePullback_coeFn` | Its representative agrees almost everywhere with the composed finite-dimensional representative. |
| `finitePullback_inner` | It preserves every real Hilbert inner product. |
| `polynomialCylinder` | The actual random variable p((ωᵢ)ᵢ∈s), for a genuine multivariate polynomial p. |
| `polynomialCylinder_memLp` | Each such random variable has all finite moments, transported from the verified finite marginal. |
| `polynomialCylinderEmbedding` | Linear embedding of these evaluated polynomials into L²(Ω, μ). |
| `polynomialCylinderEmbedding_coeFn` | The embedded class is represented almost everywhere by the actual polynomial evaluation. |
| `polynomialCylinderEmbedding_injective` | For fixed s, distinct polynomials give distinct L² classes. |
| `finiteHermite_orthonormal` | For each fixed s, the pullback of its complete finite tensor Hermite family remains orthonormal. Completeness in the entire infinite product is not asserted. |
| `coordinateL2` | L² class of the actual evaluation Xₙ, built using its proved integrability. |
| `coordinateL2_coeFn` | This class has the stated actual evaluation representative almost everywhere. |
| `coordinate_integral` | E[Xₙ] = 0. |
| `coordinate_product_integral` | E[Xₙ Xₘ] = 1 if n = m and 0 otherwise. |
| `coordinateL2_orthonormal` | The coordinate L² classes form an orthonormal family. No completeness in all L² is claimed. |
| `CoefficientSpace` | Mathlib's Hilbert space lp (n ↦ ℝ) 2, namely real ℓ² coefficients. |
| `firstChaosEmbedding` | The linear isometry from ℓ² into L² constructed by the orthogonal Hilbert-sum theorem applied to the proved coordinate orthonormal family. |
| `firstChaos_hasSum` | For every h ∈ ℓ², the finite sums of hₙ Xₙ converge unconditionally in L² to `firstChaosEmbedding h`. |
| `firstChaos_single` | The image of a single coefficient a at index n is exactly a times the actual coordinate class. |
| `firstChaos_inner` | ⟨W h, W k⟩L² = ⟨h, k⟩ℓ². This is stated as an L² inner product; centering of every infinite limit is not silently assumed. |
| `firstChaos_norm` | ‖W h‖L² = ‖h‖ℓ². |
| `firstChaos_finiteSum` | The extension agrees with every finite linear combination of actual coordinate classes. |
| `firstChaos_injective` | Different ℓ² coefficient vectors yield different L² random variables. |

### Proof dependencies and absence of circular assumptions

The measure and marginal proofs reuse `Measure.infinitePi`, its probability
instance, `measurePreserving_eval_infinitePi`, `infinitePi_map_restrict`, and
`iIndepFun_infinitePi`. They do not posit an infinite Gaussian measure axiom.
Polynomial integrability is pulled back from the existing proved finite-dimensional
`productPolynomial_memLp`; faithfulness uses the existing polynomial embedding
injectivity and Mathlib's isometric Lp pullback. Tensor orthogonality is used only
for independent coordinate marginals and only within a fixed finite index set.

The coordinate second moment is derived from the previously verified real
polynomial Stein identity applied to p(x) = x. Off-diagonal products use genuine
coordinate independence and proved L² membership. The resulting orthonormality
is the input to Mathlib's `OrthogonalFamily.linearIsometry`, whose
`hasSum_linearIsometry` proves actual unconditional L² convergence. There is
no assumed convergence, no independently prescribed derivative, and no assumed
infinite-dimensional graph domain or adjoint identification.

Finite projections include s = ∅ without special hypotheses. Earlier correlated
finite-dimensional coordinates and their true polynomial derivatives are
preserved unchanged; this new independent sequence model does not assert tensor
orthogonality for correlated coordinates. Passing from independent sequence
coordinates to correlated ℓ² combinations requires the Gaussian limit result
below before claiming an isonormal family.

### Remaining analytic obligations and next task

The single best next task is to prove, for every h ∈ ℓ², that the actual
representative of `firstChaosEmbedding h` has law N(0, ‖h‖²). A noncircular
route is to prove the exact Gaussian law of finite weighted coordinate sums,
transport their proved L² convergence to convergence in probability/distribution,
and identify the limiting characteristic function while variances tend to
‖h‖². The current unconditional L² convergence theorem is a proved prerequisite,
not a hypothesis substituting for Gaussianity. Centering and joint Gaussianity
of all finite families of these limits must also be established to complete the
isonormal process and correlated-coordinate model.

Additional obligations before infinite-dimensional Malliavin operators are:

- Density of the union of finite-coordinate polynomial spaces in L²(Ω, μ).
  Finite-dimensional polynomial density alone does not establish this; one needs
  density of finite-coordinate measurable cylinders or a proved conditional
  expectation approximation. Pulled-back finite Hermite families overlap as s
  changes, so their union cannot simply be declared an orthonormal basis.
- Compatibility under enlargement and renaming of finite coordinate sets,
  including representation independence of the resulting Hilbert-valued
  polynomial derivative. The fixed-set polynomial injectivity proved here does
  not by itself settle comparisons between different coordinate sets.
- A genuine ℓ²-valued cylindrical gradient with proved L² integrability,
  Gaussian integration by parts, dense domain, and closability.
- The divergence adjoint, graph cores, and any infinite-dimensional spectral
  domain characterization. The finite-dimensional equalities are not imported
  as infinite-dimensional operator equalities.

No infinite-dimensional derivative, divergence, Itô formula, or full isonormal
Gaussian law is claimed in this milestone.

### Verification

The complete `lake build` succeeds (3292 jobs). Both new modules compile without
new warnings; the two existing unused-section-variable warnings in
`Foundation/Adjoint.lean` remain unchanged. A fresh direct Lean run of
`Foundation/AxiomAudit.lean` yields 469 results for 469 explicit queries,
including all 34 new declarations. The only dependencies reported are
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom is
reported. The fresh raw output is in the ignored build artifact
`.lake/build/infinite-gaussian-foundation-axioms.log`.

All earlier proof modules are unchanged. The original `OperatorDerivative.lean`
and `OperatorDerivative.tex` retain their previously recorded SHA-256 hashes.

## Genuine ℓ² isonormal Gaussian process (after aceed38)

The Gaussian law obligation left by the preceding milestone is now proved for
the original `firstChaosEmbedding`, without changing that construction or any
earlier proof module. On Ω = ℝ^ℕ with the countable product standard Gaussian
probability measure μ, the existing linear isometry W : ℓ² → L²(Ω, μ) satisfies

- μ.map W(h) = N(0, ‖h‖²) for every h ∈ ℓ², including h = 0;
- E[W(h)] = 0, E[W(h)W(k)] = Cov(W(h),W(k)) = ⟨h,k⟩;
- every finite family (W(hᵢ)) is jointly Gaussian, even when its Gram matrix is
  singular or coordinates coincide;
- linearity holds exactly as an L² linear map and almost everywhere for each
  fixed finite linear relation between actual representatives.

`firstChaos_isGaussianProcess` verifies Mathlib's Gaussian process predicate for
these actual representatives indexed by all ℓ² vectors. Together with the
proved linear isometry and covariance theorem, this establishes a genuine real
isonormal Gaussian process over ℓ². There is no assumption of Gaussianity of an
L² limit and no assumed joint Gaussianity.

### Exact new definitions and theorems

All names are in `OperatorDerivativeRewrite.Foundation.InfiniteGaussian`.
The complete list of 30 new declarations is:

| Declaration | Precise mathematical content |
| --- | --- |
| `weightedSum` | The actual finite random variable Sₛ(a)(ω) = Σₙ∈s aₙωₙ. |
| `weightedSumL2` | Its L² class, constructed as the finite sum of proved coordinate classes. |
| `weightedSumL2_coeFn` | That L² class is represented almost everywhere by Sₛ(a). |
| `weightedSum_charFun` | Its characteristic function at t is exp(−t² Σₙ∈s aₙ²/2). |
| `weightedSum_law` | Its exact law is N(0, Σₙ∈s aₙ²), also for empty sums and zero coefficients. |
| `weightedSumL2_tendsto` | Initial-segment weighted sums converge to the original W(h) in L². |
| `weightedSumL2_tendstoInMeasure` | These actual L² representatives converge to W(h) in probability. |
| `weightedSumL2_tendstoInDistribution` | They converge to W(h) in distribution under μ. |
| `coefficientSquares_hasSum` | Σₙ hₙ² converges unconditionally to ‖h‖ℓ²². |
| `firstChaos_charFun` | The actual limit law has characteristic function exp(−‖h‖²t²/2). |
| `firstChaos_law` | Equality of the actual pushforward measure with N(0, ‖h‖²), without a nonzero-norm restriction. |
| `firstChaos_hasGaussianLaw` | Gaussianity of the actual representative of W(h). |
| `firstChaos_integral` | E[W(h)] = 0 for every h. |
| `firstChaos_product_integral` | E[W(h)W(k)] = ⟨h,k⟩ℓ². |
| `firstChaos_covariance` | Cov(W(h),W(k)) = ⟨h,k⟩ℓ², for arbitrary h and k. |
| `firstChaos_zero_law` | W(0) has the point-mass law δ₀. |
| `firstChaos_add_ae` | W(h+k) = W(h)+W(k) almost everywhere for each h,k. |
| `firstChaos_smul_ae` | W(ah) = aW(h) almost everywhere for each a,h. |
| `firstChaosFamily` | The actual finite random vector ω ↦ (W(hᵢ)(ω))ᵢ. This definition has no prescribed Gaussianity field. |
| `firstChaos_linearCombination_ae` | W(Σᵢ aᵢhᵢ) = Σᵢ aᵢW(hᵢ) almost everywhere. |
| `firstChaosFamily_linear_ae` | For each continuous real linear form L on the finite coordinate space, L(W(hᵢ)) agrees almost everywhere with W(Σᵢ L(eᵢ)hᵢ). |
| `firstChaosFamily_linear_law` | The exact law of that projection is N(0, ‖Σᵢ L(eᵢ)hᵢ‖²). |
| `firstChaosFamily_hasGaussianLaw` | Joint Gaussianity for every finite index type and arbitrary vectors hᵢ. Uses `Finite`, with an enumeration chosen only inside the proof. |
| `firstChaosFamily_covariance` | The covariance matrix of the finite random vector is its Gram matrix (⟨hᵢ,hⱼ⟩). The individual covariance equality does not require finiteness. |
| `firstChaos_unit` | W(eₙ) is exactly the original coordinate L² class. |
| `firstChaosFamily_unit_law` | Every finite family of unit coefficients has exactly the original finite product Gaussian marginal law, including the empty family. |
| `firstChaos_variance` | Var(W(h)) = ‖h‖². |
| `firstChaos_finiteSupport_ae` | W of a finite-support coefficient vector is the actual finite weighted coordinate sum almost everywhere. |
| `firstChaosFamily_finiteCoordinates_law` | A finite coefficient matrix A supported in a finite coordinate set s yields exactly the pushforward of the previously verified finite product Gaussian γˢ by x ↦ Ax. No invertibility or independence of output rows is required. |
| `firstChaos_isGaussianProcess` | Mathlib's `IsGaussianProcess` holds for the actual process indexed by all ℓ² vectors. |

### Noncircular limiting argument

The finite characteristic function calculation uses the previously verified
standard Gaussian evaluation laws and joint independence from the product
measure. Measurable coordinate scaling preserves independence. The genuine
one-dimensional theorem `GaussianCore.W_gaussian_law` supplies the scaled
coordinate laws; Mathlib's characteristic function product formula for independent
finite sums then proves exp(−t²Σ aₙ²/2). Uniqueness of finite measure
characteristic functions proves the finite-sum law as well.

The prior unconditional L² series theorem gives convergence of initial-segment
sums. `tendstoInMeasure_of_tendsto_Lp` explicitly proves convergence in
probability. `TendstoInMeasure.tendstoInDistribution_of_aemeasurable` then proves
convergence in distribution of the measurable representatives. Mathlib's
`TendstoInDistribution.tendsto_charFun` yields convergence to the characteristic
function of the actual limit law. These are separate proved implications;
L² convergence is not treated as the conclusion about laws.

Mathlib's `lp.hasSum_norm`, specialized to exponent two, proves Σ hₙ² = ‖h‖².
Continuity of real-to-complex coercion, scalar arithmetic and complex exponential
therefore identifies the pointwise characteristic function limit. Uniqueness of
limits equates this function with the characteristic function of W(h).
`Measure.ext_of_charFun` gives the exact centered Gaussian measure equality.
No division by ‖h‖ occurs, so the zero vector is covered by the same argument
and is explicitly identified with δ₀.

Joint Gaussianity is derived after all scalar laws are proved. Every continuous
linear form on a finite real coordinate space is expanded in coordinate unit
vectors. Exact L² linearity, plus the verified almost-everywhere representatives
of finite sums and scalar multiples, identifies its evaluation on the finite
family with an actual W of the corresponding ℓ² combination. Its scalar law is
already known. `isGaussian_of_map_eq_gaussianReal` then proves that the joint
pushforward measure is Gaussian. This requires no orthogonality, independence,
positive-definite covariance, or graph-domain hypothesis. All finite dimensions,
including dimension zero, are covered by the finite-index statements.

Centering follows by integration against the proved Gaussian law. Product
expectations reuse the original Hilbert isometry and the definition of the L²
inner product; the product is integrable by the existing L² inner-product
infrastructure. The covariance and variance identities then use the proved
centering and Mathlib's covariance/variance formulas. Joint Gaussianity is not
used to manufacture covariance or to assume an L² multiplication closure.

### Compatibility and scope

The original coordinate classes and finite Hermite, polynomial, derivative,
divergence, graph-domain and adjoint proofs are unchanged. Unit vectors in ℓ²
recover their exact coordinate classes and finite product laws. More generally,
finite-support coefficient matrices recover actual correlated and dependent
linear coordinate families as pushforwards of the same finite product Gaussian.
Tensor orthogonality continues to apply to the independent input coordinates;
it is not asserted for the correlated output coordinates.

The process is defined over the real coefficient Hilbert space ℓ². Its sample
space remains ℝ^ℕ with product measure; no identity-covariance Gaussian Radon
measure on ℓ² is claimed. Linearity of representatives is proved almost
everywhere for each fixed relation, not as a simultaneous pointwise linear
functional on all of ℓ² outside one universal null set.

The Gaussian-law, centering, joint-Gaussianity and correlated-coordinate
obligations listed in the previous milestone are resolved. Before constructing
infinite-dimensional cylindrical derivatives, the remaining requirements are:

- proved density of finite-coordinate polynomial cylinders in the full product
  Gaussian L² space (finite-dimensional density alone does not prove this);
- a genuine Hilbert-valued derivative determined by actual finite polynomial
  or smooth functions, with representation independence across finite Gaussian
  families and appropriate integrability;
- Gaussian integration by parts, a dense derivative domain, and closability;
- identification of the divergence adjoint and any claimed infinite-dimensional
  graph cores or spectral domains;
- if needed, transport from ℓ² to other separable real Hilbert index spaces
  through a chosen Hilbert-space isometry, with its compatibility proved.

No infinite-dimensional derivative, divergence, graph-domain identity, or Itô
formula is introduced in this milestone.

### Verification of the complete isonormal milestone

The full `lake build` succeeds (3345 jobs). Both new proof modules compile
without warnings; the two older unused-section-variable warnings in
`Foundation/Adjoint.lean` remain unchanged. A fresh direct Lean run of
`Foundation/AxiomAudit.lean` returns 499 results for 499 explicit axiom queries,
including all 30 new declarations. Its complete dependency set is
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom
axioms. Raw output is retained as the ignored build artifact
`.lake/build/infinite-gaussian-isonormal-axioms.log`.

The original source SHA-256 hashes still match the recorded baseline. All earlier
proof modules, dependency configuration, lockfile, and Lean toolchain are
unchanged. The root imports and audit module are extended to include the two
new verified modules.

## Full product L² polynomial cylinder density (after c1202d0)

This is the first complete milestone toward the requested infinite-dimensional
Malliavin derivative. It resolves polynomial cylinder density in the entire
countable Gaussian product L² space. It does not yet construct that derivative,
its closed extension, or a divergence operator.

### Exact core and verified declarations

`MvPolynomial ℕ ℝ` is an algebraic polynomial space: each polynomial involves
only finitely many variables. The existing sample space Ω = ℝ^ℕ and measure μ
are preserved. The new evaluation map sends p to the actual L² class of
ω ↦ p(ω), with integrability established before this class is constructed.
Its range is exactly the union of the existing finite-coordinate polynomial
spaces, not an assumed closure or merely a larger linear span.

All fourteen new declarations are in
`OperatorDerivativeRewrite.Foundation.InfiniteGaussian`:

| Declaration | Exact meaning |
| --- | --- |
| `coordinatePolynomial_memLp` | Actual evaluation of every p ∈ ℝ[ℕ] belongs to all finite Lp spaces. This is proved by finite-variable renaming and the verified finite marginal estimates. |
| `coordinatePolynomialL2` | The actual L² equivalence class of ω ↦ p(ω). |
| `coordinatePolynomialL2_coeFn` | Its representative agrees almost everywhere with actual evaluation. |
| `coordinatePolynomialEmbedding` | Linear evaluation map ℝ[ℕ] → L²(Ω, μ); its image is the algebraic coordinate polynomial core. |
| `coordinatePolynomialL2_rename` | Renaming a finite-index polynomial into natural-number variables gives exactly its existing finite-cylinder L² class. |
| `coordinatePolynomialEmbedding_range` | The image is exactly ⋃ₛ range(polynomialCylinderEmbedding s), over all finite sets s ⊆ ℕ. |
| `coordinatePolynomialEmbedding_injective` | Distinct algebraic coordinate polynomials give distinct L² classes. Two polynomials are first placed in one common finite variable set, where existing injectivity applies. |
| `ae_zero_of_cylinder_integrals` | An integrable real function whose integrals vanish on every finite measurable cylinder is zero almost everywhere; product sigma-algebra generation is proved infrastructure, not an assumption of cylinder density. |
| `orthogonal_finitePullback` | Orthogonality to every coordinate polynomial implies orthogonality to every L² class pulled back from any finite Gaussian marginal. |
| `orthogonal_cylinder_integral` | Such an orthogonal L² function has zero integral on every finite measurable cylinder. |
| `eq_zero_of_coordinatePolynomial_orthogonal` | The orthogonal complement of the algebraic coordinate polynomial core is trivial. |
| `coordinatePolynomialEmbedding_dense` | The image of the actual polynomial evaluation map is dense in the whole product Gaussian L² space. |
| `polynomialCylinders_dense` | Equivalently, the actual union of finite-coordinate polynomial spaces is dense in the whole L² space. |
| `exists_polynomialCylinder_approx` | For every f ∈ L² and ε > 0, there are a finite set s and a genuine polynomial p ∈ ℝ[s] with ‖f − polynomialCylinderEmbedding s p‖L² < ε. |

### Noncircular density proof

Every countable-variable polynomial is renamed from a finite variable set using
Mathlib's `MvPolynomial.exists_finset_rename`. Its integrability and finite
pullback identification therefore reuse the already verified finite-dimensional
results. `exists_finset_rename₂` puts two polynomials in one common finite set,
which proves injectivity without any infinite-dimensional support assumption.
These are actual finite polynomial cylinders, including constants and the
empty coordinate set.

For density, take an arbitrary f ∈ L² orthogonal to all these polynomial classes.
For each fixed finite coordinate set s, the continuous functional
 g ↦ ⟨f, finitePullback s g⟩ vanishes on the finite-dimensional polynomial image.
The previously verified finite Gaussian polynomial density theorem, plus
`Continuous.ext_on`, extends this equality to every g in that finite L² space.
Applying it to finite measurable-set indicators and transporting indicators
through the measure-preserving projection proves that ∫₍cylinder s S₎ f = 0
for every measurable S.

L² membership under this probability measure proves f is integrable. Mathlib's
`generateFrom_measurableCylinders` and `isPiSystem_measurableCylinders` identify
a generating π-system. `MeasurableSpace.induction_on_inter` extends the zero
integral identity from that system to all measurable sets: the whole-space
integral is already zero, complements use `setIntegral_compl`, and disjoint
countable unions use `integral_iUnion` with the proved integrability of f.
`Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero` then gives f = 0 almost
everywhere. The Hilbert orthogonal-complement criterion proves density of the
core. Its proved exact range identity turns this into density of the actual
union of finite-coordinate polynomial spaces. The final approximation theorem
extracts a finite-set, single-polynomial witness from metric density.

Thus finite-dimensional polynomial density is not mistaken for full product
density. Full density follows from an additional proved sigma-algebra argument.
No conditional-expectation convergence, cylinder density, or graph density is
assumed. No L² × L² → L² closure hypothesis is introduced.

### Remaining representation and operator obligations

The density result concerns independent evaluation coordinates ωₙ, which are
already proved to equal W(eₙ) as L² classes. It gives the needed dense scalar
subcore for a future operator. It does not silently restrict the requested
arbitrary-coordinate cylindrical domain to finite-support h vectors.

The following requirements of the larger Malliavin derivative objective remain:

1. Define p(W(h₁), …, W(hₙ)) and its actual ℓ²-valued derivative for arbitrary
   finite families of ℓ² vectors, with proved scalar and vector integrability.
   Infinite-support h vectors need not produce finite-coordinate polynomials
   in the sample evaluations, so this is a genuinely larger core.
2. Prove representation independence across different arbitrary families,
   including correlated and linearly dependent ones. The injectivity proved
   here is for independent coordinate polynomials only. A polynomial vanishing
   on a degenerate Gaussian family's support need not be the zero polynomial.
   One must control its derivative along the actual finite-dimensional Hilbert
   span; formal equality of polynomial expressions is insufficient.
3. Establish substantive product/chain rules, Gaussian integration by parts
   against actual finite-rank polynomial test vector fields, and density of
   the needed vector test space in L²(Ω; ℓ²).
4. Use these identities and dense test spaces to prove closability, with
   operator-domain membership kept separate from the derivative identities.
5. Construct the closed derivative and its densely defined adjoint divergence,
   with explicit actual domains. No graph-norm density, maximal-domain
   characterization, or infinite-dimensional adjoint equality is proved by
   the scalar density theorem established here.

All earlier Gaussian, finite-dimensional operator, spectral-domain, and adjoint
results remain unchanged. Work stops at this scalar density milestone as
requested; the overall Malliavin operator construction remains unfinished.

### Verification of the density milestone

The complete `lake build` succeeds (3347 jobs). Both new modules compile without
warnings; the two existing unused-section-variable warnings in
`Foundation/Adjoint.lean` remain unchanged. A fresh Lean run of the complete
`Foundation/AxiomAudit.lean` produces 513 results for 513 explicit queries,
including all fourteen new declarations. The only dependencies reported are
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or custom
axiom dependency. Raw audit output is retained in the ignored build artifact
`.lake/build/infinite-gaussian-cylinder-density-axioms.log`.

The original Lean/manuscript SHA-256 hashes remain unchanged. All previous proof
modules, the toolchain, and dependency configuration remain unchanged. The root
imports, axiom audit, and documentation are extended for this verified milestone.
The overall Malliavin operator objective remains open beyond scalar core density.

## Recovered milestone: arbitrary isonormal polynomial cylinders and gradients

Baseline: `2d31e09e71daf530c82244a6b7616218f955c83c`.
The interrupted working tree contained only the untracked
`Foundation/InfiniteGaussianCylinders.lean`; all committed files were unchanged.
Its 25 declarations already contained the cylinder construction, integrability
proofs, polynomial gradient and product rules, analytic perturbation argument,
compatibility lemmas, and scalar core density proof. A targeted Lean run found
one unfinished elaboration: the linear-coordinate derivative in
`isonormalCylinderShift_hasFDerivAt` lacked its basepoint. Recovery supplied the
explicit zero Hilbert vector and wrapped the line for the style linter. No
recovered definition, theorem statement, or mathematical hypothesis was changed.
An exact pre-repair copy is preserved in the ignored build artifact
`.lake/build/recovered-infinite-cylinders.lean`.

### Mathematical meaning of the completed declarations

Let H be the already constructed real Hilbert space ℓ², μ the countable product
of standard Gaussian measures, and W : H → L²(μ) the verified isonormal isometry.
For any finite index type I, arbitrary h : I → H, and real polynomial p in I,
write F(h,p)(ω) = p((W(hᵢ)(ω))ᵢ). No orthogonality, independence, nonzero-vector,
finite-support, or rank hypothesis is imposed on h. Actual representatives of
W(hᵢ) are used; their pointwise values are not asserted to satisfy all Hilbert
linear relations simultaneously outside one universal null set.

| Lean declarations | Precise content |
| --- | --- |
| `isonormalCylinder` | The actual scalar polynomial evaluation F(h,p). |
| `isonormalCylinder_C`, `isonormalCylinder_X` | Constants evaluate to constants; a coordinate variable evaluates to W(hᵢ). |
| `isonormalCylinder_add`, `isonormalCylinder_mul` | Evaluation respects polynomial addition and multiplication. |
| `isonormalCylinder_memLp` | F(h,p) belongs to every finite-exponent Lp(μ), proved from the genuine Gaussian marginal laws and doubled-exponent Hölder. |
| `isonormalCylinderGradient` | G(h,p)(ω) = Σᵢ (∂ᵢp)((W(hⱼ)(ω))ⱼ) hᵢ in H; partials are actual polynomial derivatives. |
| `isonormalCylinderGradient_memLp` | G(h,p) belongs to every finite-exponent Lp(μ; H), by scalar polynomial moments and finite sums of fixed Hilbert vectors. |
| `isonormalCylinderL2`, `isonormalCylinderGradientL2` | The scalar and H-valued L² classes obtained from the proved integrability. These are maps of representation data (h,p), not an operator on scalar L² classes. |
| `isonormalCylinderL2_coeFn`, `isonormalCylinderGradientL2_coeFn` | Their Lp representatives agree almost everywhere with F and G, respectively. |
| `isonormalCylinderGradient_C`, `isonormalCylinderGradient_X` | The gradient of a constant is zero; the gradient of the i-th coordinate is hᵢ. |
| `isonormalCylinderGradient_add` | G(h,p+q) = G(h,p) + G(h,q), pointwise. |
| `isonormalCylinderGradient_mul` | G(h,pq) = F(h,p) G(h,q) + F(h,q) G(h,p), proved using the genuine polynomial partial-derivative product rule. |
| `isonormalCylinderShift` | The actual Hilbert-space polynomial Ψ(h,p,ω)(v) = p((W(hᵢ)(ω) + ⟨hᵢ,v⟩)ᵢ). |
| `isonormalCylinderShift_hasFDerivAt`, `isonormalCylinderShift_fderiv` | Ψ has the genuine Fréchet derivative at v=0 given by the continuous linear functional v ↦ ⟨G(h,p)(ω),v⟩. The proof uses analytic constant, sum, and product differentiation. |
| `isonormalCylinderShift_product_rule` | The actual Fréchet derivative at zero of Ψ(h,p,ω) Ψ(h,q,ω) is represented by F(h,p) G(h,q) + F(h,q) G(h,p). |
| `isonormalCylinder_smulGradient_memLp` | Each product-rule term F(h,p) G(h,q) has every finite Lp moment, using both factors at exponent 2r. This is polynomial-core closure, not L² × L² → L² closure. |
| `isonormalCylinderL2_units` | Choosing hᵢ to be the corresponding coordinate unit vectors recovers the existing finite-coordinate polynomial embedding as an L² class. |
| `isonormalCylinderL2_rename_units` | Polynomial renaming along any finite map into ℕ agrees with evaluation at the corresponding isonormal unit vectors; injectivity of that map is not required. |
| `isonormalPolynomialCore` | The set of scalar L² classes represented by some polynomial in an arbitrary finite family of H directions. No derivative graph is attached to this set. |
| `isonormalPolynomialCore_dense` | This scalar set is dense in the entire Gaussian L² space because it contains the previously proved dense coordinate-polynomial subcore. |

The statements allow empty finite index types: the sum defining G is then zero,
and the polynomial is constant. Thus no positive-dimension restriction is hidden.
The new core also allows infinite-support h vectors. Existing independent
coordinate constructions and all prior operator results are preserved.

### Scope of genuine differentiation and the explicit open obligation

The verified derivative is the derivative of the displayed affine-coordinate
function on H for each fixed ω. This is substantive analytic differentiation,
not independently prescribed derivative data. It does not yet identify Ψ with
F evaluated at a translated sample ω+v. Such an identification requires an
almost-everywhere translation argument for the chosen W representatives,
including the relevant Cameron–Martin measure facts; none is assumed here.

Representation independence remains unproved: from
F(h,p) = F(k,q) almost everywhere, one must prove
G(h,p) = G(k,q) almost everywhere, even for different finite index types and
linearly dependent families. The finite-dimensional representation-independence
results do not apply directly to the infinite product sample space. In
particular, a degenerate Gaussian coordinate law does not have full support in
the ambient coordinate space, so scalar equality does not justify formal
polynomial equality or unrestricted equality of coordinate partial derivatives.

A possible noncircular route is to take the common finite-dimensional span of
both families, choose an orthonormal basis, prove its W coordinates have the
standard Gaussian joint law, transport both polynomials using the proved
almost-everywhere linear relations, and apply full-support polynomial
uniqueness and genuine differentiation on that span. The span inclusion must
then transport the gradient identity back to H. These transports and the
common-span comparison are future proof obligations, not hypotheses introduced
into any completed theorem.

Consequently, no Malliavin derivative operator on scalar L² equivalence classes,
infinite-dimensional Gaussian integration by parts, gradient closability,
vector test-space density, divergence adjoint, graph-domain characterization,
or infinite-dimensional adjoint equality is claimed. The present product rules
hold for actual polynomial representations within one chosen family. They do
not discharge the comparison between distinct representations. Full smooth
cylinders and infinite-dimensional chain rules also remain beyond this milestone.

### Verification and preservation

The complete Lake build succeeds (3348 jobs). The recovered module compiles
without warnings after the line wrap; the two pre-existing unused-variable
warnings in `Foundation/Adjoint.lean` remain. The full axiom audit has 538 explicit
queries and 538 verified results, including all 25 recovered declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur: no `sorryAx` or custom
axioms. The raw output is preserved in the ignored build artifact
`.lake/build/infinite-gaussian-cylinders-axioms.log`. A source scan found no
`sorry`, `admit`, or custom axiom declarations in Foundation.

The original Lean and manuscript SHA-256 hashes match the previously recorded
values. Earlier proof modules, toolchain, and dependency lockfile are unchanged.
Only the recovered module, project root import, axiom queries, and documentation
are included in this milestone. This section supersedes the earlier density
milestone's open items about arbitrary-cylinder integrability and polynomial
product differentiation; its representation, integration-by-parts, and operator
obligations remain open as specified above.

## Representation-independent infinite-dimensional polynomial derivative

Baseline: `fb17f970af28169e93e7cc7acab6402123c04e4e`. The starting working tree
was clean. The previous cylinder definitions and all earlier proof modules are
preserved unchanged. This milestone proves the previously explicit
representation-independence obligation and constructs the genuine derivative
on the scalar polynomial cylindrical subspace. It stops before Gaussian
integration by parts or closability.

### Common finite-dimensional Gaussian realization

`Foundation/InfiniteGaussianRepresentation.lean` has seven declarations:

| Declaration | Exact mathematical content |
| --- | --- |
| `finiteGaussianPoint` | For a finite-dimensional real Hilbert space E, an isometric linear inclusion A : E → H, and the standard orthonormal basis (bₐ) of E, defines X_A(ω) = Σₐ W(A bₐ)(ω) bₐ. Here H is the verified ℓ² Hilbert space. |
| `finiteGaussianPoint_measurable` | This actual E-valued random vector is measurable. |
| `finiteGaussianPoint_coordinate` | For every v ∈ E, W(A v) = ⟨v,X_A⟩ almost everywhere, by proved finite-sum W linearity and orthonormal basis reconstruction. |
| `finiteGaussianPoint_law` | μ.map X_A = stdGaussian E, proved by characteristic functions of the preceding coordinates, the verified first-chaos Gaussian law, and ‖A v‖ = ‖v‖. No law or independence is assumed. |
| `isonormalCylinder_finiteGaussianPoint` | F(Ah,p) = cylinder(h,p)(X_A) almost everywhere for every finite family h in E. |
| `isonormalCylinderGradient_finiteGaussianPoint` | G(Ah,p) = A(cylinderGradient(h,p)(X_A)) almost everywhere; the finite and infinite genuine gradient formulas are compatible through the linear inclusion. |
| `isonormalCylinderGradientL2_representation_independent` | For arbitrary finite index types I,J, arbitrary h : I → H and k : J → H, and polynomials p,q, F(h,p) = F(k,q) as scalar L² classes implies G(h,p) = G(k,q) as H-valued L² classes. There are no rank, independence, orthogonality, finite-support, or derivative-equality hypotheses. |

For the last theorem, take S = span(range h ∪ range k) inside H. Finiteness of
both families proves finite dimensionality of S. Equip S with its Borel sigma
algebra, use its standard orthonormal basis, and apply the realization above to
its isometric subtype inclusion A. Each hᵢ and kⱼ is lifted to S using proved
span membership. The scalar transport lemmas and the assumed scalar L² equality
give equality of the two finite-space cylinder functions at X_A almost
everywhere. Their equality set is closed because both functions are continuous,
hence measurable. The proved pushforward law transfers that equality to
stdGaussian S. The previously verified
`FiniteGaussian.cylinderGradient_representation_independent` then gives equality
of their gradients everywhere on S; transport through A and the actual gradient
compatibility lemmas gives equality of the H-valued L² classes.

Full support is used on S, not on the possibly degenerate original coordinate
space. Consequently, dependent-coordinate polynomial evaluation is never
asserted to be injective. The original formal polynomials need not be equal.
The proof also covers S = {0} and empty families: all basis sums and all scalar
projection laws used above remain valid in dimension zero.

### The actual polynomial scalar L² domain and derivative

`Foundation/InfiniteGaussianDerivative.lean` establishes the following:

| Declarations | Mathematical content |
| --- | --- |
| `isonormalCylinderL2_rename` | Renaming polynomial variables along any finite map agrees with composing the Hilbert coordinate family with that map. The scalar statement needs no finite-type hypothesis. |
| `isonormalCylinderGradientL2_rename` | The genuine L² gradients agree under that same renaming, deduced from the proved representation-independence theorem and scalar equality. |
| `isonormalCylinderL2_add`, `isonormalCylinderGradientL2_add` | Polynomial addition gives addition of actual scalar and gradient L² classes. |
| `isonormalCylinderL2_const_mul`, `isonormalCylinderGradientL2_const_mul` | Multiplying a polynomial by a real constant gives scalar multiplication of the actual scalar and gradient classes. |
| `isonormalCylinderL2_mem_core` | A cylinder indexed by any finite type belongs to the original Fin-indexed scalar core, via a proved finite equivalence and renaming. |
| `isonormalPolynomialCore_zero`, `isonormalPolynomialCore_add`, `isonormalPolynomialCore_smul` | Zero, addition, and real scalar multiplication preserve the scalar core. Addition uses a common disjoint-union family, not an assumed closure property. |
| `polynomialCylindricalDomain` | The resulting real submodule of the actual scalar Gaussian L² space, with carrier exactly the previously defined isonormalPolynomialCore. |
| `PolynomialRepresentation`, its four fields, `polynomialRepresentation` | Witness data for a scalar domain element: dimension, Hilbert directions, an actual polynomial, and equality of its evaluated scalar L² class to the element. A witness is chosen noncomputably from proved membership; it contains no independently prescribed derivative value. |
| `polynomialGradient` | The H-valued L² gradient of that chosen representation. |
| `polynomialGradient_agrees` | For every representation (h,p) of f, the chosen value equals G(h,p) in H-valued L², using the proved comparison theorem. Its scalar representation equality is the definition of being a representation, not a gradient-equality assumption. |
| `polynomialGradient_add`, `polynomialGradient_smul` | The representation-independent gradient is a real linear map, with addition compared in a common family and scalar multiplication reduced to constant-polynomial multiplication. |
| `polynomialDerivative` | The genuine linear operator D : polynomialCylindricalDomain → L²(μ; H), implemented as a LinearMap on that submodule. No closed extension is asserted. |
| `polynomialCylindricalDomain_dense` | Its scalar domain is dense in the full ambient Gaussian L² space, using the already proved core-density theorem. |
| `polynomialDerivative_on_cylinder` | D of the domain element represented by F(h,p) equals G(h,p), for every finite representation. |
| `polynomialDerivative_empty` | For any polynomial in an empty coordinate family, the actual domain derivative is zero. |

Noncomputable witness choice affects neither operator values nor the operator's
mathematical meaning: `polynomialGradient_agrees` proves that every witness has
the same value. No arbitrary representation-independence hypothesis or custom
axiom is introduced. The derivative is a densely defined linear operator on the
polynomial domain; no domain of a closure is being substituted for this domain.

### Intrinsic products and Leibniz with correct integrability

`Foundation/InfiniteGaussianPolynomialProducts.lean` has thirteen declarations:

| Declarations | Mathematical content |
| --- | --- |
| `exists_common_polynomial_representation` | Any two scalar domain elements admit a common finite Hilbert family and two actual polynomials representing them. The construction combines their witnesses and renames into one Fin-indexed family. |
| `polynomialDomain_memLp`, `polynomialDerivative_memLp` | Actual representatives of every domain element and its genuine derivative have every finite Lp moment, by almost-everywhere transport of the earlier polynomial moment proofs. |
| `polynomialDomain_mul_memLp` | The product of two domain elements' scalar representatives has every finite Lp moment; exponent r uses both input moments at 2r and Hölder. |
| `polynomialProductL2`, `polynomialProductL2_coeFn` | The actual scalar L² class of their pointwise product and its almost-everywhere representative identity. |
| `polynomialProductL2_agrees` | In any common polynomial representation, this actual L² product equals the evaluation class of p q. |
| `polynomialProductL2_mem_domain` | This product belongs to the scalar cylindrical subspace, proved from a common representation and polynomial multiplication. |
| `polynomialProduct` | Multiplication of actual domain elements, returning a domain element with the proved membership witness. |
| `polynomialDomain_smul_derivative_memLp` | f Dg has every finite Lp moment; in particular, L⁴ × L⁴ → L² proves membership at r=2. |
| `polynomialTimesDerivative`, `polynomialTimesDerivative_coeFn` | The actual H-valued L² class of f Dg and its almost-everywhere representative identity. |
| `polynomialDerivative_product` | For all actual domain elements f,g, D(polynomialProduct f g) = polynomialTimesDerivative f g + polynomialTimesDerivative g f as H-valued L² classes. This is the intrinsic Leibniz identity D(fg)=f Dg+g Df. |

Product closure and the Leibniz identity have separate proofs. Membership is
established through scalar polynomial multiplication and higher moments before
the derivative identity is proved. The identity then uses genuine partial
differentiation in a common representation and the independently established
representation comparison. This does not introduce L² × L² → L² closure outside
the polynomial domain, nor boundedness of polynomial multiplication on L².

### Verification, dependencies, and remaining obligations

The full `lake build` passes (3351 jobs). All three new modules compile without
warnings; only the two pre-existing unused-variable warnings in Adjoint remain.
The complete axiom audit includes 583 queries and 583 results: all earlier 538
queries plus 45 queries for the new declarations and representation fields.
The dependency union is only `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx` or custom axiom. The raw audit output is saved as the ignored
build artifact `.lake/build/infinite-gaussian-representation-axioms.log`.

Earlier proof modules, the original Lean source and manuscript, toolchain, and
dependency configuration remain unchanged. Root imports, axiom queries, and
project documentation are extended for these three new modules.

Representation independence is now proved for polynomial cylinders on the
verified countable-product isonormal model over H = ℓ². This supersedes the open
representation obligation of the preceding milestone. Extension to a general
abstract separable Hilbert space/model, non-polynomial smooth cylinder classes,
and translation compatibility of sample representatives are not claimed here.
Gaussian integration by parts for this actual infinite-dimensional operator,
density of the necessary vector test fields, closability, its closed extension,
divergence adjoints, and graph-domain characterizations remain unproved. No
closed-domain algebra or graph-norm density assertion is inferred from the
polynomial-domain product rule. The next analytic milestone is Gaussian
integration by parts with proved test-space density, then closability.

## Genuine Gaussian IBP, dense finite-rank divergence fields, and closability

Baseline: `baa5f859a066e6eb5b57ad3f16c2bcd25221cb36`. The starting working tree
was clean. This milestone preserves the existing polynomial derivative,
representation independence, scalar domain, and product results. It establishes
Gaussian integration by parts and closes the actual polynomial derivative on
the verified countable-product isonormal model over H = ℓ².

### Directional finite-Hilbert Gaussian analysis

`Foundation/FiniteGaussianDirectionalIBP.lean` has five declarations:

| Declaration | Exact mathematical meaning |
| --- | --- |
| `basisPolynomialMap` | For arbitrary finite hᵢ in a finite-dimensional Hilbert space E, substitutes the genuine linear polynomial Σₐ ⟨hᵢ,bₐ⟩ Xₐ into p, where (bₐ) is the standard orthonormal basis of E. This is a ring homomorphism of actual polynomial algebras. |
| `basisPolynomialMap_eval` | Evaluation of that substituted polynomial at y is exactly p((⟨hᵢ,Σₐ yₐ bₐ⟩)ᵢ). No coordinate-rank assumption is imposed. |
| `basisPolynomialMap_pderiv_eval` | Its a-th evaluated partial derivative is ⟨cylinderGradient(h,p)(Σₐ yₐ bₐ),bₐ⟩. The proof differentiates the actual substituted polynomial, using the true polynomial product rule. |
| `cylinder_stein_basis` | E[⟨gradient(h,p),bₐ⟩] = E[cylinder(h,p) ⟨bₐ,x⟩] under stdGaussian E, transported from the previously proved independent-coordinate polynomial Stein theorem. |
| `cylinder_stein` | E[⟨gradient(h,p),v⟩] = E[cylinder(h,p) ⟨v,x⟩] for every v ∈ E, by orthonormal reconstruction, proved integrability, and finite-sum integration. |

This is the missing analytic bridge between the original independent-coordinate
IBP theorem and arbitrary finite Hilbert families. It does not treat correlated
coordinates as independent tensor coordinates. Empty index families and
zero-dimensional Hilbert spaces are allowed.

### Actual vector test core and its proved density

`Foundation/InfiniteGaussianVectorCore.lean` has eight declarations:

| Declarations | Exact mathematical meaning |
| --- | --- |
| `GaussianVectorL2` | Mathlib L²(μ; H), using the genuine ℓ² Hilbert fiber norm. |
| `scalarTensor`, `scalarTensor_coeFn` | The bounded linear map f ↦ f h from scalar L² to H-valued L², and its actual almost-everywhere representative formula. It uses the existing continuous-linear-map Lp composition infrastructure. |
| `cylindricalVectorDomain` | The algebraic span of actual G h fields, with G in the already verified scalar polynomial cylindrical subspace and h arbitrary in H. |
| `scalarTensor_mem_domain` | Every such rank-one polynomial field belongs to that core. |
| `scalarTensor_inner` | ⟨f h,u⟩ in vector L² equals the scalar L² pairing of f with the actual projected field ⟨h,u⟩. |
| `eq_zero_of_cylindricalVector_orthogonal` | A vector L² field orthogonal to every rank-one polynomial field is zero. Scalar cylinder density first kills every scalar projected field; countably many ℓ² unit-coordinate projections then kill its actual representative almost everywhere. |
| `cylindricalVectorDomain_dense` | This core is dense in the entire H-valued Gaussian L² space, by the Hilbert orthogonal-complement criterion. |

Density is not assumed from scalar density alone. The proof establishes the
projection pairing, uses the already proved scalar density, and separately
uses completeness of the ℓ² coordinate system. The later exact finite-sum
characterization and norm-approximation theorem identify the dense set with
genuine finite-rank polynomial fields, rather than an unspecified vector domain.

### Genuine infinite-cylinder Stein and rank-one IBP

`Foundation/InfiniteGaussianIBP.lean` has nine declarations:

| Declarations | Exact mathematical meaning |
| --- | --- |
| `isonormalCylinder_stein` | For arbitrary finite h, polynomial p, and v ∈ H, E[⟨G(h,p),v⟩] = E[F(h,p) W(v)]. The proof transports both sides to the standard Gaussian on span(range h ∪ {v}) using the previously proved genuine finite realization and gradient compatibility. |
| `polynomialDerivative_stein` | The same identity E[⟨D₀F,v⟩] = E[F W(v)] on the actual representation-independent scalar L² polynomial domain. |
| `polynomial_times_firstChaos_memLp` | F W(h) has every finite Lp moment. At exponent r, both input moments at 2r are proved and Hölder is applied. |
| `polynomial_directional_memLp` | ⟨D₀G,h⟩ has every finite Lp moment, using the proved vector derivative moments and a fixed Hilbert direction. |
| `rankDivergence_memLp` | G W(h) − ⟨D₀G,h⟩ has every finite Lp moment. |
| `rankDivergence`, `rankDivergence_coeFn` | Its actual scalar L² class and the proved almost-everywhere expression δ₀(Gh)=G W(h)−⟨D₀G,h⟩. |
| `polynomialDerivative_rank_integration_by_parts` | E[⟨D₀F,Gh⟩] = E[F rankDivergence(G,h)] for all scalar polynomial-domain F,G and arbitrary h ∈ H. This follows from Stein applied to the proved intrinsic polynomial product and the actual product derivative. |
| `polynomialDerivative_rank_pairing` | The corresponding Hilbert-space pairing identity ⟨D₀F,Gh⟩_{L²(H)} = ⟨F,rankDivergence(G,h)⟩_{L²}. |

The rank-one IBP proof establishes integrability before splitting sums or
subtracting integrals: F⟨D₀G,h⟩ and G⟨D₀F,h⟩ use L² × L² → L¹; F(GW(h)) uses
the independently proved L² membership of GW(h). Fourth moments justify that
membership. No L² × L² → L² closure is assumed.

### Single-valued cylindrical divergence, closed derivative, and full adjoint

`Foundation/InfiniteGaussianOperators.lean` has forty-one declarations. They
establish the following definitions and exact statements:

| Declarations | Exact mathematical meaning |
| --- | --- |
| `cylindricalDerivative` | D₀ as a Mathlib LinearPMap on ambient scalar L², with domain exactly polynomialCylindricalDomain and value exactly polynomialDerivative. |
| `cylindricalDivergenceGraph` | The algebraic span of the pairs (G h, G W(h)−⟨D₀G,h⟩) of actual L² classes. No independently prescribed output is introduced. |
| `cylindricalDivergenceGraph_pairing` | Every pair (u,v) in that span satisfies ⟨D₀F,u⟩=⟨F,v⟩ for every scalar polynomial test F. Proved rank-one IBP puts the generators in the kernel of the actual pairing-difference linear functional, hence also their span. |
| `cylindricalDivergenceGraph_vertical_zero` | If (0,v) belongs to this graph, then v=0. The pairing identity and proved scalar density force v to vanish. This proves divergence single-valuedness, rather than assuming it. |
| `cylindricalDivergence`, `cylindricalDivergence_graph` | The genuine partial linear operator δ₀ obtained from this proved single-valued graph, with its graph equal to the explicitly generated graph. |
| `cylindricalDivergence_rank_graph` | Each actual rank-one field has precisely its explicit rankDivergence value in δ₀'s graph. |
| `cylindricalDivergence_domain` | The domain of δ₀ is exactly cylindricalVectorDomain; both inclusions are proved. |
| `cylindricalDerivative_dense_domain`, `cylindricalDivergence_dense_domain` | Both actual operator domains are dense in their respective ambient L² spaces. |
| `cylindricalDerivative_formalAdjoint` | The Hilbert IBP identity on both actual restricted operator domains. |
| `cylindricalDerivative_le_divergence_adjoint`, `cylindricalDivergence_le_derivative_adjoint` | D₀ ⊆ δ₀* and δ₀ ⊆ D₀*, with domain inclusion and values proved from IBP and the relevant proved domain density. |
| `cylindricalDerivative_isClosable` | D₀ is closable because it is contained in the closed adjoint δ₀* of a densely defined operator. This uses the genuine IBP and vector density already proved. |
| `cylindricalDivergence_isClosable` | δ₀ is also closable, using its proved inclusion in the closed adjoint D₀*. |
| `closedCylindricalDerivative`, `closedCylindricalDerivative_isClosed`, `closedCylindricalDerivative_dense_domain` | D is the actual graph closure of D₀; closability proves that it is a closed densely defined operator. |
| `closedCylindricalDerivative_graph`, `closedCylindricalDerivative_mem_iff` | graph(D)=closure(graph(D₀)); F∈Dom(D) iff there exists V∈L²(μ;H) with (F,V) in that graph closure. These are exact graph domains, with no unproved Sobolev characterization imposed. |
| `hilbertDivergence` | The full natural Hilbert-space adjoint δ=D*. |
| `hilbertDivergence_eq_cylindricalDerivative_adjoint` | D*=D₀*, by the previously proved generic closure-adjoint theorem and the newly proved closability and density. |
| `cylindricalDivergence_le_hilbertDivergence` | δ₀ ⊆ δ, with actual domain and value inclusion. |
| `hilbertDivergence_isClosed`, `hilbertDivergence_dense_domain` | δ is closed because D is densely defined, and is densely defined because its domain contains the proved dense domain of δ₀. |
| `hilbertDivergence_mem_iff` | u∈Dom(δ) iff there exists v∈scalar L² such that ⟨DF,u⟩=⟨F,v⟩ for every F∈Dom(D). This is an exact weak-divergence domain characterization proved from the natural adjoint definition and its pairing identity. |
| `cylindricalField`, `cylindricalDivergenceExpression` | The actual finite sums u=Σⱼ Gⱼ hⱼ and v=Σⱼ(GⱼW(hⱼ)−⟨D₀Gⱼ,hⱼ⟩), for arbitrary finite index types. |
| `cylindricalDivergence_field_graph`, `cylindricalField_mem_domain`, `cylindricalDivergence_field_apply` | Every finite sum belongs to δ₀'s domain, its explicit sum expression is in the graph, and applying δ₀ gives that expression for any domain proof. |
| `cylindricalDivergence_representation_independent` | If two arbitrary finite decompositions give the same H-valued L² field, their divergence sum expressions are equal as scalar L² classes. This follows from the proved graph single-valuedness; no decomposition-independence hypothesis is used. |
| `cylindricalField_integration_by_parts` | For every scalar polynomial F and every actual finite-rank cylindrical u, E[⟨D₀F,u⟩]=E[F δ₀u]. |
| `cylindricalField_ibp_integrable` | Both integrands in that finite-field identity are integrable, proved by vector Hölder and scalar L² product integrability. |
| `closedCylindricalDerivative_core_graph`, `closedCylindricalDerivative_core_mem`, `closedCylindricalDerivative_core_apply` | Every original scalar polynomial-domain F belongs to Dom(D), and DF retains exactly its genuine polynomial derivative D₀F. |
| `hilbertDivergence_field_graph` | The full adjoint δ contains every finite-rank field with precisely the explicit cylindrical divergence value. |
| `cylindricalVectorDomain_mem_iff` | The vector core consists exactly of finite sums Gⱼ hⱼ, with a Fin n representation. The proof extracts finite span witnesses and absorbs real coefficients into the scalar polynomial-domain elements. |
| `closedCylindricalDerivative_le_cylindricalDivergence_adjoint` | D ⊆ δ₀* is a proved closed-operator inclusion. No equality is inferred. |
| `exists_cylindricalField_approx` | For every u∈L²(μ;H) and ε>0, there is one genuine finite-rank polynomial field Σⱼ Gⱼhⱼ with L² distance less than ε. |

Thus operator-domain membership, actual expressions, integration by parts,
single-valuedness, and closability are separate verified steps. The natural
adjoint domain uses the ambient L² norm on Dom(D), not an assumed graph-norm
boundedness condition. Its weak divergence v is uniquely determined because
Dom(D) is dense. No arbitrary adjoint-domain or graph-density assumption occurs.

### Exact remaining obligations and verification

The strongest proved relations here are
D₀ ⊆ δ₀*, D=closure(D₀) ⊆ δ₀*, and δ₀ ⊆ D₀*=D*=δ.
These do not establish closure(δ₀)=δ or D=δ₀*. A graph-core/essential-adjointness
argument would be needed for those stronger identifications. No graph-norm
density of the vector polynomial core in Dom(δ) has been proved here.

All construction remains on the genuine countable-product Gaussian model over
H=ℓ², allowing arbitrary directions, including infinite-support, dependent,
correlated, and zero directions. Extension to other abstract Hilbert models,
non-polynomial smooth cylinders, sample-space translation/Cameron–Martin
compatibility, maximal Sobolev or chaos spectral domains, and advanced stochastic
calculus/Itô results remain future work. No multiplication-algebra claim is made
for Dom(D) or Dom(δ), and no equality with a bounded energy-space interface is
assumed.

The full Lake build passes (3355 jobs). All four new modules compile without
warnings; the two existing unused-variable warnings in Adjoint remain unchanged.
The complete axiom audit has 646 queries and 646 results, including all 63 new
declarations. Its dependency union is only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or custom axioms occur. The raw output is retained in
`.lake/build/infinite-gaussian-ibp-closability-axioms.log`, an ignored build
artifact. The Foundation source scan finds no `sorry`, `admit`, or custom axiom
declarations.

The original Lean and manuscript hashes and all earlier proof modules remain
unchanged. Only these four new proof modules, root imports, axiom queries, and
documentation are included. This section supersedes the preceding milestone's
open IBP, vector density, closability, and natural closed-operator/adjoint
construction obligations, while preserving the explicit unresolved graph-core
and full-domain identification obligations above.

## Finite-coordinate divergence graph approximation (continuing 65a6afbf)

### Outcome and scope

This milestone proves that every maximal divergence graph on a finite set of
independent Gaussian coordinates embeds in the graph closure of the genuine
infinite-dimensional polynomial divergence. Its total-degree Hermite
approximations converge in the actual infinite-space divergence graph norm,
preserving cancellations. It also proves the operator-first identity δ* = D
for the full divergence δ = D*, and proves that the two requested polynomial
core identities are equivalent. Neither polynomial core identity is asserted.

The model is still Ω = ℝ^ℕ with countable product standard Gaussian measure μ,
H = ℓ²(ℕ;ℝ), scalar L²(μ), and vector L²(μ;H). Existing arbitrary-direction
polynomial cylinders, including dependent, correlated, and infinite-support
directions, are preserved. The new tensor truncations apply specifically to
finite sets of independent standard coordinates, not to arbitrary correlated
coordinate lists.

### Exact new definitions and statements

`Foundation/AdjointBidual.lean` supplies two reusable real Hilbert-space theorems:

- `closedOperator_adjoint_adjoint_eq`: if T is closed and both T and T* have
  dense ambient domains, T** = T. The reverse inclusion uses orthogonal
  separation of the closed graph in the Hilbert product `WithLp 2 (E × F)`.
- `closableOperator_adjoint_adjoint_eq_closure`: if T is closable and both
  ambient domains are dense, T** = closure(T). The proof uses the preceding
  theorem and the already verified fact that graph closure leaves T* unchanged.

No graph-density assumption occurs in either statement. All their density
hypotheses are discharged by existing concrete theorems in the applications.

`Foundation/InfiniteGaussianFiniteSectors.lean` defines and proves:

| Declaration | Exact mathematical meaning |
| --- | --- |
| `coordinatePolynomialDomain s p` | The actual class p((ωᵢ)ᵢ∈s), as a member of the existing intrinsic scalar polynomial domain. Membership follows from unit-direction isonormal cylinders. |
| `coordinatePolynomialDomain_derivative_coeFn` | Its actual derivative is almost everywhere Σᵢ∈s (∂ᵢp)((ωⱼ)ⱼ∈s)eᵢ. The proof uses the representation-independent genuine derivative, not prescribed derivative values. |
| `finiteVectorPullback s` | A bounded linear map Jₛ from finite vector Gaussian L² to L²(μ;H), defined by Jₛu = Σᵢ∈s eᵢ Iₛ(uᵢ), where Iₛ is the previously verified scalar isometric pullback and uᵢ is the actual L² component. |
| `finiteVectorPullback_apply`, `finiteVectorPullback_polynomial` | The exact component sum formula and its identification with an actual finite-rank cylindrical field for polynomial vectors. |
| `rankDivergence_coordinate` | δ₀(p eᵢ) is the actual pullback of xᵢp − ∂ᵢp. The derivative contribution is computed using actual partial derivatives and orthogonality of the coordinate units. |
| `finitePolynomialDivergence_lift_graph` | For every finite polynomial vector u, (Jₛu, Iₛδ₀,ₛu) belongs to the existing genuine infinite δ₀ graph. |
| `closedPolynomialDivergence` | Exactly closure(δ₀), using the already proved closability; it is not defined to be δ. |
| `closedPolynomialDivergence_isClosed` | This actual graph closure is closed. |
| `closedPolynomialDivergence_le_hilbertDivergence` | closure(δ₀) ⊆ δ, including domains and values, by closed-extension minimality. |
| `closedPolynomialDivergence_adjoint_eq` | closure(δ₀)* = δ₀*. |
| `finiteDivergence_truncation_lift_graph` | If (u,g) lies in the full finite adjoint ∇₀,ₛ* graph, then (Jₛu≤N, Iₛg≤N+1) lies in the genuine infinite polynomial δ₀ graph for every N. |
| `finiteDivergence_truncation_lift_tendsto` | Both coordinates of these lifted truncations converge in their infinite-space L² norms to (Jₛu,Iₛg). |
| `finiteDivergence_truncation_lift_graphNorm_tendsto` | The squared graph error ‖Jₛu≤N − Jₛu‖² + ‖Iₛg≤N+1 − Iₛg‖² tends to zero. This convergence lemma is separate from graph membership. |
| `finiteDivergence_lift_closed_graph` | Every full maximal finite divergence pair (u,g) lifts to graph(closure(δ₀)). This follows from the explicit polynomial graph sequence. |
| `finiteDivergence_lift_hilbert_graph` | The same pair belongs to graph(δ), with the same value. |
| `finiteDivergence_coefficients_lift_closed_graph` | If the actual scalar coefficients of g equal the combined divergence coefficients of u, the lifted pair belongs to graph(closure(δ₀)). This uses proved finite coefficient realization; equality of coefficients is the exact spectral graph condition, not a presumed core property. |
| `finiteDivergence_domain_lift` | The genuine condition Σβ bβ² < ∞ supplies an actual scalar g and puts (Jₛu,Iₛg) in graph(closure(δ₀)). Integrability and realization are proved by the existing finite spectral theorem. |
| `finiteVectorPullback_empty` | J∅u = 0; all finite-sector graph theorems also allow dimension zero. The finite adjoint restricts its scalar output to zero in that dimension. |
| `coordinatePolynomialDomain_derivative_lift` | D₀(Iₛp) = Jₛ(∇₀,ₛp), as actual vector L² classes. |
| `finitePolynomialGradient_lift_graph` | Every finite polynomial gradient graph lifts to the genuine infinite D₀ graph. |
| `finiteGradient_lift_closed_graph` | Every full maximal finite gradient graph lifts to graph(D), by the proved finite Hermite graph approximations. |
| `hilbertDivergence_adjoint_eq_closedDerivative` | δ* = D, using D's proved closedness, D-domain density, and δ-domain density. |
| `cylindricalDivergence_adjoint_dense_domain` | Dom(δ₀*) is dense because it contains the already proved dense Dom(D). |
| `cylindricalDivergence_adjoint_adjoint_eq_closedPolynomialDivergence` | δ₀** = closure(δ₀), using concrete closability and both concrete density proofs. |
| `polynomialDivergence_core_iff_adjoint_identification` | closure(δ₀) = δ if and only if δ₀* = D. Taking adjoints uses the proved identities above. This equivalence does not establish either equality. |

### Combined coefficients and cancellation

For u in a finite coordinate sector the spectral divergence condition is

    bβ = Σᵢ:βᵢ≥1 √βᵢ uᵢ,β−eᵢ,
    Σβ |bβ|² < ∞.

Every vector component uses the same total-degree cutoff |α| ≤ N. A coefficient
contributing to bβ has degree |β|−1, regardless of which component contributes.
Thus the finite theorem `divergenceCoefficient_truncation` retains the entire
sum when |β| ≤ N+1 and removes it otherwise. The lifted graph theorem reuses
that exact result. It never demands Σᵢ,α (αᵢ+1)|uᵢ,α|² < ∞, which would be
stronger and would exclude legitimate cancellations. Scalar coefficient
realization and graph membership are established before the graph limit is used.

### Exact remaining analytic bridge

L² density of polynomial fields does not imply graph density in Dom(δ).
The unproved step is approximation of an arbitrary full infinite divergence
pair by maximal finite-coordinate divergence pairs. This milestone handles
all inner Hermite approximations after such a finite pair has been obtained.

A concrete sufficient bridge is the following finite-coordinate conditional
expectation theorem, which is NOT assumed or formalized as an axiom:

Let Sₙ = {0,...,n−1}, let Eₙ be conditional expectation onto σ(ωᵢ : i∈Sₙ),
and let πₙ be the Hilbert projection onto span{eᵢ : i∈Sₙ}. For every F∈Dom(D),

    EₙF ∈ Dom(D),    D(EₙF) = πₙ Eₙ(DF).

Here vector conditional expectation acts on the H-valued random field before
πₙ. The required next construction identifies scalar finite pullbacks with
that measurable subspace and identifies Jₛ with its finite vector counterpart.
Mathlib already provides `condExpL2`, its contraction property, and its
almost-everywhere agreement with conditional expectation in
`MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean` and `Basic.lean`.
The missing result is compatibility with this project's genuine cylindrical
D and the finite Gaussian operators, not existence of conditional expectation.

For arbitrary-direction polynomial cylinders, a noncircular route is to split
each h into πₙh and (1−πₙ)h, prove Gaussian independence of these orthogonal
families, integrate the residual polynomial using its established Gaussian
moments, and prove the displayed derivative identity by actual polynomial
partial differentiation. Contraction and closedness then extend it to Dom(D).
This remains an obligation, including infinite-support h; it is not supplied
as a hypothesis to any completed theorem.

Duality would then give, for every (u,v)∈graph(δ),

    uₙ = πₙ Eₙu ∈ Dom(δ),    δuₙ = Eₙv,

and identify (uₙ,Eₙv) with an actual finite adjoint graph. One must additionally
prove uₙ→u in vector L² and Eₙv→v in scalar L². The existing scalar polynomial
density and coordinate completeness can supply this convergence with the
uniform contraction estimates; an L¹ martingale limit alone is insufficient.
Combining these outer approximations with the now verified inner Hermite
approximations would prove closure(δ₀)=δ, and then δ₀*=D by the verified
bidual equivalence. No mathematical counterexample to either equality is
claimed; the obstruction here is an unfinished analytic compatibility proof.

### Operator-first manuscript identification

`OperatorDerivative.lean:57–80` defines the operator derivative as the natural
unbounded adjoint. `OperatorDerivative.tex:48–52` takes δ as primitive and
`OperatorDerivative.tex:500–504` describes the Gaussian cylindrical derivative,
its graph closure, and the Skorokhod adjoint. The verified concrete full δ now
recovers exactly D = δ*. This is a valid operator-first identification on the
countable Gaussian model, without presuming the polynomial divergence core.
Choosing δ₀ or closure(δ₀) as the primitive integral would instead give δ₀*,
which is only known to contain D. Its equality with D is precisely the open
core problem. None of these statements supplies predictable isometry, PRP,
Clark–Ocone hypotheses, or an identification with the original bounded energy
interface. The polynomial core is distinct from the manuscript's smooth
bounded cylindrical core; equality of their graph closures is not asserted.

### Verification

The complete `lake build` passes (3357 jobs). Both new proof modules compile
without warnings; the two longstanding unused-variable warnings in Adjoint
are unchanged. The complete axiom audit has 674 queries and 674 results,
including all 28 new declarations. Its dependency union is only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx` or custom axiom.
The raw output is retained in the ignored artifact
`.lake/build/infinite-gaussian-finite-sectors-axioms.log`. The Foundation
source scan finds no `sorry`, `admit`, or custom axiom declarations.
The original Lean and TeX sources and all earlier proof modules are unchanged.

## Finite-coordinate weak-gradient bridge (current milestone)

The two target identities remain **unproved**:

    closure(δ₀) = δ = D*,       δ₀* = D.

The existing finite-sector Hermite truncation gives graph approximation **after**
an infinite field has been identified with a maximal finite-sector divergence
pair. It does not provide finite-sector graph approximation of arbitrary
`u ∈ Dom(δ)`. The bidual theorem proves the displayed identities equivalent,
but neither follows from L² density alone.

`Foundation/InfiniteGaussianCoordinateFields.lean` now establishes the following
additional facts with the actual product Gaussian measure and operators:

| Declaration | Mathematical statement |
| --- | --- |
| `coordinatePolynomialVectorDomain` | The algebraic span of fields `p(ω|ₛ)eₙ`, where `s` is finite and `p` is a genuine polynomial on that finite coordinate space. |
| `coordinatePolynomialVectorDomain_le` | Every such field belongs to the actual polynomial divergence domain. This follows from the existing rank-field graph, without asserting graph closure. |
| `coordinatePolynomialVectorDomain_dense`, `exists_coordinatePolynomialVector_approx` | These finite-coordinate fields approximate every `L²(Ω;ℓ²)` field in the **ambient L² norm**. The proof uses verified scalar polynomial density and the completeness of the coordinate vectors in `ℓ²`. |
| `finiteVectorPullback_insert`, `coordinatePolynomialVector_mem_finite_sector` | A rank-one coordinate field is the pullback of a genuine finite Gaussian vector field after enlarging its coordinate set to include its output direction. |
| `eq_zero_of_finiteVectorPullback_orthogonal` | The ranges of all finite vector lifts jointly detect every vector `L²` class. This is an orthogonality statement; it is not convergence of the associated adjoint projections. |
| `finiteSector_weak_gradient_graph` | If `(F,G) ∈ graph(δ₀*)`, then `(Iₛ*F,Jₛ*G) ∈ graph(δ₀,ₛ*)` for every finite `s`, where `Iₛ` and `Jₛ` are the established scalar and vector lifts. The proof uses the actual polynomial divergence lift and Hilbert adjoint pairings. |
| `finiteSector_weak_gradient_lift_graph` | Every projected pair `(IₛIₛ*F,JₛJₛ*G)` lies in `graph(D)` by the previously verified finite-dimensional Hermite graph theorem. No convergence is asserted. |
| `finiteScalarProjection_fix`, `finiteScalarProjection_norm_le`, `exists_finiteScalarProjection_approx` | `IₛIₛ*` fixes the finite scalar sector, is contractive, and its finite-sector choices approximate every scalar Gaussian `L²` class in norm. This uses proved polynomial density and the Hilbert adjoint of the isometric pullback. |

These statements apply to all finite `s`, including the empty set. They do not
replace the maximal finite vector divergence condition by componentwise
Sobolev bounds; the previous finite graph theorem still uses the combined
Hermite coefficients and permits cancellation.

The exact missing step is **joint finite-sector projection convergence** on
the graph of `δ₀*` (equivalently, an appropriate conditional-expectation
commutation theorem): find finite sets `sₙ` such that both

    Iₛₙ Iₛₙ* F → F          in scalar L²,
    Jₛₙ Jₛₙ* G → G          in vector L²

for each `(F,G) ∈ graph(δ₀*)`. The scalar approximation above is existential
and does not by itself give a common sequence with the vector approximation.
The vector lift has not yet been proved isometric or its adjoint compositions
identified with finite-coordinate conditional expectation and direction
projection. The joint density of its ranges, proved here, is strictly weaker
than convergence of `JₛJₛ*`. With this additional noncircular projection result,
closedness of `D` and `finiteSector_weak_gradient_lift_graph` would yield
`δ₀* ≤ D`; the reverse inclusion and existing bidual theorem would then give
both desired identities. No theorem in this milestone assumes that convergence.

Mathlib already supplies bounded Hilbert adjoints, `condExpL2`, Gaussian
product measures, and the `L²` infrastructure. Public `gaussian-hilbert`
contains finite Hermite completeness, while `lean-malliavin` has a closed
Gaussian Banach-space Malliavin derivative and simple-field divergence. Their
interfaces do not directly supply this project's finite-lift projection
compatibility, so no new dependency was introduced. The inspected sources are
`https://github.com/mrdouglasny/gaussian-hilbert/blob/4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e/GaussianHilbert/HermitePolynomials.lean`
and `https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean`.

The complete `lake build` passes (3358 jobs), and the separately built
`Foundation.AxiomAudit` has 688 queries and 688 results. Every new declaration
depends only on some subset of `propext`, `Classical.choice`, and `Quot.sound`;
none depends on `sorryAx` or a custom axiom. The source scan found no
`axiom`, `sorry`, or `admit` declaration. The audit transcript is kept in the
ignored file `.lake/build/infinite-gaussian-coordinate-fields-axioms.log`.

### Complete divergence graph core on the countable Gaussian product

`Foundation/InfiniteGaussianProjectionConvergence.lean` resolves the projection
obligation left above. The theorem applies to the established countable product
of independent standard real Gaussians, with ambient fiber `ℓ²(ℕ)` and genuine
polynomial-cylinder operators. It does not introduce a componentwise
Sobolev-domain condition or assume graph density.

The finite fiber map sends `x ∈ ℝˢ` to `Σᵢ∈s xᵢ eᵢ ∈ ℓ²(ℕ)`.
`finiteFiberMap_orthonormal` and `finiteFiberIsometry` verify that this is an
isometry, including for `s = ∅`. Its pointwise `L²` lift and the
measure-preserving finite Gaussian projection give `finiteVectorIsometry`.
`finiteVectorPullback_eq_isometry` proves that this is **the previously defined
vector lift** `Jₛ`, so `JₛJₛ*` is a contractive orthogonal projection, not a
new, independently prescribed approximation.

`finiteVectorProjection_fix_coordinate_of_subset` proves that a field
`p(ω|ₛ)eₙ` is fixed whenever the finite sector contains `s ∪ {n}`. Span
induction gives `finiteVectorProjection_eventually_fix_core`; the verified
ambient density of these polynomial fields and uniform projection contraction
give `finiteVectorProjection_range_tendsto`:

    J_[0,N) J_[0,N)* G → G  in L²(Ω;ℓ²), for every G.

The parallel result `finiteScalarProjection_range_tendsto` gives
`I_[0,N) I_[0,N)* F → F` for every scalar `L²` class. Thus
`finiteSector_projections_range_tendsto` is a **simultaneous** limit along the
same increasing sets. For a pair `(F,G) ∈ graph(δ₀*)`, the previously proved
finite-dimensional Hermite weak-gradient bridge places every projected pair
in `graph(D)` (`finiteSector_weak_gradient_range_graph`). Closedness of `D`
then proves `cylindricalDivergence_adjoint_le_closedDerivative`. Combining the
earlier reverse inclusion and bidual equivalence yields the exact identities

    δ₀* = D,
    closure(δ₀) = δ = D*.

The Lean declarations are `cylindricalDivergence_adjoint_eq_closedDerivative`
and `closedPolynomialDivergence_eq_hilbertDivergence`. The latter is a genuine
graph-core assertion: `hilbertDivergence_polynomial_graph_core_sequence`
constructs, for each `(u,g) ∈ graph(δ)`, a sequence in the actual polynomial
divergence domain whose field and divergence converge jointly to `(u,g)`.
The finite-dimensional spectral theorem used in the weak-gradient lift retains
the **combined** divergence coefficients `b_β`; it does not require
componentwise weighted summability. The proof does not infer graph convergence
from ambient `L²` density alone: isometric projection convergence and closedness
are the additional steps.

No unresolved analytic obligation remains for the polynomial divergence graph
core on this countable standard Gaussian product. Extensions to a general
Gaussian probability space or an arbitrary nonseparable isonormal index space
require separate transfer/density arguments. This milestone does not assert an
Itô formula or stochastic integration theory.

Verification for this milestone: the full `lake build` and
`lake build Foundation.AxiomAudit` pass. The audit contains 714 `#print axioms`
queries with 714 results. Each new declaration depends only on a subset of
`propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx` or a custom
axiom. The source scan finds no `axiom`, `sorry`, or `admit` declaration. The
audit transcript is in the ignored file
`.lake/build/infinite-gaussian-projection-axioms.log`.

## Gaussian entropy M1: finite square entropy from L4 (2026-10-11)

Implemented `Foundation/GaussianEntropy.lean`, following M1 of
`BAKRY_EMERY_REPLACEMENT_PLAN.md`. The module defines, for real functions,

    entropySq μ f = ∫ f² log(f²) dμ − (∫ f² dμ) log(∫ f² dμ).

The definition uses Mathlib's `0 * log 0 = 0` convention. As with any real
Bochner integral, the definition alone does not assert finiteness. The new
integrability theorem supplies that analytic justification.

The three required, Lean-verified statements are:

- `OperatorDerivativeRewrite.Foundation.integrable_sq_mul_log_of_memLp_four`:
  for any measurable space, finite measure μ, and real function f with
  `MemLp f 4 μ`, the function `ω ↦ (f ω)^2 * Real.log ((f ω)^2)` is integrable.
- `OperatorDerivativeRewrite.Foundation.entropySq_nonneg_of_memLp_four`:
  for a probability measure μ and `MemLp f 4 μ`, `0 ≤ entropySq μ f`.
- `OperatorDerivativeRewrite.Foundation.GaussianCore.polynomial_sq_mul_log_integrable`:
  for every real polynomial p, `x ↦ (p.eval x)^2 * Real.log ((p.eval x)^2)`
  is integrable under the existing standard Gaussian measure `GaussianCore.γ`.

No entropy-integrability assumption or positivity assumption on f is added.
The proofs also apply to functions vanishing on positive-measure sets and to
the zero polynomial.

The integrability proof uses Mathlib's nonnegative
`InformationTheory.klFun r = r * Real.log r + 1 - r`.
The new `klFun_le_one_add_sq` proves `klFun r ≤ 1 + r²` for r ≥ 0, with a
separate zero case and the genuine estimate `log r ≤ r - 1` for positive r.
Existing Hölder (`mul_L4_memLp_two`) gives f² in L² and hence f⁴ integrable;
finite-measure exponent comparison gives f² integrable. These facts provide
an integrable majorant for `klFun (f²)`. Subtracting 1 and adding f² proves
integrability of f² log(f²). Jensen's theorem `ConvexOn.map_integral_le`,
using `Real.convexOn_mul_log`, then proves nonnegative square entropy.

Supporting declarations are `entropySq_congr` (a.e. invariance),
`entropySq_zero` (zero entropy for zero under any measure), and
`entropySq_const` (zero entropy for every constant on a probability space).
Together with the definition, the majorant, and the three required results,
all eight declarations are queried in `Foundation/AxiomAudit.lean`.
The module is imported by `OperatorDerivativeRewrite.lean`.

Verification: targeted Lean checking of the new module passed with no errors
or warnings. The complete `lake build` passed (3372 jobs). Fresh execution of
`lake env lean Foundation/AxiomAudit.lean` passed with 722 reports covering
721 distinct declarations. Each of the eight new declarations reports exactly
`{propext, Classical.choice, Quot.sound}`; the complete audit has the same
union. There is no `sorryAx`, custom axiom, or unchecked proof step.
Elaborated `#check @...` statements confirm the hypotheses recorded above.

M1 is complete. This milestone does not establish log-Sobolev, Fisher decay,
a semigroup, or finiteness for every L² function. The original Gaussian
log-Sobolev axiom has not been replaced. Later milestones in the plan remain
open. No external dependency, original manuscript change, or alteration of
an existing theorem statement is part of this milestone.

## Gaussian Mehler M2a: concrete one-dimensional OU kernels (2026-10-11)

Starting verified commit: `62546acb0d3f81a49d5b09613b32e1fcf39f6bf6`.
Implemented `Foundation/GaussianMehler.lean`, namespace
`OperatorDerivativeRewrite.Foundation.GaussianMehler`.

### Scope and exact statements

The measure `γ` is the existing `GaussianCore.γ = gaussianReal 0 1`,
with variance one. The actual definition is

```lean
mehler (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :=
  ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ
```

The useful analytic class is specified by `hf : Continuous f` and a real
bound `hM : ∀ z, ‖f z‖ ≤ M`. No smoothness or prescribed derivative is
required. A second function g has the analogous continuity and bound
hypotheses where needed. The mathematical statements of the declarations are:

- `one_sub_exp_nonneg (t) (ht : 0 ≤ t)`: `0 ≤ 1 - exp(-2*t)`.
- `integrable_comp_of_bounded`: for any finite measure μ, measurable real
  f bounded in norm, and measurable g into ℝ, `f ∘ g` is μ-integrable.
  This is an integrability conclusion, not an assumed integrability field.
- `kernel_integrable hf hM t x`: the actual Mehler integrand is γ-integrable.
- `mehler_zero (f)`: `mehler 0 f = f`. No regularity is needed here:
  at zero time the integrand is genuinely constant in y.
- `mehler_const (t c)`: `mehler t (fun _ => c) = fun _ => c`.
- `mehler_mono hf hg hM hN hfg t x`: from `∀ z, f z ≤ g z`,
  `mehler t f x ≤ mehler t g x`, with both integrands proved integrable.
- `mehler_nonneg hf hM hpos t x`: from `∀ z, 0 ≤ f z`,
  `0 ≤ mehler t f x`.
- `mehler_pos hf hM hpos t x`: from `∀ z, 0 < f z`,
  `0 < mehler t f x`; full support of the positive integrand and γ(ℝ)=1
  give strict positivity. There is no assumed uniform positive lower bound.
- `mehler_norm_le hM t x`: `‖mehler t f x‖ ≤ M`.
- `mehler_continuous hf hM t`: `Continuous (mehler t f)`.
- `mehler_integrable hf hM t`: `Integrable (mehler t f) γ`.
- `gaussian_combination_map (a b)`: the map `(x,y) ↦ a*x+b*y` sends
  γ×γ to `gaussianReal 0 (a²+b²)`, with nonnegative variance represented
  explicitly in ℝ≥0. This includes degenerate choices of a and b.
- `kernel_map (t) (ht : 0 ≤ t)`: the Mehler mixing map sends γ×γ to γ.
- `integral_mehler hf hM t ht`: `∫ x, mehler t f x ∂γ = ∫ x, f x ∂γ`.
- `mehler_compose s t hs ht hf hM`: for `0 ≤ s` and `0 ≤ t`,
  `mehler (s+t) f = mehler s (mehler t f)` as functions on ℝ.
- `mehler_tendsto_mean hf hM x`:
  `Tendsto (fun t => mehler t f x) atTop (𝓝 (∫ y, f y ∂γ))`.

The normalization is exp(-t), variance `1-exp(-2*t)`, and invariant standard
Gaussian variance one. Composition and invariance explicitly require
nonnegative times. Some elementary boundedness/continuity statements are
valid for every real time, but no negative-time OU semigroup is asserted.

### Proof dependencies and source compatibility

The pinned upstream implementation was inspected before the port:
[markov-semigroups, Euclidean.lean at acf6491](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/Instances/WorkInProgress/Euclidean.lean).
Its concrete namespace is `Gaussian1D` (rather than a standalone Gaussian1D
file). Reused source arguments are `ouSemigroup`, `ou_kernel_map`,
`ouSemigroup_compose`, value boundedness, and the pointwise dominated
convergence step inside `ouSemigroup_ergodic`. The upstream `IsCore` smoothness
conditions are not used: these particular arguments need only bounded
continuity. The composition proof is a source-level port with attribution.
The file retains Michael R. Douglas's copyright notice; the applicable Apache
2.0 license is included at `LICENSES/Apache-2.0.txt`.

Upstream pins Lean v4.30.0. The port is verified against our unchanged
Lean v4.34.1 and Mathlib lock
`d13f23b723b8a846827a245b89c10fc7d3f11612`. A concrete API migration was needed:
`gaussianReal_add_gaussianReal_of_indepFun` now takes `HasLaw` arguments,
where the pinned upstream proof passed their `.map_eq` equalities. Variance
constructor coercions were checked explicitly. No upstream abstract
semigroup classes, axioms, package dependencies, or derivative results are
imported. This verifies the local port, not the whole upstream repository.

Mathlib supplies `gaussianReal_const_mul`,
`gaussianReal_add_gaussianReal_of_indepFun`, `indepFun_prod`, `integral_map`,
`integral_prod`, bounded integral estimates, and
`tendsto_integral_filter_of_dominated_convergence`.
Constant domination proves each kernel and product integrand integrable.
Invariance follows from the Gaussian mixing law and Fubini. Composition
compares the laws of `exp(-t)*sqrt(1-exp(-2*s))*Y + sqrt(1-exp(-2*t))*Z`
and `sqrt(1-exp(-2*(s+t)))*Y`; their variances coincide. Continuity and the
pointwise limit follow from dominated convergence with majorant M.

### Verification and remaining obligations

All seven requested M2a targets are established on the stated bounded
continuous class. All 18 declarations in this module, including the measure
abbreviation and kernel definition, have transitive `#print axioms` queries
in `Foundation/AxiomAudit.lean`. The root module imports the new module.
Final verification: the complete `lake build` passed (3373 jobs), with no
warnings from the new module. The pre-existing `Foundation.Adjoint` unused
section-variable warnings remain. Fresh `lake env lean Foundation/AxiomAudit.lean`
passed with 740 reports for 739 distinct declarations. Every new declaration
reports exactly `{propext, Classical.choice, Quot.sound}`; the complete audit
has the same union, with no `sorryAx` or custom axiom. Fresh elaborated
`#check @...` queries for all 18 declarations also passed. The ignored
transcripts are `.lake/build/gaussian-mehler-axioms.log` and
`.lake/build/gaussian-mehler-statements.log`. A source scan found no axioms,
`unsafe`, `sorry`, or `admit` in the new module. Original source SHA256 hashes
match the previous milestone, and the dependency configuration and lockfile
have no diff.

M2a does not assert an L²-class extension or strong continuity in L².
M2b (actual spatial differentiation and weighted Fisher-information decay),
M3 (entropy dissipation), and M4 (Gaussian log-Sobolev) remain unimplemented.
The legacy log-Sobolev axiom is not discharged by these kernel properties.
No assertion of a general abstract curvature-dimension theorem follows.
The original manuscripts, existing theorem statements, dependency lockfile,
and the two pre-existing untracked audit/plan documents are preserved.

## Gaussian Fisher M2b: derivative commutation and Fisher decay (2026-10-11)

Starting verified commit: `db6768796c01935bfee26bc1bc0288f30069a127`.
Implemented by Sol Medium and reviewed against the mathematical targets.
The new file is `Foundation/GaussianFisherDecay.lean`, namespace
`OperatorDerivativeRewrite.Foundation.GaussianFisher`. It imports and uses
M2a's existing `GaussianMehler.mehler`; there is no new semigroup definition.
The measure abbreviation remains the existing standard Gaussian γ = N(0,1).

### Definition and exact hypotheses

```lean
def fisherInformation (g : ℝ → ℝ) : ℝ :=
  ∫ y, (deriv g y) ^ 2 / g y ∂γ
```

This is Fisher information, rather than the legacy `gaussian_fisher` Dirichlet
energy. `deriv g` is the actual Mathlib derivative. The definition alone makes
no assertion of integrability or positivity for arbitrary g. The new theorems
prove those analytic obligations on their stated class.

The full decay theorem has exactly these hypotheses:

```lean
theorem fisherInformation_decay
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    fisherInformation (GaussianMehler.mehler t g) ≤
      Real.exp (-2 * t) * fisherInformation g
```

No C² or C∞ hypothesis, normalization `∫g=1`, entropy integrability,
commutation identity, Fisher inequality, or arbitrary derivative candidate
is assumed. `M ≥ 0` and positivity of g are derived from the stated bounds.

### Completed declarations

- `hasDerivAt_mehler_C1`: for `ContDiff ℝ 1 f`, uniform bounds
  `∀ x, ‖f x‖ ≤ M` and `∀ x, ‖deriv f x‖ ≤ M`, and any real t and x₀,
  `HasDerivAt (mehler t f) (exp(-t) * mehler t (deriv f) x₀) x₀`.
  This is a genuine differentiation theorem for the existing integral.
- `deriv_mehler_C1`: under those same hypotheses,
  `deriv (mehler t g) x = exp(-t) * mehler t (deriv g) x`.
- `mehler_lower_bound`: if g is continuous and uniformly bounded in norm,
  `0 < ε`, and `∀ x, ε ≤ g x`, then `ε ≤ mehler t g x` for every real t,x.
  In particular all subsequent Mehler denominators are strictly positive.
- `fisherInformation_integrable`: for measurable g and measurable `deriv g`,
  `0 < ε`, `∀ x, ε ≤ g x`, and `∀ x, |deriv g x| ≤ M`,
  `Integrable (fun x => (deriv g x)^2 / g x) γ`. No upper bound on g is
  needed for this supporting integrability result. The measurability facts
  are derived from C¹ regularity when used in the final theorem.
- `weighted_cauchy_schwarz_mehler`: under precisely the full decay theorem's
  g,ε,M hypotheses, for t ≥ 0 and every x,
  `(mehler t (deriv g) x)^2 / mehler t g x ≤
   mehler t (fun y => (deriv g y)^2 / g y) x`.
- `fisherInformation_mehler_integrable`: under those same hypotheses and
  t ≥ 0, the function `x ↦ (deriv (mehler t g) x)^2 / mehler t g x`
  is γ-integrable. This is proved before applying integral monotonicity.
- `fisherInformation_decay`: the displayed full theorem.

The two other declarations are the abbreviation γ and the supporting
`cauchy_schwarz_gamma` helper. This helper assumes actual integrability of
AB, A², and B² and proves `(∫AB)^2 ≤ (∫A²)(∫B²)` by expanding the
nonnegative square `(A-λB)^2`. The zero second-moment case is treated
separately; in the other case its denominator is proved positive.

### Genuine analysis and proof dependencies

Differentiation uses Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The spatial integrand
`g(exp(-t)*x + sqrt(1-exp(-2*t))*y)` has its derivative proved by the
ordinary chain rule. The derivative integrand is dominated by the integrable
constant `|exp(-t)|*M`. Continuity and measurability are consequences of
`ContDiff ℝ 1 g`, not additional assumptions about the desired integral.

The pointwise bound `0 ≤ (deriv g)^2/g ≤ M²/ε` supplies a genuine integrable
majorant. In weighted Cauchy–Schwarz, A is the composed `deriv g / sqrt(g)`
and B is the composed `sqrt(g)`. Every square-root denominator is positive;
AB, A², and B² are proved measurable and integrable before the inequality.
Preservation of ε gives the positive denominator `mehler t g x` when dividing
the resulting inequality. These are kernel averages against the actual γ.

For the evolution's Fisher integrand, derivative commutation and M2a
boundedness give `|deriv (mehler t g)| ≤ M` when t ≥ 0. M2a continuity
applied to g and `deriv g` also gives measurability of the evolved derivative
via the proved derivative formula. The input integrability result then
applies to the evolution.

The final proof integrates the pointwise estimate, with explicit input,
evolved, and Mehler-Fisher integrability. M2a's `integral_mehler` is applied
to the continuous bounded function `(deriv g)^2/g`; invariance is reused,
rather than assumed or independently repackaged as a structure field.
Finally `(exp(-t))² = exp(-2*t)` yields the exact rate. All theorems include
zero time; no division by a positive-time smoothing coefficient is used.

Source-level ports retain attribution to Michael R. Douglas and contributors,
Apache 2.0, at commit `acf649108ea2222f4a8544a2782f448cb502492a`:

- [Euclidean.lean: hasDerivAt_ouSemigroup_C1](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/Instances/WorkInProgress/Euclidean.lean#L505).
- [OUEntropyDecomposition.lean: Cauchy–Schwarz and Fisher decay](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/General/OUEntropyDecomposition.lean#L84).

The latter's historical comments call results axioms, but the inspected
pinned declarations have proof bodies. Only the concrete M2b proof slice is
ported; no abstract semigroup or entropy-dissipation infrastructure is
imported. The local port is checked against Lean/Mathlib v4.34.1 and the
unchanged dependency lock. Existing `LICENSES/Apache-2.0.txt` applies.

### Verification and scope boundary

The new module is imported by the root project and `Foundation/AxiomAudit.lean`.
All ten new declarations, including the supporting Cauchy–Schwarz helper, have
explicit transitive axiom queries. Final verification: the complete `lake build`
passed (3374 jobs), with no warnings from the new module. The pre-existing
`Foundation.Adjoint` unused section-variable warnings remain. Fresh
`lake env lean Foundation/AxiomAudit.lean` passed: 750 reports for 749 distinct
declarations. Each of the ten new declarations reports exactly
`{propext, Classical.choice, Quot.sound}`; this is also the complete audit's
union. There is no `sorryAx` or custom axiom. Exact elaborated `#check @...`
queries for all ten declarations passed. The ignored transcripts are
`.lake/build/gaussian-fisher-axioms.log` and
`.lake/build/gaussian-fisher-statements.log`. A source scan finds no `axiom`,
`unsafe`, `sorry`, or `admit` in the new module. The original manuscript hashes
match the previous milestone, and there is no dependency or lockfile diff.

M2b's five targets are complete on the exact stated C¹, bounded, uniformly
positive class. There is no remaining M2b mathematical or Lean obstruction.
M3 entropy dissipation and M4 log-Sobolev have not been started. In particular,
this milestone does not replace the original Gaussian log-Sobolev axiom,
prove abstract curvature-dimension theory, or extend Fisher decay to an
unproved maximal Sobolev domain. Original manuscripts and previous verified
statements are preserved, as are the pre-existing untracked plan and graph
core audit documents.

## M3 prerequisite milestone: finite centered entropy, continuity, and ergodic limit

Starting point: `fb89674635246eac1a316f6ec3b82381a24ff317`.
New module: `Foundation/GaussianEntropyDissipation.lean`.
**This is an independently verified subset of M3. The entropy-dissipation
identity is not yet proved.** No M4 development is included.

### Definitions and exact normalization

Namespace: `OperatorDerivativeRewrite.Foundation.GaussianEntropyDissipation`.
`γ` is the existing standard real Gaussian probability measure, with no new
measure or semigroup definition. Put

```
entropyDensity g = integral (g * log g) dγ
                   - (integral g dγ) * log (integral g dγ)
entropyTrajectory g t = entropyDensity (GaussianMehler.mehler t g)
```

This is centered density entropy, not entropy of the square of the evolved
input. `entropyDensity_eq_entropySq_sqrt` proves exactly
`entropyDensity g = entropySq γ (fun x => Real.sqrt (g x))` under
`∀ x, 0 ≤ g x`. Both definitions are real-valued functionals; only the
integrability theorems below license their interpretation as finite entropy.
Signed bounded inputs also have finite values for the real `r log r`
functional, but the entropy interpretation and Jensen nonnegativity are
asserted only for nonnegative inputs. `Real.log 0 = 0` and continuity of
`r * Real.log r` handle zero, without introducing a positive lower bound.

### Exact verified theorem statements

In this table `P t g` denotes the existing `GaussianMehler.mehler t g`.
All bounds are pointwise; `M` is an arbitrary real bound, not an additional
regularity predicate. There are no derivative candidates or assumed
entropy integrability hypotheses.

| Theorem | Hypotheses | Conclusion |
|---|---|---|
| `entropyDensity_eq_entropySq_sqrt` | `∀ x, 0 ≤ g x` | `entropyDensity g = entropySq γ (fun x => Real.sqrt (g x))` |
| `exists_mul_log_bound` | any `M : ℝ` | `∃ B : ℝ, ∀ r : ℝ, ‖r‖ ≤ M → ‖r * Real.log r‖ ≤ B` |
| `entropyDensity_integrable` | `Measurable g`, `∀ x, ‖g x‖ ≤ M` | `Integrable g γ ∧ Integrable (fun x => g x * Real.log (g x)) γ` |
| `entropyDensity_nonneg` | preceding measurable bound and `∀ x, 0 ≤ g x` | `0 ≤ entropyDensity g` |
| `mehler_time_continuous` | `Continuous g`, `∀ x, ‖g x‖ ≤ M`, any `x : ℝ` | `Continuous (fun t => P t g x)` |
| `entropyTrajectory_integrable` | same continuous bound, any `t : ℝ` | `Integrable (P t g) γ ∧ Integrable (fun x => P t g x * Real.log (P t g x)) γ` |
| `entropyTrajectory_nonneg` | same continuous bound, `∀ x, 0 ≤ g x`, any `t : ℝ` | `0 ≤ entropyTrajectory g t` |
| `entropyTrajectory_continuous` | same continuous bound | `Continuous (entropyTrajectory g)` |
| `entropyTrajectory_zero` | any `g : ℝ → ℝ` | `entropyTrajectory g 0 = entropyDensity g` |
| `entropyTrajectory_tendsto_zero_time` | same continuous bound | `Tendsto (entropyTrajectory g) (𝓝 0) (𝓝 (entropyDensity g))` |
| `entropyTrajectory_eq_invariant_mean` | same continuous bound, `0 ≤ t` | `entropyTrajectory g t = (∫ x, P t g x * Real.log (P t g x) ∂γ) - (∫ x, g x ∂γ) * Real.log (∫ x, g x ∂γ)` |
| `entropyTrajectory_tendsto_atTop` | same continuous bound | `Tendsto (entropyTrajectory g) atTop (𝓝 0)` |

The Mehler formula has a real-time extension using the total real square
root. Continuity is proved for that formula on all real times, including
zero; the semigroup interpretation and mean invariance remain restricted
to nonnegative times. The full neighborhood limit at zero implies the
required right-hand limit. No time differentiability at zero is claimed.
For the intended class `ContDiff ℝ 1 g`, `0 < ε`, `ε ≤ g x ≤ M`,
`|deriv g x| ≤ M`, every continuous bounded/nonnegative hypothesis above
follows from the stated bounds. These results actually need less regularity
than dissipation and do not silently strengthen that eventual theorem.

### Proof dependencies and upstream inspection

The proofs use Mathlib `Real.continuous_mul_log`, compactness of `Icc`,
`Integrable.mono'`, `Real.convexOn_mul_log.map_integral_le`,
`continuous_of_dominated`, and
`tendsto_integral_filter_of_dominated_convergence`. The compact image of
`[-M,M]` supplies an actual constant dominator for `r log r`. The density
itself is dominated by `M`. Both dominators are integrable under the Gaussian
probability measure. Kernel continuity and these dominators prove continuity
of both spatial integrals. M2a pointwise convergence to the mean, followed by
outer dominated convergence for both integrals, proves their centered
cancellation at infinity. Mean invariance is reused only with its original
nonnegative-time restriction. Jensen is applied only after proving both
integrals finite.

M2b is imported and its actual derivative/Fisher infrastructure is preserved,
but Fisher decay and log-Sobolev are not used to prove the entropy limit.
Neither polynomial integration by parts nor finite-dimensional operator
closure is misapplied to evolving nonpolynomial logarithms.

Inspected concrete pinned sources, commit
`acf649108ea2222f4a8544a2782f448cb502492a`:

- [Euclidean.lean, Gaussian1D.ouSemigroup_entropy_sq_ergodic, line 1209](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/Instances/WorkInProgress/Euclidean.lean#L1209).
  Its compact-bound/outer-DCT argument is adapted here for a bounded density
  directly, without assuming it is the square of an upstream `IsCore` function.
- [OUEntropyDecomposition.lean, hasDerivAt_entropy_ouSemigroup, line 607](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/General/OUEntropyDecomposition.lean#L607).
  Its approximately 1000-line concrete proof includes positive-time
  smoothing, inner time differentiation, outer entropy differentiation,
  and a bilinear Dirichlet step. Historical partial-proof comments are
  not evidence that the current declaration is an axiom; the actual proof
  body was inspected. This theorem has not been ported or asserted locally.
- [EuclideanStein.lean, stein_identity_standard, line 165](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/Instances/WorkInProgress/EuclideanStein.lean#L165),
  `hasDerivAt_t_ouSemigroup` at line 291, and
  `gaussian_dirichlet_form_bilinear` at line 703 were inspected as remaining
  narrow reusable proof infrastructure. None is imported as an assumption.

Attribution to Michael R. Douglas and contributors and the Apache-2.0 license
reference are preserved in the new module. Existing `LICENSES/Apache-2.0.txt`
applies. No external dependency or dependency pin is changed.

### Exact remaining M3 obligations

There is no identified mathematical counterexample for the planned positive
bounded C¹ class. The following analytic proofs, however, are still absent
from the local Lean development; the verified limits above do not imply them:

1. Nonpolynomial Gaussian Stein integration by parts with explicit
   integrability/boundary control. The first recommended next theorem is,
   for `ContDiff ℝ 1 v`, `∀ x, |v x| ≤ A`, and
   `∀ x, |deriv v x| ≤ B`,
   `∫ x, x * v x ∂γ = ∫ x, deriv v x ∂γ`.
   Prove integrability of both sides and Gaussian-weighted boundary limits,
   then derive it from the actual PDF derivative. Reuse the concrete upstream
   `stein_identity_standard` proof, without its abstract framework.
2. Positive-time spatial C² regularity of `P t g` from bounded C¹ input and
   bounded actual first derivative, including second-derivative bounds on
   compact positive-time intervals. Do not require a supplied unrelated
   second-derivative function or silently strengthen g to C².
3. Actual kernel time differentiation for `t > 0`. On a neighborhood bounded
   away from zero, prove the inner dominator involving `1 + |x| + |y|`, and
   derive `∂t P t g = deriv (deriv (P t g)) - x * deriv (P t g)`.
   The singular derivative of the square-root coefficient cannot be bounded
   uniformly down to zero by this argument.
4. Outer differentiation of entropy, dominated locally in positive time.
   Use the already verified `ε ≤ P t g ≤ M`, so logarithms/reciprocals have
   justified positive denominators. Establish genuine integrability of
   `(∂t P t g) * (1 + log (P t g))`, not just an equality of totalized integrals.
5. Gaussian bilinear IBP with `1 + log (P t g)` gives the negative of
   `∫ (deriv (P t g))² / (P t g) dγ`. With mean invariance, conclude precisely
   `HasDerivAt (entropyTrajectory g)
       (-GaussianFisher.fisherInformation (GaussianMehler.mehler t g)) t`
   under the original positive bounded C¹ hypotheses and `0 < t`.

The above next Stein theorem is a prerequisite, not a replacement statement
for dissipation. The strongest completed claim in this commit is the finite,
continuous, ergodically vanishing centered entropy trajectory. Its domination
lemmas justify the integrals and their continuity/limits, **not differentiation
under either integral**. No entropy decay rate, monotonicity, entropy
production equality, or Gaussian log-Sobolev inequality is claimed here.
A right derivative at zero is a further optional obligation; continuity at
zero, needed for the planned later limit argument, is already verified.

### Verification

Complete `lake build` passed: 3375 jobs. The new module has no warnings;
pre-existing unused section-variable warnings in `Foundation.Adjoint` remain.
`lake env lean Foundation/AxiomAudit.lean` passed: 765 reports for 764 distinct
declarations. All 15 new declarations (three definitions/abbreviations and
12 theorems), and the complete audit's union, depend only on
`propext`, `Classical.choice`, and `Quot.sound`. There is no `sorryAx` or
custom mathematical axiom. Exact `#check @...` queries for all new declarations
passed. A source scan finds no `axiom`, `unsafe`, `sorry`, or `admit` in the
new module. Ignored verification transcripts:

- `.lake/build/gaussian-entropy-trajectory-build.log`
- `.lake/build/gaussian-entropy-trajectory-axioms.log`
- `.lake/build/gaussian-entropy-trajectory-statements.log`

Original Lean and TeX manuscript hashes match the previous verified milestone.
The toolchain, dependency lockfile, and previous theorem statements are
unchanged. The pre-existing untracked replacement plan and independent
operator audit remain preserved and are not included in this commit.
## Bounded C¹ Gaussian Stein identity: completed M3 integration-by-parts prerequisite

Starting commit: `c1dad1d0d549dc3c770dc5ec451b4c5f33295480`.
New module: `Foundation/GaussianSteinBounded.lean`.
Namespace: `OperatorDerivativeRewrite.Foundation.GaussianSteinBounded`.
The measure is the existing `GaussianCore.γ = gaussianReal 0 1`; the module
introduces no new Gaussian measure, operator, semigroup, or derivative data.

### Exact verified identity and hypotheses

```lean
theorem stein_identity {h : ℝ → ℝ} (hc : ContDiff ℝ 1 h)
    {A B : ℝ} (hb : ∀ x, |h x| ≤ A)
    (hdb : ∀ x, |deriv h x| ≤ B) :
    (∫ x, deriv h x ∂GaussianCore.γ) =
      ∫ x, x * h x ∂GaussianCore.γ
```

The derivative is Mathlib's actual `deriv h`. `ContDiff ℝ 1 h` gives
continuous differentiability, including continuity/measurability of the
actual derivative. The two uniform bounds can be different. No positivity,
positive lower bound, compact support, second derivative, entropy assumption,
Stein assumption, approximation hypothesis, or semigroup field is used.
Neither bound constant needs a separately supplied nonnegativity proof:
the corresponding pointwise bound already implies nonnegativity by evaluation
at zero. There are no additional implicit analytic assumptions.

### Supporting theorem statements

Write `γ = GaussianCore.γ` and `ρ x = gaussianPDFReal 0 1 x` below. Bare
`Integrable` in the weighted statements is with respect to Lebesgue volume.

| Theorem | Hypotheses | Exact conclusion |
|---|---|---|
| `integrable_of_bounded` | `Measurable h`, `∀ x, |h x| ≤ A` | `Integrable h γ` |
| `integrable_coordinate_mul_of_bounded` | same measurable bound | `Integrable (fun x => x * h x) γ` |
| `stein_integrable` | the main theorem's C¹ and two bounds | `Integrable h γ ∧ Integrable (deriv h) γ ∧ Integrable (fun x => x * h x) γ` |
| `density_products_integrable` | the main theorem's hypotheses | `Integrable (fun x => h x * ρ x) ∧ Integrable (fun x => deriv h x * ρ x) ∧ Integrable (fun x => h x * (-x * ρ x))` |
| `density_product_hasDerivAt` | `ContDiff ℝ 1 h`, any `x : ℝ` | `HasDerivAt (fun y => h y * ρ y) (deriv h x * ρ x + h x * (-x * ρ x)) x` |
| `density_product_tendsto_zero` | the main theorem's hypotheses | `Tendsto (fun x => h x * ρ x) atBot (𝓝 0) ∧ Tendsto (fun x => h x * ρ x) atTop (𝓝 0)` |

Thus every Gaussian integral in the identity is separately proved integrable;
the identity is not an equality produced merely by totalizing nonintegrable
real integrals. The intermediate Lebesgue integrals are also proved integrable.
Both boundary terms are proved to vanish; no tail limit is an assumption.

### Proof architecture and reuse

1. Bounded measurable functions are integrable under the Gaussian probability
   measure by `Integrable.mono'` and the integrable constant bound.
2. Mathlib `ProbabilityTheory.memLp_id_gaussianReal` at exponent one yields
   Gaussian integrability of the coordinate. Its absolute value times A
   dominates `|x * h x|`, giving coordinate-product integrability.
3. Existing local `GaussianCore.integrable_density_mul` transfers each
   Gaussian integrability result to integration against the real PDF under
   Lebesgue measure. Algebraic rearrangement gives both product-rule terms.
4. Existing local `GaussianCore.density_hasDerivAt` proves the actual density
   derivative `ρ' x = -x * ρ x`; Mathlib's actual product rule supplies the
   derivative of `h * ρ`. The sum of the two integrable pieces is integrable.
5. Mathlib `tendsto_zero_of_hasDerivAt_of_integrableOn_Iic` and
   `tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` establish zero limits at
   the two infinities from the genuine derivative and weighted-function
   integrability. These theorems prove the boundary estimates internally;
   they are not boundary conditions imposed on h.
6. `integral_mul_deriv_eq_deriv_mul` gives whole-line integration by parts
   with those verified limits and integrable terms. Conversion via
   `integral_gaussianReal_eq_integral_smul` then gives Stein's identity with
   the exact sign and standard variance-one normalization.

The proof generalizes the existing local polynomial proof's infrastructure,
without using polynomial approximation. It has no approximation or derivative
convergence gap.

Inspected the concrete pinned upstream source:
[EuclideanStein.lean, Gaussian1D.stein_identity_standard, line 165](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/Instances/WorkInProgress/EuclideanStein.lean#L165),
commit `acf649108ea2222f4a8544a2782f448cb502492a`. Its PDF derivative, PDF tail
limits, weighted integrability helpers, and Stein proof were read. The local
proof reuses the already verified density derivative and Mathlib boundary
infrastructure instead of duplicating its exponential-tail lemmas and its
whole-line FTC assembly. The upstream uses one shared bound M; the local
theorem permits separate A and B. Attribution to Michael R. Douglas and
contributors and the Apache-2.0 notice are retained in the new module;
`LICENSES/Apache-2.0.txt` remains applicable. No upstream abstract framework
or new dependency is introduced.

### Verification and remaining M3 obligations

The module is added to the root project imports and `Foundation/AxiomAudit.lean`.
Complete `lake build` passes (3376 jobs); the new module has no warnings.
Pre-existing unused section-variable warnings in `Foundation.Adjoint` remain.
The transitive axiom audit passes: 772 reports for 771 distinct declarations.
Every one of the seven new theorems, and the complete audit's union, uses only
`propext`, `Classical.choice`, and `Quot.sound`. There is no `sorryAx` or custom
mathematical axiom. Exact elaborated `#check @...` checks for all seven new
theorems pass. A source scan finds no `axiom`, `unsafe`, `sorry`, or `admit` in
the new module. Ignored transcripts:

- `.lake/build/gaussian-stein-build.log`
- `.lake/build/gaussian-stein-axioms.log`
- `.lake/build/gaussian-stein-statements.log`

Original manuscript SHA-256 hashes match the preceding milestone; toolchain,
Mathlib lockfile, dependency configuration, and all earlier verified theorem
statements remain unchanged. The two pre-existing untracked Markdown documents
are preserved and excluded from this commit.

This completes the bounded C¹ Stein prerequisite identified in the previous
milestone. It does not prove entropy dissipation, generator/time commutation,
log-Sobolev, or an abstract Bakry–Émery criterion. Remaining M3 obligations are:

1. Positive-time C² smoothing of the actual Mehler evolution from bounded C¹
   input, with actual second-derivative bounds on compact positive-time intervals.
2. Time differentiation of the actual Mehler kernel under its inner integral,
   with local positive-time domination; derive the generator formula
   `∂t P_t g = (P_t g)'' - x (P_t g)'` using the proved Stein identity.
3. Outer entropy differentiation with an integrable local time dominator;
   justify all logarithms and reciprocal denominators using M2b's proved
   positive lower-bound preservation.
4. Establish the weighted bilinear IBP needed for the evolved logarithm, using
   actual derivatives and the newly proved Stein identity only after proving
   its application hypotheses. Assemble
   `HasDerivAt (entropyTrajectory g) (-fisherInformation (P_t g)) t` for `t > 0`.

Continuity and the ergodic entropy limit from the preceding milestone remain
verified. No complete entropy differentiation argument was begun here. The
next independently verifiable analytic milestone is positive-time spatial
second-derivative regularity/bounds for the existing Mehler kernel; arbitrary
supplied derivative candidates must not replace actual derivatives.

## Static Gaussian rotation and bounded C¹ Stein pairing (direct interpolation B1)

The preceding paragraph records the earlier generator-route recommendation; the direct interpolation route is now selected for M3.

`Foundation/GaussianRotationStein.lean` implements only the first static milestone of
`M3_ENTROPY_DISSIPATION_STRATEGY.md`. It reuses the existing variance-one
`GaussianCore.γ` and the verified bounded C¹ `GaussianSteinBounded.stein_identity`.
No time or entropy derivative is asserted here.

* `gaussian_rotation_map`: for **any real** `a,b` satisfying `a²+b²=1`, the
  map `(x,y) ↦ (a*x+b*y, -b*x+a*y)` preserves `γ.prod γ`. The sign of `b`
  is handled by choosing `arccos a` or its negative. The result is a direct
  specialization of Mathlib's `IsGaussian.map_rotation_eq_self`, with
  centeredness and exact coordinate formulas proved.
* `product_abs_coordinates_integrable`: both absolute coordinate functions
  have finite `γ.prod γ` integrals. This follows from Mathlib's Gaussian
  first `Lp` moment, not from totalized integral algebra.
* `rotated_stein_integrable`: for bounded measurable `k`, bounded C¹ `ψ`
  whose **actual derivative** is bounded, all four product integrands in
  the original and rotated Stein pairings are integrable. The unbounded
  factor is at most linear in one or both Gaussian coordinates; explicit
  absolute-coordinate majorants establish finiteness.
* `rotated_stein_identity`: under the same bounds and `a²+b²=1`,

  ```text
  ∫ ψ(x) k(a*x+b*y) (-b*x+a*y) d(γ⊗γ)
    = -b ∫ ψ'(x) k(a*x+b*y) d(γ⊗γ).
  ```

  This remains valid for negative `b` and at `b=0`; no division by `b`
  occurs. Rotate to `(z,v)`, use the inverse `x=a*z-b*v`, apply the verified
  one-dimensional Stein theorem to `v ↦ ψ(a*z-b*v)`, multiply by `k(z)`,
  use product Fubini, and rotate back. `k` is never differentiated.

This identity supplies the fixed-time integration-by-parts step of direct
Gaussian interpolation. It does **not** imply entropy dissipation alone. The
remaining M3 obligations are the actual positive-time derivative of the
existing Mehler kernel, a common local integrable dominator for its
parameter derivative, positive-time C¹/log-factor packaging, outer entropy
differentiation under the Gaussian integral, and identification of the
result with negative Fisher information. The proved zero-time continuity is
separate from positive-time differentiation. Neither log-Sobolev nor any
abstract Bakry–Émery criterion is claimed.

The new proof uses pinned Mathlib's Gaussian rotation invariance and first
Gaussian moment, plus the project's already attributed bounded Stein theorem.
It adapts no code from the upstream `markov-semigroups` repository; the
existing local Apache-2.0 attribution for the Stein foundation remains.

Verification: full `lake build` passes (3377 jobs). The complete transitive
`Foundation/AxiomAudit.lean` run has 777 reports, including `#print axioms`
for all five new declarations. Each of those five depends only on
`propext`, `Classical.choice`, and `Quot.sound`; the complete transcript
contains no `sorryAx` or custom axiom. Exact elaborated `#check @...`
checks for all five pass. The new module contains no `sorry`, `admit`,
`axiom`, or `unsafe`. Its compile has no warnings; the two pre-existing
unused-section-variable warnings in `Foundation.Adjoint` remain. The
corresponding ignored logs are `gaussian-rotation-build.log`,
`gaussian-rotation-axioms.log`, and `gaussian-rotation-statements.log`
under `.lake/build`.

## Actual positive-time derivative of the Gaussian Mehler kernel (direct interpolation B2)

`Foundation/GaussianMehlerTimeDerivative.lean` uses the **existing**
`GaussianMehler.mehler` integral. Set `a(t)=exp(-t)` and
`b(t)=sqrt(1-exp(-2t))`. Under `ContDiff ℝ 1 g`, a global norm bound
`‖g z‖≤M`, and a global bound `‖deriv g z‖≤B` on the **actual** derivative,
the new theorem `hasDerivAt_mehler_time` proves, for `t>0` and any `x`, both
integrability of the differentiated kernel and

```text
HasDerivAt (fun s => GaussianMehler.mehler s g x)
  (∫ y, deriv g (a(t)*x+b(t)*y)
       * (-a(t)*x+(a(t)^2/b(t))*y) dγ(y)) t.
```

`deriv_mehler_time` states the corresponding equality for Mathlib's actual
`deriv`. No derivative at zero is claimed, since the displayed velocity
contains `1/b(t)`.

The supporting results establish `a(t)^2+b(t)^2=1` for `t≥0`, `b(t)>0`
for `t>0`, `a'(t)=-a(t)`, `b'(t)=a(t)^2/b(t)` for `t>0`, continuity of `b`,
and an explicit positive-time neighborhood
`U={s | b(t)/2 < b(s)} ∩ (0,∞)`. On `U` the denominator is at least
`b(t)/2>0`, `0≤a(s)≤1`, and `velocity_bound` proves

```text
|-a(s)*x+(a(s)^2/b(s))*y| ≤ |x|+|y|/(b(t)/2).
```

Thus the derivative integrand is dominated by
`B*(|x|+|y|/(b(t)/2))`. The bound is independent of `s` on `U` and is
integrable in `y` by Mathlib's finite first Gaussian moment. The proof also
establishes measurability of the original and derivative kernels, bounded
integrability at the base time, and the actual pointwise chain rule throughout
`U`. Only then does it apply Mathlib
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, which returns derivative
integrability and the genuine integral derivative simultaneously. The
formula's coefficient signs follow from `a'=-a` and `b'=a²/b`.

This theorem does not use rotation/Stein, Fisher decay, C² input, entropy
dissipation, or an assumed derivative candidate. It prepares the outer
entropy differentiation; the static rotated Stein identity from B1 will be
used only when identifying that outer derivative with negative Fisher
information. Remaining M3 obligations are positive-time C¹ regularity and
bounded derivative of the evolved Mehler function, logarithmic-factor
positivity/bounds, outer differentiation under the Gaussian integral with a
common local majorant in `x`, and the final rotation/Stein pairing. The
zero-time continuity already proved elsewhere remains a separate result.

Verification: full `lake build` passes (3378 jobs). The complete transitive
axiom audit has 790 reports, including all 13 new definitions/theorems;
each new declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`. The complete audit contains no `sorryAx` or custom axiom.
Exact elaborated `#check @...` checks pass for every new declaration.
The new module has no warning or `sorry`, `admit`, `axiom`, or `unsafe`.
Only the two pre-existing unused-section-variable warnings in
`Foundation.Adjoint` remain. Logs are under `.lake/build/` as
`gaussian-time-build.log`, `gaussian-time-axioms.log`, and
`gaussian-time-statements.log`. No original manuscript, existing theorem
statement, toolchain, or dependency pin changes.

## Complete one-dimensional positive-time entropy dissipation (direct interpolation M3)

`Foundation/GaussianEntropyDissipationProof.lean` proves the actual derivative
of the **existing centered** entropy trajectory for the **existing**
variance-one Mehler semigroup. Let `g : ℝ → ℝ` satisfy `ContDiff ℝ 1 g`,
`0<ε`, `ε≤g(z)≤M`, and `‖deriv g z‖≤B` for every `z`. The final statements,
for every `t>0`, are:

```text
hasDerivAt_entropy_dissipation:
  HasDerivAt (GaussianEntropyDissipation.entropyTrajectory g)
    (-GaussianFisher.fisherInformation (GaussianMehler.mehler t g)) t

deriv_entropy_dissipation:
  deriv (GaussianEntropyDissipation.entropyTrajectory g) t
    = -GaussianFisher.fisherInformation (GaussianMehler.mehler t g)
```

`GaussianFisher.fisherInformation u` is exactly
`∫ (deriv u(x))²/u(x) dγ(x)`. `evolved_fisher_integrable` proves that this
specific integrand is integrable using the proved lower bound and actual
spatial derivative bound. No mass-one normalization is imposed on `g`.
There is no factor two, because `γ=gaussianReal 0 1` has variance one.

Proof dependencies and analytic obligations discharged:

1. `mehler_contDiff_one` combines the verified actual spatial derivative
   commutation with continuity of the Mehler average of `deriv g`.
   `mehler_bounds` gives `ε≤P_tg≤M`, and `mehler_deriv_bound` gives
   `‖(P_tg)'‖≤B` for `t≥0`.
2. `logFactor t g x = 1+log(P_tg(x))` is proved C¹ with actual derivative
   `(P_tg)'/(P_tg)`. The logarithm's argument is positive, and
   `logFactor_bound` and `deriv_logFactor_bound` give explicit bounds
   `1+|log ε|+|log M|` and `B/ε`. These bounds do not assume that one lies
   between `ε` and `M`.
3. `timeVelocity` names the concrete formula established by the preceding
   Mehler time-derivative theorem. Its measurability in `x` is proved by
   Mathlib's product-parameter integral API. For `s` in the verified
   neighborhood of `t₀>0`, `timeVelocity_local_bound` proves
   `‖timeVelocity s g x‖ ≤ B*(|x|+m₁/(b(t₀)/2))`, where
   `m₁=∫|y|dγ<∞`. The first Gaussian moment makes the outer majorant
   integrable in `x`.
4. `hasDerivAt_entropy_raw` applies Mathlib's dominated local
   differentiation theorem to the *actual* integrand
   `P_sg(x) log(P_sg(x))`. It proves measurability, base-time
   integrability, a common positive-time majorant, and the pointwise
   chain rule throughout the neighborhood before interchanging derivative
   and outer integral.
5. `hasDerivAt_entropyTrajectory_raw` uses the already verified Gaussian
   invariance of the mean on a positive-time neighborhood. It transfers
   the derivative to the original centered entropy; no globally false
   negative-time invariance identity is used.
6. `entropy_pairing_eq_neg_fisher` proves the product integrability needed
   for both Fubini interchanges by the verified
   `GaussianRotationStein.rotated_stein_integrable`. It rewrites the time
   velocity as `(a/b)(-b*x+a*y)` with `b>0`, applies the proved
   `rotated_stein_identity`, then uses the actual identities
   `deriv(P_tg)=a P_t(deriv g)` and
   `deriv(logFactor)=(deriv(P_tg))/(P_tg)` to obtain negative Fisher
   information. The sign and cancellation of `b` are checked in Lean.

The previously verified `entropyTrajectory_tendsto_zero_time` and
`entropyTrajectory_tendsto_atTop` supply continuity at zero and convergence
of centered entropy to zero at infinity. This milestone adds the positive-time
derivative, **not** a two-sided derivative at zero. It does not prove a
log-Sobolev inequality, extend the input beyond bounded positive C¹
functions, or establish an abstract Gamma₂ curvature theorem. Those are
separate later obligations. The proof uses local Mathlib Gaussian,
parametric-integral, and product-measure infrastructure; no upstream source
code was copied into this module.

Verification: full `lake build` passes (3379 jobs). The complete
transitive `Foundation/AxiomAudit.lean` run contains 808 reports,
including all 18 new declarations. Each new declaration depends only
on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or
custom mathematical axiom appears. All 18 exact elaborated `#check @...`
checks pass. The new module has no warnings and contains no `sorry`,
`admit`, `axiom`, or `unsafe`. Two pre-existing unused-section-variable
warnings in `Foundation.Adjoint` remain. Ignored transcripts are under
`.lake/build/` as `gaussian-entropy-dissipation-build.log`,
`gaussian-entropy-dissipation-axioms.log`, and
`gaussian-entropy-dissipation-statements.log`. No original manuscript,
previous theorem statement, dependency pin, or lockfile changes.
## M4: bounded C¹ Gaussian log-Sobolev core

`Foundation/GaussianLogSobolevCore.lean` proves the variance-one standard
Gaussian inequality for every actual `ContDiff ℝ 1 f` whose values and actual
Mathlib derivative are uniformly bounded by a common finite `M`:

`entropySq γ f ≤ 2 * ∫ x, (deriv f x) ^ 2 ∂γ`.

No positivity or nonvanishing condition is imposed on `f`. The separate
`core_sq_mul_log_integrable` theorem establishes finiteness of the
`f² log(f²)` integral from the bounded C¹ hypothesis through M1's L⁴
integrability theorem. The derivative energy is integrable by an explicit
Gaussian probability-space bound in `regularized_fisher_le_energy`.

The positive-density lemma `entropyDensity_le_half_fisher` applies to a
uniformly positive bounded C¹ `g` with bounded actual derivative. It combines
M3's genuine identity `d/dt Entγ(P_tg) = -I(P_tg)` and M2b's
`I(P_tg) ≤ exp(-2t) I(g)` by proving that
`Entγ(P_tg) - exp(-2t) I(g)/2` is monotone for `t ≥ 0`.
Continuity of entropy at zero and its verified limit zero at infinity give
`Entγ(g) ≤ I(g)/2`. This comparison is equivalent to integrating the
exponential bound, without invoking an unverified improper integral.

For arbitrary core `f`, `regularized_deriv` proves the actual derivative
`(f²+ε)'=2ff'`, and `regularized_fisher_le_energy` proves
`I(f²+ε) ≤ 4 ∫(f')²` for each `ε>0`. `regularized_entropy_tendsto`
uses `ε_n=1/(n+1)` and genuine bounded dominated convergence for both
integrals in centered entropy, using Mathlib's continuous `r log r` at zero.
The resulting factor is exactly `1/2 * 4 = 2` for the standard Gaussian
variance-one normalization. The proof does not assume log-Sobolev.

This is a Gaussian special-case theorem on a bounded C¹ core. It does not
replace the original general Bakry–Émery axiom or establish its full-domain
version. M5–M6 require a noncircular approximation theorem that preserves
both the derivative energy and entropy (or another justified domain
extension). An abstract Γ₂ curvature criterion remains a separate result.
Verification: full `lake build` passes (3380 jobs). The transitive
`Foundation/AxiomAudit.lean` run reports 815 declarations. Each of the
seven new declarations uses only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or custom mathematical axiom occurs. The new
Lean module has no warnings, `sorry`, `admit`, `axiom`, or `unsafe`.
The two pre-existing unused-section-variable warnings in
`Foundation.Adjoint` remain. No previous Lean theorem statement, original
manuscript, dependency pin, or lockfile was changed.

## M5a: local Gaussian Sobolev bridge

`Foundation/GaussianLocalSobolev.lean` establishes the first M5 prerequisite
without a graph-density or entropy hypothesis. Its measure comparison says
that for every real `a,b` there is a finite positive `C` such that

`volume.restrict (Set.Icc a b) ≤ C • GaussianCore.γ`.

The Gaussian density is continuous and strictly positive. Mathlib's compact
minimum theorem supplies a positive lower bound on `Icc a b`; it also handles
`b < a`, when that interval is empty and its restricted measure is zero.
The identity of the Gaussian measure with Lebesgue measure weighted by its
actual density, `withDensity_mono`, and restriction/scaling yield the displayed
measure comparison. `MemLp.of_measure_le_smul` then proves local Lebesgue
`L²` membership for any Gaussian `L²` function, with no extra measurability
assumption beyond `MemLp`.

For ordinary functions `f,h : ℝ → ℝ`, assume only
`∀ x, HasDerivAt f (h x) x` and
`Integrable (fun x => (h x)^2) GaussianCore.γ`.
`derivative_eq_deriv` identifies `h` pointwise with Mathlib's `deriv f`;
`measurable_deriv` supplies measurability. `memLp_two_iff_integrable_sq`
and the local measure comparison give local Lebesgue `L²`, hence local `L¹`.
`intervalIntegrable_derivative_of_gaussian_sq_integrable` proves
`IntervalIntegrable h volume a b` for arbitrary endpoint order. Finally,
`integral_derivative_eq_sub_of_gaussian_sq_integrable` applies Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt` to conclude
`∫ x in a..b, h x = f b - f a`. No continuity of `h`, assumed absolute
continuity of `f`, or independently supplied local Lebesgue integrability is
used. No Gaussian log-Sobolev result is imported by this module.

This milestone proves a local FTC bridge, **not** the full weighted Sobolev
approximation from M5 and not the full-domain Gaussian LSI of M6. Remaining
M5 work: construct smooth cutoffs with simultaneous Gaussian `L²` control
of values and actual derivatives; smooth the compactly supported results
with both errors controlled; and prove a diagonal graph approximation.
Ambient `L²` density alone cannot discharge these obligations.

Verification: full `lake build` passes (3381 jobs). The six new public
declarations have exact elaborated `#check @...` probes in
`.lake/build/gaussian-local-sobolev-statements.log`. The complete
`Foundation/AxiomAudit.lean` run reports 821 declarations; each new
public declaration depends transitively only on `propext`,
`Classical.choice`, and `Quot.sound`, with zero `sorryAx` or custom axioms.
The module compiles without warnings. The two pre-existing unused-section-
variable warnings in `Foundation.Adjoint` remain. The build and axiom logs
are under `.lake/build/gaussian-local-sobolev-*.log`. No original source,
previous verified theorem statement, dependency pin, or lockfile changed.

## M5: simultaneous Gaussian L² cutoff approximation

`Foundation/GaussianSobolevCutoffs.lean` fixes one smooth bump `χ` equal to one on
`[-1,1]`, supported in `[-2,2]`, and defines `cutoff n x = χ(x/(n+1))` and
`truncated f n x = cutoff n x * f x`. Mathlib's `ContDiffBump` supplies smoothness,
value bounds, and compact support. The actual product derivative is
`cutoff n x * h x + deriv (cutoff n) x * f x` whenever
`∀ x, HasDerivAt f (h x) x`. No continuity of `h` is assumed.

Under Gaussian integrability of `f²` and `h²`,
`simultaneous_sq_error_tendsto` proves, with this **same** sequence, that
both `∫(truncated f n - f)² dγ` and
`∫(deriv (truncated f n) - h)² dγ` tend to zero. Its proof derives
measurability of `h` from the actual derivative, bounds the value error by
`f²`, and dominates the derivative error by `2h² + 2C²f²`, with `C` a
verified global bound on the base bump derivative. Dominated convergence is
applied only after these integrability and pointwise-limit facts are proved.
`derivative_cutoff_extra_sq_integral_bound` additionally establishes the
quantitative estimate

    ∫ (deriv (cutoff n) * f)² dγ ≤ (C/(n+1))² ∫ f² dγ.

This is a cutoff graph-approximation milestone, **not** smooth approximation
of `f`: the truncated function remains only differentiable with the original
regularity. The remaining M5 step is controlled smoothing of these compactly
supported functions and their actual derivatives, followed by a diagonal
sequence. M6 entropy limits and the original Bakry–Émery axiom replacement
remain open. No original manuscript or dependency pin was changed.

Verification for this milestone: complete `lake build` succeeds (3390 jobs).
`Foundation/AxiomAudit.lean` succeeds with 833 transitive reports. All 12
new public declarations have only `propext`, `Classical.choice`, and
`Quot.sound` in their transitive axiom sets; no `sorryAx` or custom axiom
is reported. The two pre-existing unused-section-variable warnings in
`Foundation.Adjoint` remain unrelated to this module.

## M5: compact-support derivative and primitive bridge

`Foundation/GaussianSobolevSmoothApprox.lean` establishes the fixed-cutoff
hypotheses required before smoothing. For an everywhere differentiable `f`
with actual derivative `h`, compact support of `f`, and Gaussian integrability
of `h²`, `compact_derivative_memLp_volume` proves `h ∈ L²(volume)` by
bounding the support of `deriv f` inside a finite interval and applying the
verified local Gaussian-to-Lebesgue comparison. No continuity of `h` is used.
`compact_derivative_integrable_volume` upgrades this to global Lebesgue
integrability. `compact_derivative_integral_zero` then uses the verified local
FTC on an interval strictly containing both supports to prove `∫h dx=0`.
`compact_primitive_representation` supplies a point left of the support
from which `f(x)=∫_a^x h(y)dy` for every real `x`.

The module applies these results to each `truncated f n` from the previous
milestone under exactly the original Gaussian square-integrability and
actual-derivative hypotheses. It proves square integrability of each actual
cutoff derivative, zero Lebesgue integral, and an exact primitive formula.
This establishes the compatibility condition for zero-mean derivative
smoothing. It does **not** assert smooth graph density: the cutoff remains
only everywhere differentiable, and no smooth approximating derivative,
fixed-support correction, primitive error bound, or diagonal sequence has
yet been constructed.

The remaining M5 proof needs (i) smooth Lebesgue-L² approximation of each
compactly supported derivative with support in a common larger interval,
(ii) correction by a normalized smooth bump so the derivative approximants
have integral zero, (iii) quantitative control of both the primitive and
derivative errors on that interval, (iv) transfer of both estimates to
Gaussian L², and (v) a diagonal sequence combined with the cutoff limits.
M6 entropy limits are not begun. No original manuscript or dependency pin
was modified.

Verification: complete `lake build` succeeds (3391 jobs). The direct
`Foundation/AxiomAudit.lean` check succeeds with 842 transitive reports.
All nine new public declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom appears.
The new module has no warnings. The two pre-existing unused-section-variable
warnings in `Foundation.Adjoint` are unchanged.

## M5: fixed-support smooth approximation and zero-mean correction

`Foundation/GaussianSobolevFixedSupport.lean` establishes a smaller supporting milestone for the fixed-compact-support smoothing argument. For a Lebesgue `L²` function `h` with pointwise support in `[-R,R]`, `R ≥ 0`, and every `ε > 0`, `exists_fixed_support_smooth_approx` gives a genuinely smooth approximant `v` supported in the *same enlarged interval* `[-(R+2),R+2]`, with `eLpNorm (h-v) 2 volume ≤ ENNReal.ofReal ε`. The proof applies Mathlib's smooth compactly supported `L²` density theorem, then multiplies the approximant by a smooth bump equal to one on the support of `h`. Its pointwise bound by one ensures this support truncation does not increase the `L²` error.

`exists_unit_integral_bump` constructs a smooth `q` supported in the enlarged interval with `∫q dx=1`, using Mathlib's normalized `ContDiffBump`; the integral is a proved property of that construction. The definition `corrected v q = v - (∫v dx) q` and `corrected_properties` prove that the corrected function is smooth, retains the same fixed support, and has zero Lebesgue integral. Integrability of both terms is derived from smoothness and compact support.

This milestone does **not** yet establish convergence of the corrected approximants. The remaining quantitative lemma must bound `|∫v dx| = |∫(v-h) dx|` by the Lebesgue `L²` error on the common finite interval, using the already proved `∫h dx=0` for cutoff derivatives. Then one must bound the `L²` error added by `(∫v)q`, construct the compactly supported smooth primitives, prove their actual derivatives and quantitative primitive error bound, transfer both estimates to Gaussian `L²`, and finally diagonalize across cutoffs. None of those results is assumed here, and neither the final M5 theorem nor M6 has been started. Original manuscripts and dependency pins remain unchanged.

Verification for this fixed-support subset: the complete `lake build` succeeds (3441 jobs). Direct `lake env lean Foundation/AxiomAudit.lean` succeeds. All four newly audited declarations report exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom is reported. The new module has no warnings.

## M5: smooth compactly supported primitives of corrected approximants

`Foundation/GaussianSobolevPrimitives.lean` proves the primitive part of the fixed-support construction. `integrable_of_memLp_two_support` derives global Lebesgue integrability from Lebesgue `L²` membership and support in a finite interval. `correction_integrable` proves actual integrability of the original derivative `h`, smooth approximant `v`, their difference, and the corrected function `v-(∫v)q`. The latter three use smoothness and common compact support; no totalized-integral artifact is used.

For any continuous `w`, `primitive a w x := ∫ y in a..x, w y` has actual Mathlib derivative `w x` at every `x`. If `w` is smooth, this primitive is `C∞`. If `support w ⊆ [A,B]`, `a<A`, and `∫w dx=0`, then the primitive vanishes for `x≤A` and `x≥B`, hence has compact support. In particular, `corrected_primitive_properties` applies the previous module's proved zero-integral correction to construct a `C∞` compactly supported primitive whose actual derivative is precisely `corrected v q`. The right-hand vanishing relies on the proved zero total integral, not on an assumption about the primitive.

The **quantitative correction estimate is still open**. In Lean one must bound `|∫v dx|=|∫(v-h)dx|` by the `L²` error on the common finite interval, using the previously proved `∫h dx=0`. This requires a finite-measure Hölder/Cauchy–Schwarz bridge between the restricted Lebesgue integral and the global `eLpNorm`. The derived bound must then control `‖corrected v q-h‖₂`. Without that, neither convergence of the corrected approximants nor simultaneous Gaussian graph convergence follows. The next step is this restricted-measure estimate, followed by the primitive error bound and Gaussian transfer. The final diagonal M5 approximation and M6 are untouched. Original manuscripts and dependency pins are unchanged.

Verification for this primitive milestone: complete `lake build` succeeds (3442 jobs); direct `lake env lean Foundation/AxiomAudit.lean` succeeds. Every new declaration depends transitively only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom appears. The new module builds without warnings. The only build warnings are the two pre-existing unused-section-variable warnings in `Foundation.Adjoint`.

## M5: quantitative fixed-support smooth graph approximation

`Foundation/GaussianSobolevQuantitative.lean` completes the fixed-compact-support argument. Its `L2Norm u` is `sqrt (∫u² dx)`. Every estimate using this notation has the appropriate Lebesgue `MemLp u 2 volume` hypothesis; `L2Norm_eq_eLpNorm` proves that, under this hypothesis, it is exactly Mathlib's finite `L²` seminorm. The bare definition is totalized for arbitrary functions, but no estimate treats a non-`L²` input as integrable.

`cs_setIntegral` proves finite-interval Cauchy–Schwarz for `u ∈ L²(volume.restrict [A,B])`, `A≤B`: `|∫_[A,B]u dx| ≤ sqrt(B-A) sqrt(∫_[A,B]u² dx)`. `cs_integral_of_support` transfers this to the global integral when `support u ⊆ [A,B]`. `integral_v_bound` then proves, for Lebesgue-L² `h,v` supported in `[A,B]` and `∫h dx=0`, `|∫v dx| ≤ sqrt(B-A) L2Norm(v-h)`. All needed global integrability follows from finite support and L² membership, using the previous module. Endpoints are handled through equality of `Icc` and `Ioc` set integrals under Lebesgue measure.

`correction_error` applies Mathlib's `lpNorm` triangle inequality and exact scalar norm law to `w=corrected v q`, yielding `L2Norm(w-h) ≤ (1+sqrt(B-A)L2Norm(q))L2Norm(v-h)`. It only requires L² membership of `q`; the final construction supplies this from the existing smooth compactly supported unit-integral bump. `corrected_properties` independently proves smoothness, common support, and zero integral for this `w`.

`primitive_error_on_Icc_from_left` proves, when `a<A` and `h,w ∈ L²(volume)` are supported in `[A,B]`, `|primitive a w x - primitive a h x| ≤ sqrt(B-A)L2Norm(w-h)` for `x∈[A,B]`. `primitive_change_base` justifies shifting the integration start from `a` to `A`; it uses the verified vanishing of the integrand to the left, not an extra regularity assumption. With proved zero integrals of both functions, `primitive_error_global` extends the bound to all real `x` because both primitives vanish outside the interval. `primitive_gaussian_sq_error` proves genuine Gaussian integrability and the function-error bound `(B-A)L2Norm(w-h)²`.

`standard_gaussian_le_volume` proves the standard Gaussian measure is dominated by Lebesgue measure, directly from the Gaussian PDF bound `gaussianPDFReal 0 1 x ≤ 1`. Thus `gaussian_sq_error_le_volume` gives genuine integrability and `∫u² dγ ≤ L2Norm(u)²` for every Lebesgue-L² `u`. `actual_derivative_support_in_Icc` proves support of an actual everywhere derivative lies in the closed support interval of `f`, and `actual_primitive_from_left` uses the previously verified Gaussian-local FTC to identify the original `f` with its primitive. `fixed_support_graph_error` consequently bounds both Gaussian squared errors for a smooth zero-mean `w`, with the *actual* derivative of its primitive.

Finally, `fixed_support_smooth_graph_approx` states: for `R≥0`, an everywhere actual derivative `∀x, HasDerivAt f (h x) x`, `support f ⊆ [-R,R]`, `Integrable (fun x => h x²) γ`, and every `tol>0`, there exists `F` with `ContDiff ℝ ∞ F`, `HasCompactSupport F`, `∫(F-f)² dγ < tol`, and `∫(deriv F-h)² dγ < tol`. The **same** `F` meets both inequalities. The proof uses controlled-support smooth Lebesgue-L² density, the normalized bump and its zero-mean correction, the quantitative estimates above, and the smooth compact primitive. It assumes neither continuity of `h` nor graph density. No additional `f∈L²(γ)` hypothesis is needed in this fixed-support setting; everywhere differentiability gives continuity, and compact support gives boundedness.

This is the fixed-support stage of M5, **not** the global weighted Sobolev approximation theorem. The next step is a diagonal choice combining these approximants with `GaussianSobolevCutoffs.simultaneous_sq_error_tendsto` for arbitrary Gaussian-L² `f` and actual derivative `h`. M6 entropy limits and any replacement of the original Bakry–Émery axiom remain separate.

## M5: global simultaneous Gaussian smooth graph approximation

`Foundation/GaussianSobolevGlobalApprox.lean` proves `exists_smooth_compact_graph_sequence`. If `f` has actual derivative `h` at every real point and both `f²` and `h²` are integrable for the standard Gaussian measure, there is **one** sequence `Fₙ` of C∞ compactly supported functions such that both `∫(Fₙ-f)² dγ → 0` and `∫(deriv Fₙ-h)² dγ → 0`. The proof applies the verified fixed-support graph approximation to each smooth-cutoff truncation with tolerance `1/(n+1)`. It proves square integrability of the function and derivative errors through Mathlib `MemLp`, then uses the integrated squared triangle inequality and the previously verified simultaneous cutoff limits. The derivatives are actual Mathlib derivatives; no continuity of `h`, positivity of `f`, or assumed graph density is used.

This completes the global smooth graph-approximation statement of M5 for everywhere differentiable representatives with Gaussian-L² value and derivative. Extension of the Gaussian log-Sobolev inequality to this class, including entropy convergence, is M6 and remains unproved. The general Bakry–Émery curvature theorem and original manuscript remain untouched.

Verification: complete `lake build` succeeds (3444 jobs), and direct `lake env lean Foundation/AxiomAudit.lean` succeeds. The new theorem's transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or custom axiom. The two existing unused-section-variable warnings in `Foundation.Adjoint` are unchanged.

## M6: full one-dimensional Gaussian log-Sobolev inequality

`Foundation/GaussianLogSobolevFull.lean` proves `gaussian_logSobolev_of_hasDerivAt`: for any real functions `f,h` with `HasDerivAt f (h x) x` at every `x` and Gaussian integrability of `f²` and `h²`, the function `f² log(f²)` is genuinely Gaussian-integrable and `entropySq γ f ≤ 2 ∫h² dγ`. No positivity, boundedness, or C¹ regularity assumption appears. `gaussian_logSobolev_of_hasDerivAt_pos` adds the original axiom's strict-positivity hypothesis as a compatibility corollary, with the same measure and factor 2.

The proof applies the verified M5 simultaneous graph approximation to obtain one sequence of smooth compactly supported `Fₙ`. A real `L²` norm lemma proves convergence of `∫Fₙ²` and `∫(deriv Fₙ)²`. M4 gives an inequality for the *genuinely integrable* nonnegative quantity `klFun(Fₙ²) = Fₙ² log(Fₙ²)+1−Fₙ²`. The Gaussian-L² error gives convergence in measure and then an almost-everywhere convergent subsequence. Fatou and continuity of `klFun` bound the limiting extended integral by the finite limit of the M4 bounds. Only after proving that extended integral finite does the proof infer integrability of `klFun(f²)`, then of `f² log(f²)`, and finally rewrite the inequality in centered entropy form. This avoids using a totalized real integral for a potentially nonintegrable function and handles `f=0` pointwise.

The theorem is the concrete variance-one Gaussian inequality under the original derivative and L² hypotheses. It does not establish the abstract `Γ₂ ≥ κΓ` Bakry–Émery curvature criterion, nor does this milestone edit or replace the axiom in the original manuscript/source.

Verification: complete `lake build` succeeds (3445 jobs), and direct `lake env lean Foundation/AxiomAudit.lean` succeeds. Both new public theorems depend transitively exactly on `propext`, `Classical.choice`, and `Quot.sound`; neither depends on `sorryAx` or a custom axiom. The two pre-existing `Foundation.Adjoint` unused-section-variable warnings remain unchanged.

Verification: complete `lake build` succeeds (3443 jobs); direct `lake env lean Foundation/AxiomAudit.lean` succeeds. All 19 new public declarations have transitive axiom sets contained in `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom appears. The new module has no warnings. Only the two pre-existing unused-section-variable warnings in `Foundation.Adjoint` remain. Original manuscripts and dependency pins are unchanged.

## P0: one-site Poisson finite-support difference/divergence calculus

`Foundation/PoissonDifferenceCore.lean` uses Mathlib's actual
`ProbabilityTheory.poissonMeasure rate` on `ℕ`, with `rate : ℝ≥0`.
`poisson_weight_pos` explicitly assumes `0 < rate`; the recurrence and finite-support
identities are stronger and hold for every nonnegative rate. For
`w(n) = (poissonMeasure rate).real {n}`, `poisson_weight_succ` proves
`(n+1) w(n+1) = rate w(n)`. This includes `n=0`.

For actual `Finsupp` functions `f,u : ℕ →₀ ℝ`, `forwardDifference f n` is
`f(n+1)-f(n)`. `backwardWeighted u 0 = 0` and
`backwardWeighted u (n+1) = (n+1)u(n)`, so
`poissonDivergenceExpr rate u n = backwardWeighted u n-rate*u(n)`.
`divergence_at_zero` and `divergence_at_succ` verify both boundary formulas explicitly.
The finite-support lemmas prove these functions retain finite support.
`integrable_of_finite_support` uses Mathlib's exact Poisson integrability
criterion; `memLp_two_of_finite_support` derives genuine L² membership from
integrability of the actual square. The module proves L² membership for the
finite-support fields and both pairing integrands under the Poisson measure,
and also under the `rate`-weighted Poisson measure. The two pairing terms are
separately proved integrable before the real integral identities are used.

`poisson_shift_finsupp` states

`∫ n, (n : ℝ) * f n ∂poissonLaw rate =
  (rate : ℝ) * ∫ n, f (n+1) ∂poissonLaw rate`.

`poisson_difference_ibp_finsupp` states

`(rate : ℝ) * ∫ n, forwardDifference f n * u n ∂poissonLaw rate =
  ∫ n, f n * poissonDivergenceExpr rate u n ∂poissonLaw rate`.

Both proofs use `integral_poissonMeasure'` only after proving integrability,
then reindex summable finite-support series by the proved weight recurrence.
`poisson_difference_mul_finsupp` proves the actual pointwise product identity
`D(f*g) = f*Dg + g*Df + Df*Dg` for Mathlib's pointwise `Finsupp` product.
The extra quadratic term distinguishes this jump difference calculus from
an ordinary differential derivation.

This is a finite-support IBP milestone. No maximal operator domain,
closability, graph-density, adjoint equality, Poisson process representation,
or ordinary chain rule is asserted. P1–P5 from
`OPERATOR_DERIVATIVE_NON_GAUSSIAN_RESEARCH_AUDIT.md` remain open.
Verification for P0: the complete `lake build` succeeds (4006 jobs), including
`Foundation.PoissonDifferenceCore` and the project root. Direct
`lake env lean Foundation/AxiomAudit.lean` succeeds. All 34 new public
declarations have transitive axiom dependencies among exactly `propext`,
`Classical.choice`, and `Quot.sound`; none uses `sorryAx` or a custom axiom.
The new module emits no warnings. The two existing unused-section-variable
warnings in `Foundation.Adjoint` remain unchanged. The original manuscripts
and dependency pins were not modified.
## P1: genuine Poisson Hilbert core operators

`Foundation/PoissonDifferenceOperators.lean` uses the actual scalar Hilbert space
`Lp ℝ 2 (poissonLaw rate)` and field Hilbert space
`Lp ℝ 2 ((rate : ℝ≥0∞) • poissonLaw rate)`, with `0 < rate` for
injectivity and dense operator domains. Finite-support functions are embedded
as L² equivalence classes by `scalarEmbedding` and `fieldEmbedding`; positivity
of every Poisson singleton mass proves both embeddings injective. Pairing with
coordinate indicators extracts each L² representative at its atom, which
proves that both finite-support ranges are dense. This is ambient L² density,
not graph-norm density.

`differenceGraph` and `divergenceGraph` are the ranges of the actual
finite-support linear maps. `coreDifference` and `coreDivergence` are their
single-valued `LinearPMap`s. `coreDifference_finsupp_apply` and
`coreDivergence_finsupp_apply` identify their values with `f(n+1)-f(n)` and
`n u(n-1)-rate*u(n)`, including the zero boundary. The scalar and field
inner-product lemmas prove the latter carries the rate factor. Consequently
`coreDifference_formalAdjoint` is the P0 integration-by-parts identity in the
genuine Hilbert spaces. `coreDifference_le_divergence_adjoint` and
`coreDivergence_le_difference_adjoint` give operator inclusions, while
`coreDifference_isClosable` and `coreDivergence_isClosable` follow from these
inclusions and dense domains.

No maximal weighted domain, closed-operator equality, graph-core density, or
mutual-adjoint equality is claimed at P1. Those are the separate P2–P4 tasks.
P1 verification: complete `lake build` succeeds (4007 jobs). Direct
`lake env lean Foundation/AxiomAudit.lean` succeeds. Every new P1 declaration
has transitive axioms contained in `propext`, `Classical.choice`, and
`Quot.sound`; none uses `sorryAx` or a custom axiom. Exact elaborated types
of the formal-adjoint, dense-domain, and closability theorems were inspected
with Lean. Only the two pre-existing unused-section-variable warnings in
`Foundation.Adjoint` remain. P2 weighted maximal domains are next.
## P2 preparation: closed maximal pointwise Poisson operators

`Foundation/PoissonCoordinateEvaluation.lean` constructs continuous linear
coordinate functionals on both genuine Poisson L² spaces. Positive mass at
every count makes actual chosen L² representatives pointwise compatible with
addition, scalar multiplication, and Hilbert-space convergence. This is the
analytic mechanism needed to reason about coefficientwise graph limits.

`Foundation/PoissonMaximalOperators.lean` defines `maximalDifferenceGraph`
by `v(n)=f(n+1)-f(n)` and `maximalDivergenceGraph` by the exact zero-boundary
and successor formulas. Every graph equation is a closed condition under the
continuous coordinate maps. The graphs are single-valued, so
`maximalDifference` and `maximalDivergence` are actual `LinearPMap`s, both
proved closed. `coreDifference_le_maximal` and `coreDivergence_le_maximal`
prove the P1 operators are restrictions of these maximal pointwise operators.
No adjoint equality or graph-density hypothesis is used in their definitions.

**Remaining P2 obligation:** show the domains of these maximal operators are
exactly the proposed weighted square-summability classes. Closedness and
coefficientwise descriptions alone do not establish those weighted-domain
equalities. P3 graph-core density and P4 mutual-adjoint identification also
remain open.
P2 preparation verification: complete `lake build` succeeds (4009 jobs), and
direct `lake env lean Foundation/AxiomAudit.lean` succeeds. All 31 new
declarations depend transitively only on `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or custom axiom occurs. Exact elaborated types of
coordinate evaluation, closedness, and core inclusion were checked with Lean.
The only warnings are the two pre-existing unused section variables in
`Foundation.Adjoint`. This is a verified partial P2 milestone, not the
weighted-domain characterization or graph-core theorem.
## P2: exact weighted domains of the closed maximal Poisson operators

`Foundation/PoissonWeightedDomains.lean` proves that Poisson L² membership is
exactly summability of the genuine Poisson masses times the actual squared
function values. The positive rate-scaled field measure has the same
summability test. The Poisson mass recurrence and a nonzero-rate series
scaling prove `summable_shift_sq_iff_moment` and
`summable_backward_sq_iff_moment`, including the `n=0` boundary. These are
series equivalences, not definitions of operator domains.

The exact domain theorems are:

- `mem_maximalDifference_domain_iff_moment`: for every scalar class `f`,
  membership in `maximalDifference.domain` is equivalent to summability of
  `n * poissonWeight rate n * (f n)^2`.
- `mem_maximalDivergence_domain_iff_moment`: for every weighted-field class
  `u`, membership in `maximalDivergence.domain` is equivalent to summability
  of `(n+1) * poissonWeight rate n * (u n)^2`.

Both proofs first establish that the actual pointwise operator expression has
an L² realization; positive singleton masses then identify that realization
at every count. The diagonal terms are L² because the input already belongs
to its ambient Hilbert space. Closedness was independently proved in the
preceding P2 submilestone by coordinate-evaluation continuity. No adjoint
identity or graph-core density is assumed. P3 finite-support graph
approximation and P4 exact mutual adjoints remain separate obligations.
P2 verification: complete `lake build` succeeds (4010 jobs), and direct
`lake env lean Foundation/AxiomAudit.lean` succeeds. All 13 new
`PoissonWeightedDomains` declarations and the new weighted almost-everywhere
pointwise lemma depend transitively only on `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or custom axiom appears. The exact two maximal-domain
iff statements and both Poisson reindexing equivalences were checked with
Lean. The two old `Foundation.Adjoint` warnings remain the only build warnings.
## P3 preparation: finite-coordinate truncation boundaries

`Foundation/PoissonTruncation.lean` defines `truncate f N` as the genuine
finite-support restriction to counts below `N`. For `truncate f (N+1)`, the
actual forward difference agrees with the full difference below `N`, equals
`-f(N)` at `N`, and vanishes above `N`. For a truncated field, divergence
agrees with the full expression through `N`, has a single incoming value
`(N+1)u(N)` at `N+1`, and vanishes thereafter. Theorems
`scalar_boundary_sq_tendsto_zero` and
`divergence_boundary_sq_tendsto_zero` show the respective boundary weighted
square masses tend to zero. The divergence result uses precisely the P2
next-count domain moment, not a componentwise Sobolev condition.

**Remaining P3 obligation:** establish simultaneous L² convergence of each
truncation and its operator value, including the series-tail norm estimates.
Vanishing of the isolated boundary terms alone is insufficient to claim graph
convergence. Neither closure equality nor graph-core density is asserted yet.
P3 preparation verification: complete `lake build` succeeds (4011 jobs),
and direct `lake env lean Foundation/AxiomAudit.lean` succeeds. All 10 new
truncation declarations have transitive axioms among `propext`,
`Classical.choice`, and `Quot.sound` only. Lean checked the exact boundary and
vanishing-mass theorem types. This is not a verified graph-core result.
## P3 continuation: ambient L² convergence

Finite-coordinate restrictions converge in genuine scalar and rate-weighted field L² via Mathlib uniform integrability. The same truncation family is used on each side of the operator graph. The difference of a truncated function decomposes into the cutoff of its full difference plus one outgoing boundary atom. This does not yet prove graph convergence: the operator values must be related to the maximal graph and the boundary atom controlled in L².


## P3 complete: exact graph-core closure

Foundation/PoissonGraphApprox.lean proves simultaneous Hilbert convergence of finite-support truncations and their actual operator outputs. The output is the cutoff of the maximal value plus one boundary atom, whose squared norm tends to zero by the exact P2 weighted moment. Thus closure_coreDifference_eq_maximal and closure_coreDivergence_eq_maximal identify both graph closures with their closed maximal pointwise operators. No adjoint equality is assumed in this argument. P4 exact mutual adjoints remains open pending reverse adjoint-domain characterization.


## P4 complete: exact Hilbert adjoints

Foundation/PoissonAdjoints.lean tests arbitrary adjoint graph pairs against each finite-support count basis vector. The Poisson weight recurrence and strict positivity identify the entire adjoint-domain coefficient formula, including count zero. It proves coreDifference.adjoint = maximalDivergence, coreDivergence.adjoint = maximalDifference, and mutual adjointness of the closed maximal operators. These conclusions use P3 graph-core identities; no adjoint domain is assumed. The field Hilbert measure retains the factor rate, which is essential for the unscaled divergence formula.


## P5: bounded non-Gaussian product calculus and polynomial examples

Foundation/PoissonBoundedCalculus.lean proves actual scalar and weighted-field L² membership for bounded count functions. It proves bounded products belong to the maximal difference domain and the genuine closed operator satisfies D(fg)=fDg+gDf+(Df)(Dg) pointwise at every positive-mass atom. This is an explicit restricted multiplication domain; no assertion that arbitrary dom(D) is an algebra is made.

Foundation/PoissonMoments.lean proves every Poisson polynomial moment series converges by a ratio estimate, all real polynomials belong to scalar L², and genuine Poisson integrals satisfy E[N]=λ and E[N²]=λ²+λ. Foundation/PoissonPolynomialExamples.lean then verifies the actual closed-operator equalities δ1=N−λ, D(N−λ)=1, and D((N−λ)²)=2(N−λ)+1; the ordinary differential square chain rule is false. The product theorem covers bounded representatives. Full maximal-domain multiplier characterization, Poisson-process stochastic integration, Clark–Ocone, and martingale representation remain outside this one-site milestone.


## One-site Poisson bounded multipliers on the full maximal derivative domain

`Foundation/PoissonMultipliers.lean` extends P5 from two bounded factors to an
arbitrary `f` in the exact maximal difference domain and a bounded real count
function `g`. It constructs actual scalar and rate-weighted field `Lp` products,
proves pointwise evaluation using positive mass at every Poisson atom, and
proves the estimates `‖g f‖₂ ≤ C ‖f‖₂` and `‖g u‖₂,field ≤ C ‖u‖₂,field`
whenever `|g(n)| ≤ C`. These classes do not depend on the chosen bound or on a
bounded representative of the same Poisson L² class.

The actual maximal derivative of the bounded scalar class of `g` has values
`Dg(n)=g(n+1)-g(n)`, hence `|Dg(n)| ≤ 2C` with no additional hypothesis.
For `f ∈ dom(D)`, the established maximal-domain formula gives
`Sf(n)=f(n+1) ∈ L²(λ μλ)`. Thus `g Df` and `(Sf) Dg` are both in the weighted
field L² space. In particular, the shifted term satisfies the explicit bound
`‖(Sf)Dg‖₂,field ≤ 2C ‖Sf‖₂,field`. Their pointwise sum equals the difference of the scalar
product, so the exact maximal-domain criterion proves `gf ∈ dom(D)`.
`scalarMul_difference_shifted` identifies the actual operator output with the
sum of those two weighted L² classes. Separately, `f Dg`, `g Df`, and
`(Df)(Dg)` belong to weighted L² by the proved bounded-multiplier estimates;
`scalarMul_difference_expanded` proves the full three-term jump rule as an
equality of actual field L² elements. The two forms are mathematically
identical because `Sf=f+Df` pointwise on the maximal domain.

Boundedness of `g` alone suffices here; boundedness of `Dg` follows from the
finite-difference formula. This does not make `dom(D)` an algebra. Indeed,
with `w_n = μλ({n})` and `f(n)=w_n^(-1/4)/sqrt(n+1)`, the ratio test gives
`Σ sqrt(w_n)<∞`, so `f ∈ dom(D)`. Yet `f² ∈ L²(μλ)` because
`Σ w_n f(n)^4=Σ 1/(n+1)^2<∞`, while `f² ∉ dom(D)` because
`Σ n w_n f(n)^4=Σ n/(n+1)^2=∞`. This is a mathematical counterexample,
not a new Lean declaration. No arbitrary-domain product statement, multisite
claim, or Poisson-process integral is inferred.

Verification: the complete `lake build` succeeds (4018 jobs). Direct
`lake env lean Foundation/AxiomAudit.lean` succeeds with 1106 transitive
reports; all 27 new public declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound` or subsets thereof. No `sorryAx`, custom
axiom, `sorry`, `admit`, or unsafe code is present. The two previously known
unused section-variable warnings in `Foundation.Adjoint` remain.

## Poisson bounded-multiplier algebra and commutator

`Foundation/PoissonMultiplierAlgebra.lean` proves bounded count functions are closed under addition and multiplication, that their actual scalar L² multiplication maps add and compose, and that successive multiplication preserves the exact maximal difference domain. For an arbitrary `f ∈ dom(D)` and bounded `g`, `difference_commutator` identifies the actual field-L² commutator `D(gf) − gDf` with `(Sf)Dg`, while `difference_product_shifted_multiplier` proves the alternative genuine field-L² rule `D(gf)=fDg+(Sg)Df`. `difference_product_norm_le` quantitatively bounds the output by `C‖Df‖ + 2C‖Sf‖` in the rate-weighted field norm. Both terms are genuine L² classes, with integrability established in `PoissonMultipliers.lean`.

The shift norm is essential. A claim that the commutator is bounded from ambient scalar L² to the weighted field L² under boundedness of `g` alone is false: take `g(n)=(-1)^n` and normalized singleton scalar vectors at count `N`; their scalar norms equal one, while the commutator output norms grow like `2√N`. Graph-norm boundedness follows from the proved shift decomposition `Sf=f+Df`, but the present module retains the explicit shift norm. This does not assert that the maximal operator domain is an algebra.

## Poisson Lipschitz finite-difference chain rule

`Foundation/PoissonLipschitzChain.lean` constructs the genuine scalar Poisson L² composition by a globally Lipschitz map `φ : ℝ → ℝ` with `φ 0 = 0`. For every `f ∈ dom(D)`, it proves `φ(f) ∈ dom(D)` by bounding its actual jump difference pointwise by `K|Df|`, where `K` is the Lipschitz constant. `composition_difference_apply` identifies the maximal operator at every count:

    D(φ(f))(n) = φ(f(n) + Df(n)) − φ(f(n)).

`composition_difference_norm_le` proves `‖D(φ(f))‖_{L²(rate μ)} ≤ K‖Df‖_{L²(rate μ)}`. The scalar composition is a genuine L² class, and the derivative estimate concerns the actual closed maximal operator. The condition `φ(0)=0` is a sufficient integrability condition used by Mathlib's `LipschitzWith.comp_memLp`; this module does not claim the most general affine-growth version, the ordinary Gaussian chain rule, or a general square-function theorem on the whole maximal domain. The existing `difference_centeredCount_sq_eq` remains a separately proved unbounded quadratic example with the nonzero jump defect.

## Exact Poisson quadratic defect on a verified L² domain

`PoissonQuadraticDefect.bounded_square_difference` proves for every uniformly bounded count function `f` and positive rate that the **actual maximal difference** of its square satisfies `D(f²)=2fDf+(Df)²` as an equality in `L²(ℕ,rate·μ_rate)`. The input square and both right-hand terms are genuine L² classes; domain membership comes from `PoissonBoundedCalculus.bounded_product_mem_maximalDifference` and term integrability from `PoissonMultipliers.fieldMul`. This theorem does not cover every unbounded maximal-domain function. The already verified unbounded centered-count identity `D((N−rate)²)=2(N−rate)+1` is separate and uses explicit Poisson moments.

## B0: bounded Banach Lp adjoint

`Foundation/BanachLpAdjoint.lean` starts the Paper 2 reconstruction with an
actual normed real space `H`, measure `μ`, Hölder-conjugate exponents `q,p ≥ 1`,
and an actual continuous linear map `δ : H →L[ℝ] Lp ℝ p μ`. It defines
`boundedBanachDerivative δ : Lp ℝ q μ →L[ℝ] StrongDual ℝ H` by composing
Mathlib's `ContinuousLinearMap.lpPairing` with precomposition by `δ`.

`integrable_mul` proves that `F · δu` is genuinely integrable. The evaluation
theorem identifies `D F u` with its real integral, `boundedBanachDerivative_norm_le`
gives `‖D F‖ ≤ ‖F‖ ‖δ‖`, and `boundedBanachDerivative_eq_zero_iff` identifies its
kernel with the annihilator of the range of `δ`. On a finite measure,
`boundedBanachDerivative_const_eq_zero` proves that `D` kills Mathlib constant
Lp classes when every `δu` has zero actual integral. These conclusions use no
scalar-Lp dual-surjectivity theorem, Hilbert/Riesz identification, process
construction, or stochastic representation hypothesis.

This bounded construction does not resolve the impossible interfaces in the
legacy Banach source, construct a stable integral, or address unbounded Banach
adjoints. Those remain distinct obligations. The original files and dependency
pins are untouched.

Verification: the full `lake build` passes (4,022 jobs). Direct execution of
`Foundation/AxiomAudit.lean` passes with 1,128 transitive axiom reports. Every
new public declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`; there are no `sorryAx` or custom axioms. The declarations were
also inspected with fully explicit `#check` types. The two unused-section-variable
warnings from the older `Foundation.Adjoint` remain unchanged.

## C2: closed Banach ranges and concrete annihilators

`Foundation/BanachRange.lean` works with the genuine B0 operator
`δ : H →L[ℝ] Lp ℝ p μ` and its actual Hölder adjoint. A positive lower
bound `c‖u‖ ≤ ‖δu‖` proves injectivity. If `H` is complete, it proves that
the actual range is closed and constructs Mathlib's continuous linear
equivalence `H ≃L[ℝ] δ.range`, with `c‖δ⁻¹v‖ ≤ ‖v‖` for range elements.

Independently of any lower bound or completeness, `kernel_iff_annihilates_closure`
identifies `D F = 0` with vanishing of the genuine pairing against the entire
norm closure of `range δ`. A nonzero pairing with such an `F` therefore proves
that a chosen `Lp` element lies outside this closure, hence outside the range.
This is a precise nonrepresentability criterion. It requires an actual witness
`F` and a proved nonzero real integral; none is supplied by the abstract theorem.

These results are conditional functional analysis for an arbitrary concrete
bounded map. They do not construct a Poisson or stable integral, prove the
range is all centered `Lp`, or identify every `Lp` dual functional with `Lq`.

## C1: densely defined Banach adjoints

`Foundation/BanachUnboundedAdjoint.lean` takes a genuine partial linear map
`T : X →ₗ.[ℝ] Y` between real normed spaces and assumes only that its domain
is dense in `X`. The adjoint graph consists of the pairs `(φ,f)` of continuous
linear functionals satisfying `f x = φ (T x)` for every `x ∈ dom(T)`.
It is a closed linear subspace. Density makes its second coordinate unique,
so it defines an actual partial linear map `adjoint T hDense` between the
strong duals. Its graph is exactly that pairing relation and is closed.

The exact domain criterion is an **ambient norm** bound:
`φ ∈ dom(T*) ↔ ∃ C : ℝ, ∀ x ∈ dom(T), ‖φ(T x)‖ ≤ C ‖x‖`.
The forward direction uses the operator norm of the continuous adjoint value.
The reverse direction uses Mathlib's `LinearMap.extendOfNorm` along the dense
domain inclusion, and `adjoint_apply_eq_extension` proves that the constructed
value is precisely this extension. No graph-norm continuity, Hilbert/Riesz
identification, reflexivity, or boundedness of `T` is assumed.

`boundedAsPartial_adjoint_domain` and `boundedAsPartial_adjoint_apply` now
verify compatibility with a genuine bounded map `S : X →L[ℝ] Y`: every
continuous dual input belongs to the partial adjoint domain, and its value is
the ordinary continuous transpose `φ.comp S`. This does not require a general
identification of the dual of `Lp` with another `Lp`.

This result is abstract Banach operator theory, not a stochastic-integral
construction. The theorem `isClosable_of_adjoint_domain_separates` proves a
genuine sufficient condition for closability: the domain of `T*` must
separate points of `Y`. Its proof uses closure of the original graph and
the continuous adjoint pairing; it does not assume the graph is closable.
The reverse criterion and second-adjoint recovery remain to be
formalized. In general, recovering `T` from its Banach
double adjoint requires careful use of the canonical embedding into `X**`
and, for equality in `X`, reflexivity or other sufficient hypotheses.

## C3 first fixed-exponent duality map

`Foundation/BanachLpDualityFour.lean` defines `dualityFour` on actual scalar
Lp classes: `F ∈ L⁴(μ)` maps to the class of `F³` in `L^(4/3)(μ)`.
`cube_memLp` proves this integrability from Mathlib's `MemLp.norm_rpow_div`;
`dualityFour_ae` identifies the representative almost everywhere. The
quartic moment and pairing are genuinely integrable, and
`dualityFour_pairing` proves `∫ (dualityFour F) F = ∫ F⁴`, and
`quartic_integral_eq_norm` identifies this with `‖F‖₄⁴`. The exact conjugate
norm law `‖dualityFour F‖_(4/3) = ‖F‖₄³` is proved independently, including
the zero case. For an actual bounded `δ : H →L[ℝ] L⁴(μ)`, `normalFour`
composes this nonlinear map with the B0 transpose, proving
`normalFour δ u u = ‖δu‖₄⁴`. A genuine lower bound on `δ` gives
`c⁴‖u‖⁴ ≤ normalFour δ u u`. The map is nonlinear and no linear-map
structure or solvability of a normal equation is asserted. The verified
`normalFour_monotone` theorem additionally proves
`0 ≤ (A(u)-A(v))(u-v)` for all `u,v`, using the actual integrable Hölder
pairings and the signed cubic inequality. General `1<p<∞` signed-power
theory, strict monotonicity, continuity, and
normal-equation solvability remain separate obligations at the C3 baseline.

## C4: smooth cube map and quantitative monotonicity

`Foundation/BanachLpDualityFourContinuity.lean` realizes the existing cube
map by Mathlib's genuine continuous Hölder products L4 × L4 → L2 and
L2 × L4 → L(4/3). Its equality with `dualityFour` is proved a.e. The cube
and `normalFour δ` are C∞, hence continuous and locally Lipschitz, for any
measure and any real normed H. No full Lp-dual representation is used.

`normalFour_uniform_monotone` proves
`(Au-Av)(u-v) ≥ ‖δ(u-v)‖₄⁴/4` by integrating the sharp scalar cubic
inequality with established integrability. The actual lower norm bound on δ
gives `normalFour_uniform_monotone_lower`, with constant `c⁴/4`.
`normalFour_injective`, `normalFour_inverse_cubic_bound`, and
`normalFour_inverse_holder_bound` prove injectivity and exponent-1/3 stability
of the inverse relation. They do not assume or conclude surjectivity.

An independent audit of the baseline adjoint and duality modules found no
blocking defect; exact hypotheses and scope qualifications are recorded in
`BANACH_C4_C5_AUDIT.md`. In particular the adjoint-domain separation condition
is substantive, and no stochastic integral or stable lower bound is constructed.

C4 verification: the full Lake build passed (4026 jobs), and the transitive
audit passed for 1187 declarations, including all 17 new public declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur; no `sorryAx` or
custom axioms occur. An independent proof-body and elaborated-type review passed.

## C5: finite-dimensional quartic normal equations

`Foundation/BanachLpDualityFourExistence.lean` proves existence and uniqueness
for the actual equation `normalFour δ u = f`, for every `f : StrongDual ℝ H`,
when H is finite-dimensional real normed and the actual bounded map δ into
L4 satisfies `c * ‖u‖ ≤ ‖δu‖` for some `c > 0`. The measure is arbitrary.
No Hilbert identification, Lp-dual representation, nontriviality, or additional
regularity assumption is used; the zero-dimensional case is included.

`hasFDerivAt_quarticPotential` proves the Fréchet derivative of
`‖δu‖₄⁴/4` equals `normalFour δ u`, by differentiating genuine continuous
Hölder products and the L2 pairing. `exists_quarticPotential_minimizer`
proves a bounded sublevel for `‖δu‖₄⁴/4 - f u`, and obtains a global minimum
using finite-dimensional compactness. The zero-derivative theorem at that
minimum gives `normalFour_surjective`. C4 injectivity then yields
`normalFour_existsUnique` and the actual bijection `normalFourEquiv`.

`normalFour_inverse_solves` proves compatibility of its inverse with the
original normal equation. `normalFour_inverse_cubic` and
`normalFour_inverse_holder` give, for all dual inputs f,g,
`‖A⁻¹f-A⁻¹g‖ ≤ (4/c⁴)^(1/3) * ‖f-g‖^(1/3)`.

The exact theorem statements, proof dependencies, and independent baseline
audit appear in `BANACH_C4_C5_AUDIT.md`. No C4 or finite-dimensional C5
obligation remains. Infinite-dimensional solvability, general exponents,
and construction of a stochastic integral meeting the norm bound are separate.

C5 verification: the full Lake build passed (4027 jobs). The transitive
axiom audit passed for 1196 public declarations; all nine new C5 declarations
and all 17 C4 declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`. No `sorryAx`, custom axioms, or unsafe shortcuts occur.
Independent proof-body and elaborated-type review passed, including a
compiled zero-dimensional instance. Existing verified theorem statements,
original manuscripts, and dependency pins are unchanged.

## C6 prerequisite: complete-space quartic minimization

`Foundation/QuarticUniformMinimization.lean` proves
`exists_minimizer_of_quartic_midpoint`: a continuous bounded-below functional
E on a complete real normed space attains its minimum if
`E((u+v)/2) + k*‖u-v‖⁴ ≤ (E u+E v)/2` for a proved positive k.
The proof chooses an infimizing sequence, proves it norm-Cauchy from this
quantitative deficit, and uses completeness and continuity. It has no
finite-dimensionality, reflexivity, compactness, or assumed-minimizer hypothesis.

`BANACH_C6_REPORT.md` records the actual pinned Mathlib API inspection and
the selected direct proof architecture. Analytic L4 reflexivity and its
closed-subspace transport are not present in the inspected library; algebraic
`Module.IsReflexive` would incorrectly force finite-dimensionality. The C6
application will prove the needed midpoint condition for the actual quartic
energy, avoiding those missing reflexivity prerequisites.

Verification: full Lake build passed (4028 jobs); transitive audit passed
for 1197 declarations, with only `propext`, `Classical.choice`, and
`Quot.sound`. The minimization proof and elaborated type passed independent review.

## C6: complete-space p=4 normal-equation solvability

`BanachLpDualityFourCoercivity` proves a finite global lower bound on
`E(u) = ‖δu‖₄⁴/4 - f u`, and proves
`E((u+v)/2) + (c⁴/64)*‖u-v‖⁴ ≤ (E u+E v)/2`. The latter integrates a
scalar polynomial inequality after proving integrability of every quartic
term; continuous-dual forcing cancels at the midpoint.

`Foundation/BanachLpDualityFourInfinite.lean` applies the general verified
minimizing-sequence theorem. Its `exists_quarticPotential_minimizer`,
`normalFour_surjective`, and `normalFour_existsUnique` prove that every
continuous-dual datum f has a unique solution of the original `normalFour δ u=f`,
under exactly: real normed H, `CompleteSpace H`, an actual continuous linear
δ into L4 of arbitrary μ, `c > 0`, and `∀u, c*‖u‖ ≤ ‖δu‖`.
The argument uses the existing actual quartic Fréchet derivative and Fermat's
theorem. It does not use the old finite-dimensional existence proof.

`normalFourEquiv` constructs the bijection; `normalFour_inverse_solves`
checks the actual equation. The inverse cubic and Hölder estimates retain
the constant `(4/c⁴)^(1/3)`. `lpFour_normal_existsUnique` specializes to the
entire L4 space with δ=id, without a dimension restriction.

Thus C6a holds with the stronger complete-space scope, and explicit reflexivity
is eliminated from the solvability statement. The separate theorem that a
complete H embedded as a closed subspace of L4 is reflexive is not formalized:
pinned Mathlib lacks the relevant L4 bidual-surjectivity and reflexivity
transport infrastructure. This is not a gap in the direct existence proof.
`BANACH_C6_REPORT.md` records exact statements, API sources, and proof dependencies.

C6 verification: full Lake build passed (4030 jobs); transitive axiom audit
passed for 1213 declarations, including all 17 new public declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. Independent
proof-body and elaborated-type review passed, including compiled zero-space
and L4-on-ℕ-counting-measure specializations. Existing theorem bodies,
original manuscripts, pins, and pre-existing untracked documents are unchanged.

## Paper 1 reconstruction: Hilbert representation and natural domains

`Foundation/HilbertRepresentation.lean` replaces the abstract representation
argument's inappropriate L²-algebra interface by actual real Hilbert spaces.
For a linear isometry J, its actual bounded adjoint R=J* is defined everywhere;
RJ=Id, JR is the orthogonal projection onto the closed range of J, and the
residual satisfies a genuine Pythagorean norm identity. Completeness and
isometry prove closed range. If range J=C-perpendicular for a specified closed
subspace C, the represented part is F minus its C-projection, with the exact
centered norm identity. The range equality is the explicit abstract PRP input.

`adjoint_domain_iff_pairing_bound` characterizes the full unbounded adjoint
domain by |inner F (T u)| <= C*norm u on the actual dense domain of T, using
the ambient norm, not the graph norm. The graph-core variant requires genuine
equality T=closure S; ambient density alone is deliberately insufficient.
Density also proves uniqueness of the represented vector.

`predictableAdjoint_eq_projected_adjoint` proves R F=P(delta*F) only for F
in the actual full-adjoint domain, when the dense partial delta genuinely
extends J on the closed subspace P. No arbitrary L² domain membership,
Leibniz identity, or multiplication closure is assumed. This closes the
abstract domain/representation repair in Paper 1 obligations B01/B03;
construction of Brownian predictable integration and its PRP remains separate.

Verification: full Lake build passed (4031 jobs). The transitive axiom audit
passed for all 1231 listed declarations, including all 18 new public declarations;
its union is exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Paper 1 reconstruction: exact unitary adjoint transport

`Foundation/AdjointUnitaryTransport.lean` constructs the actual partial operator
`pullback U T` for a real Hilbert unitary U:K1->K2. Its domain is precisely
the inverse image of dom T, with value T(Uu). The graph, density and closedness
are transported in both directions. For dense T and complete K1,K2, the theorem
`pullback_adjoint_eq` proves equality of actual partial operators
`(T U)* = U^{-1} T*`, including full domain equality. No boundedness of T,
graph-core assumption, or stochastic pairing hypothesis is used.

This proves the abstract operator-transport step of B05. A concrete weighted
L2 unitary and an actual Brownian stochastic-integral realization are separate
requirements; this module by itself proves neither volatility rigidity nor a
stochastic sensitivity formula.

Verification: full Lake build passed (4032 jobs); all 1243 listed transitive
axiom checks passed, including all 12 new public declarations. Only `propext`,
`Classical.choice`, and `Quot.sound` occur.

## Paper 1 reconstruction: genuine Gaussian constant-kernel theorem

`Foundation/FiniteGaussianKernel.lean` proves that a graph pair (f,0) belongs
to the actual closed finite Gaussian gradient exactly when f is a scalar
multiple of the degree-zero tensor Hermite vector. The proof eliminates every
nonconstant coefficient by the verified lowering formula and uses completeness
of the tensor basis. It covers all finite dimensions, including dimension zero.

`Foundation/InfiniteGaussianKernel.lean` proves, for every actual scalar L2
class f of the countable standard Gaussian product,

    (f,0) in graph closedCylindricalDerivative
      iff exists c, f = c almost everywhere
      iff f = integral f almost everywhere.

There is no extra differentiability, cylinder, graph-density or kernel
hypothesis. A zero-gradient pair restricts to each finite-sector weak-gradient
graph; the finite kernel theorem identifies each scalar projection with its
vacuum coefficient. The existing strong convergence of these same projections
identifies f. Conversely, constants belong to the closed graph by lifting the
empty finite sector. The coefficient equals actual Gaussian expectation.

This closes the constant-kernel ingredient of B05 on the constructed canonical
Gaussian model. It does not construct a Brownian time filtration, a predictable
stochastic integral, or sensitivity of that integral to volatility. In
particular it must not be exported unchanged to a probability space containing
extra randomness invisible to the Gaussian derivative.

Verification: full Lake build passed (4034 jobs); all 1257 listed transitive
axiom checks passed, including all 14 new public declarations. Their elaborated
types were separately checked. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. Independent proof review confirmed that this is a theorem
about the full constructed closed operator, not a conditional kernel axiom.

## Paper 1 reconstruction: concrete weighted L2 and adjoint transport

`Foundation/WeightedL2Transport.lean` constructs, for any measure mu and real
measurable sigma nonzero mu-a.e., the actual linear isometric equivalence

    U : L2(sigma^2 dmu) -> L2(dmu),  Uu = sigma*u,
    U^{-1}v = v/sigma.

The a.e. formulas, both inverse identities, genuine L2 integrability and norm
identity are proved. The proof uses Mathlib withDensity integrability and
Bochner integral identities, square norms and mutual absolute continuity.
It permits signed weights and arbitrary measures: no bound on sigma, reciprocal
bound, finite measure, or integrability of 1/sigma is assumed. Integrability of
division follows from cancellation inside the *weighted* square norm.

`Foundation/WeightedAdjointTransport.lean` applies this construction to any
actual dense partial operator T:L2(mu)->X, for a real inner product space X.
The actual weighted operator has domain {u | Uu in dom T} and value T(Uu).
Density and closedness are equivalent to those of T. Its adjoint has exactly
dom T*, and its value is the weighted L2 class (T*F)/sigma, for every
F in dom T*. Equality is proved as an equality of partial operators, not only
of pairings on test functions.

This closes the concrete weighted full-space transport step of B05, and fixes
the doubled-probability-space error of B01 when mu is time-product-probability
measure. The input T is an actual partial operator, but this module does not
identify it as a Brownian divergence or construct its predictable restriction.
The stochastic-volatility rigidity conclusion remains open.

Verification: full Lake build passed (4036 jobs); transitive checks passed for
all 1286 listed declarations, including all 29 new public declarations. Their
elaborated hypotheses and proof bodies were independently reviewed. The axiom
union is exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Paper 1 reconstruction: weighted measurable subspaces

`Foundation/WeightedMeasurableTransport.lean` restricts the constructed weighted
unitary to Mathlib's actual `lpMeas` subspaces for a sub-sigma-algebra m<=m0.
For a measure on m0, an m-measurable real sigma nonzero almost everywhere,
`measurableUnitary` proves an isometric equivalence between the m-measurable
weighted and unweighted L2 classes. The underlying maps are exactly the
previous multiplication/division maps. The forward and reverse membership
statements are proved using multiplication/division measurability and both
absolute-continuity relations, not supplied as preservation assumptions.

This supplies the measurable-subspace part of weighted transport in B05.
Choosing an actual predictable sigma-algebra and identifying its integral
remain separate stochastic obligations. No filtration or stochastic integral
has been assumed or constructed by this module.

Verification after restart: full Lake build passed (4037 jobs), and all 1294
listed transitive axiom checks passed, including the eight new public declarations.
Independent review confirmed the distinct sigma-algebras and correct a.e.
transport. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

## Paper 1 reconstruction: elementary integration with random Gaussian coefficients

`Foundation/GaussianElementaryIntegral.lean` uses the actual finite standard
Gaussian product and polynomials u_i whose variables have indices strictly
less than i in a finite linear order (`IsPastPolynomial`). Define
J(u)=sum_i X_i*u_i, as an actual polynomial and its scalar Gaussian L2 class.
All finite moments, integrability of J(u) and J(u)^2, and representative
formulas are proved. Past dependence proves partial_i u_i=0, so J(u) is the
value of the existing polynomial divergence and its closed extension on u.

Theorems `elementaryIntegral_centered` and `elementaryIntegral_norm_sq` prove
E J(u)=0 and norm(J(u))^2=norm(u)^2. The proof applies the verified Gaussian
Stein identity to actual polynomial products; off-diagonal moments vanish
because later Gaussian coordinates do not occur in earlier coefficients.
No centering, independence of a coefficient from its own increment, isometry,
or divergence identity is supplied as an additional premise.

For every finite subset of the countable coordinate space, four lift theorems
prove exact graph membership in both the existing cylindrical divergence and
the full `hilbertDivergence`, preservation of the norm identity, and centering
of the lifted representative. Thus this is genuine random elementary
integration inside the previously constructed infinite Gaussian model.

Scope: coefficients are past *polynomials*, on ordered independent unit-variance
coordinates, including the empty index case. This is neither arbitrary
anticipating integration nor a Brownian-time integral. Even completion for a
fixed discrete order does not give full centered-L2 representation: the first
coordinate's second Hermite polynomial is orthogonal to the elementary range.
Continuous-time realization, refinement and predictable completion remain
requirements of B03/B05. No new PRP claim is made here.

Verification: full Lake build passed (4038 jobs); all 1314 listed transitive
axiom checks passed, including all 20 public declarations in this module.
Independent proof review confirmed genuine random coefficients and exact
normalization. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

## Paper 1 reconstruction: actual elementary Gaussian sensitivity and rigidity

`Foundation/GaussianElementaryRigidity.lean` proves the actual polynomial
sensitivity formula

    partial_k J(u) = u_k + J(i -> partial_k u_i),

and proves this is both the actual Euclidean Frechet derivative and the value
of the existing closed finite Gaussian gradient. For past polynomial fields,
differentiation preserves past dependence, by a proved inclusion of polynomial
variable sets. No independently prescribed derivative is introduced.

The exact main result is `elementaryIntegral_gradient_eq_coefficients_iff`:
for every finite linearly ordered index type (including the empty type) and
u_i real polynomials in strictly earlier independent standard coordinates,

    (elementaryIntegralL2 u, vectorPolynomialL2 u) in graph closedGradient
      iff exists c : index -> Real, forall i, u_i = C(c_i).

Forward: uniqueness in the actual closed graph identifies the sensitivity
expression, so each derivative-field elementary integral is zero. The already
proved random-coefficient isometry forces the entire differentiated field to
have zero norm. Genuine polynomial evaluation injectivity and the finite
constant-kernel theorem then force each coefficient polynomial to be constant.
Reverse: actual derivatives of constant coefficients vanish, yielding the
closed-gradient graph identity. `elementaryIntegral_rigidity_ae` states the
ordinary almost-everywhere constant representative consequence explicitly.

This is a complete discrete finite Gaussian rigidity theorem supporting B05,
not a conditional cancellation assertion. No positivity, bounded coefficients,
independence of all coefficients, or determinism conclusion is assumed. Its
finite, independent-coordinate, polynomial hypotheses are essential to the
proved scope; it does not establish the manuscript's continuous-time theorem E.

Remaining paper-critical obligations are an actual time-Hilbert Gaussian/
Brownian realization, predictable random integration and its completion,
adapted graph approximation, and sensitivity under the stochastic limit.
The new constant-kernel and weighted-transport theorems can then be applied.
The bracket/Gubinelli counterexamples and the manuscript's universal Ito
claim still require explicit mathematical revision; they are not repaired by
these finite-coordinate results. Original manuscripts and existing theorem
bodies have not been changed.

Final verification: full Lake build passed (4039 jobs); all 1323 listed
transitive axiom checks passed, including all nine declarations of this module.
A separate source-to-audit coverage check found all 110 new public declarations
and no missing audit entry; all 110 explicit `#check @...` elaborated-type
checks passed. The transitive axiom union remains exactly `propext`,
`Classical.choice`, and `Quot.sound`. Source scanning found no admissions,
custom axioms or unsafe declarations in the new modules. Independent review
after recovery from the restart found no mathematical defects, with the scope
qualifications above.

Public-declaration inventory (all exact names are listed in `Foundation/AxiomAudit.lean`):
`HilbertRepresentation` 18; `AdjointUnitaryTransport` 12;
`FiniteGaussianKernel` 5; `InfiniteGaussianKernel` 9;
`WeightedL2Transport` 22; `WeightedAdjointTransport` 7;
`WeightedMeasurableTransport` 8; `GaussianElementaryIntegral` 20;
`GaussianElementaryRigidity` 9. Every module is imported by the project root.

The next smallest paper-critical step is to construct the time-Hilbert
isonormal realization over L2([0,T]), using the existing countable Gaussian
space and an actual proved Hilbert-space coordinate embedding, then define
W_t from interval indicators and prove covariance and independent increments.
This alone would still not prove path continuity, predictable integration,
PRP or stochastic sensitivity. Those are explicit subsequent obligations,
not consequences of the current fixed discrete coordinate isometry.

## Paper 1 time realization: recovered baseline and Hilbert-indexed Gaussian process

Recovery confirmed HEAD `30d3140f569cb7afc642e220a247949f052ae02f`, all seven
previous milestones as ancestors, no tracked changes, and all twelve existing
untracked documents preserved. Repeated baseline verification passed: full
build 4039 jobs; 1323 listed transitive axiom checks with the standard trio.
No previous milestone was restarted or rewritten.

`Foundation/SeparableHilbertEmbedding.lean` constructs a linear isometric
embedding of every complete second-countable real inner product space H into
the existing countable coefficient space. Orthonormal families are proved
countable by metric separation, an actual Mathlib Hilbert basis is chosen,
and the Hilbert sum isometry places its coefficients at distinct natural
indices. No basis or coordinate embedding is supplied as a hypothesis;
zero, finite and infinite dimensional spaces are all covered.

`Foundation/GaussianHilbertProcess.lean` composes this constructed embedding
with the verified first-chaos isometry. `isonormalEmbedding` is an actual
linear L2 isometry and `isonormal` gives its measurable representatives on
the original countable Gaussian product. Theorems prove all finite joint
Gaussian laws, mean zero, law N(0,norm(h)^2), covariance inner(h,k), genuine
integrability of each product, and its expectation. Index linearity holds
in L2 and for each stated pair almost everywhere. It is not asserted
simultaneously pathwise over uncountably many indices.

Scope: the embedding is injective, not asserted onto. The resulting indexed
family need not generate the full ambient product sigma-algebra. No PRP,
Brownian continuity, joint time/sample measurability, or identification of
the ambient derivative with a natural-filtration derivative follows merely
from this construction.

Verification for this milestone: the complete Lake build passed (4042 jobs).
All 1346 listed declarations passed the transitive axiom audit; the union
is exactly `propext`, `Classical.choice`, `Quot.sound`. All six embedding
and seventeen Gaussian-process public declarations are included.

## Paper 1: actual time Hilbert space and pre-Brownian realization

`Foundation/GaussianTimeHilbert.lean` uses actual Lebesgue L2 on the real
line. `intervalVector a b` is the class of the indicator of `(a,b]`;
`timeVector t` is the indicator of `(0,t]` for nonnegative t. Their inner
products are interval intersection lengths. In particular,
`timeVector_inner` gives min(s,t), `timeVector_sub_norm_sq` gives t-s for
s <= t, and `timeVector_increments_orthogonal` handles ordered disjoint
intervals. Empty intervals, touching endpoints and zero time are included.
Completeness and second countability are established using pinned Mathlib.

`Foundation/GaussianTimeProcess.lean` defines `wienerL2` and `process` by
the constructed isonormal embedding of these time vectors into the existing
countable Gaussian product. `process_isPreBrownian` derives all Brownian
finite-dimensional laws from actual joint Gaussianity, centering and the
min covariance, using Mathlib's covariance criterion.
`process_hasLaw` gives N(0,t), `process_increment_hasLaw` gives variance
abs(t-s), `process_hasIndepIncrements` gives mutual independence on every
ordered finite partition, and `process_disjoint_increments_independent`
specializes this to two ordered disjoint intervals. `wienerL2_sub` identifies
the actual increment class with its interval vector. `naturalFiltration`
is the raw natural filtration; `process_stronglyAdapted` is proved for it.

This is a concrete pre-Brownian realization, not a continuous-path Brownian
construction. No joint time/sample measurability, completed or right-continuous
filtration, or PRP is asserted. Whole-line time L2 contains negative-time
directions not seen by these nonnegative-time coordinates. The chosen Hilbert
embedding need not be onto the ambient coefficient space. Neither ambient
Gaussian kernel theorems nor ambient density automatically transfer to the
Brownian natural sigma-algebra.

Verification: full Lake build passed (4051 jobs); all 1384 listed transitive
axiom checks passed, including all 38 new time-Hilbert/process declarations.
The axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`.

## Paper 1: genuine random predictable-step integration

`Foundation/GaussianPredictableStep.lean` proves elementary integration for
an actual `IsPreBrownianReal B μ`. For ordered nonnegative times s <= t,
`pastCoefficient B s a` is a measurable function of the entire coordinate
past, and `stepIntegral B s t a` is literally A*(B_t-B_s).
`pastCoefficient_indep_increment` derives independence from Mathlib's
`IsPreBrownianReal.indepFun_shift`. With A in L2, independence of the squared
factors proves square integrability; general L2-times-L2 closure is not used.
`integral_stepIntegral` and `integral_stepIntegral_sq` prove
E[A*(B_t-B_s)]=0 and E[(A*(B_t-B_s))^2]=(t-s)*E[A^2].

`integral_stepIntegral_mul_stepIntegral` proves cross-term orthogonality for
s <= t <= r <= v and arbitrary L2 coefficients from the respective pasts.
The regrouped past product is L1, not assumed L2. All pairing integrands are
proved integrable. On a monotone finite partition τ, the actual finite sum
`partitionIntegral` is L2 and centered, and `integral_partitionIntegral_sq`
proves E[(sum A_i*(B_{τ_(i+1)}-B_{τ_i}))^2]
= sum (τ_(i+1)-τ_i)*E[A_i^2]. No independence of the coefficients, uniform
bound, or polynomial restriction is assumed. Empty partitions and repeated
times are allowed.

`measurable_natural_iff_exists_pastCoefficient` uses actual measurable
factorization to show that this parametrization covers every real coefficient
measurable for the raw natural filtration. `integral_natural_step_sq` states
the one-step result directly for such coefficients.
`stepProcess_stronglyPredictable` and `partitionProcess_stronglyPredictable`
prove predictability of the actual indicator step processes in Mathlib's
predictable sigma-algebra. They do not assume predictability as a field.

`Foundation/GaussianTimeStepIntegral.lean` specializes to the constructed
Gaussian time process, so its principal results have no assumed Gaussian
realization. `partitionIntegralL2` is an actual scalar Gaussian L2 class;
`partitionIntegralL2_coeFn`, `partitionIntegralL2_centered` and
`partitionIntegralL2_norm_sq` prove its representative, centering and exact
norm formula. `partitionIntegralL2_congr` proves invariance under a.e.
coefficient changes for the same partition. `timeStep_integrable_sq_and_isometry`
covers every L2 coefficient measurable for this concrete natural filtration;
`timeStep_stronglyPredictable` and `timePartition_stronglyPredictable` prove
the associated integrands are genuinely predictable.

Scope: the elapsed-time energy has not yet been identified with a quotient
in time-probability L2. Cross-partition representation independence, density
of steps in the full predictable L2 subspace and continuous extension are
separate obligations. No full predictable stochastic integral, PRP, completed
filtration, or stochastic sensitivity theorem is claimed by this milestone.

Verification: full build passed (4053 jobs). All 1418 listed transitive axiom
checks passed, including the 26 generic and eight concrete public declarations
of this milestone. Only `propext`, `Classical.choice`, `Quot.sound` occur.

## Paper 1: verified polynomial common domain of stochastic integral and divergence

`Foundation/GaussianTimeDivergence.lean` defines actual polynomial coefficients
G=p(B_(r_i)) and the coefficient-space direction e(1_(s,t]), where e is the
constructed isometry from time L2 to ell2. All finite moments of G and
G*(B_t-B_s) are proved independently of the ordering hypotheses.
For r_i <= s <= t, `pastDirection_inner_increment` computes zero inner
product and `pastCoefficient_gradient_inner_increment` derives zero
contraction from the genuine polynomial derivative formula.
`rankDivergence_pastCoefficient` then proves
delta_0(G*e(1_(s,t]))=G*(B_t-B_s) in actual Gaussian L2.
`pastCoefficient_cylindricalDivergence_graph` and
`pastCoefficient_hilbertDivergence_graph` give both domain membership and
the exact value in the existing operators. The corresponding `sum` theorems
prove this for finite fields. Overlapping intervals are allowed in these
graph identities; no orthogonality/isometry is asserted for overlapping steps.
Past coordinates may be repeated, correlated or linearly dependent.

`Foundation/GaussianTimePolynomialIntegral.lean` joins this graph formula to
the actual stochastic-integral construction. `polynomialPastFunction_measurable`
and `polynomialPastFunction_memLp` prove the coefficient hypotheses, rather
than supplying integrability as a new assumption.
`polynomialPartitionIntegralL2` is the previously constructed predictable
increment integral specialized to those coefficients.
`polynomialPartitionIntegralL2_eq_sum` proves its equality with the sum of
the genuine product classes. Theorems
`polynomialPartitionIntegralL2_cylindricalDivergence_graph` and
`polynomialPartitionIntegralL2_hilbertDivergence_graph` identify this exact
value in the existing operator graphs. Their only mathematical inputs are
a finite polynomial coordinate index, monotone finite partition, polynomial
coefficients and sampling times at or before the left endpoints. Empty
coordinate sets/partitions and repeated times are allowed. The same value
satisfies the elapsed-time norm formula in
`polynomialPartitionIntegralL2_norm_sq`. Calling this a polynomial test class
does not assert a graph-core or predictable-density theorem.

`Foundation/GaussianTimeFieldNorm.lean` further identifies the actual
embedded vector-L2 norm. `scalarTensor_pair_inner` factors the pairing of
two rank-one fields, `partitionDirection_inner_eq_zero` proves orthogonality
of distinct interval directions, and `partitionField_norm_sq` gives
norm(sum A_i*e(1_(τ_i,τ_(i+1)]))^2 = sum (τ_(i+1)-τ_i)*norm(A_i)^2
for arbitrary scalar Gaussian L2 classes A_i. Adaptation is not needed for
this deterministic direction calculation. For the polynomial past fields,
`polynomialPartitionIntegralL2_norm_sq_eq_field` and
`polynomialPartitionIntegralL2_norm_eq_field` prove the actual vector-L2
Itô isometry: the constructed integral and its embedded field have equal
norms. This is stronger than a merely formal elapsed-time expression, but
does not identify arbitrary time-probability L2 quotients with these fields.

The operator here is the existing ell2-valued Gaussian divergence applied
to the explicitly embedded time directions. It is not a newly constructed
adjoint on all time-probability L2, nor a claim that every predictable L2
integrand is in this domain.

### Reuse investigation and exact next boundary

Pinned Mathlib supplies the Gaussian covariance criterion, increment laws,
independence from the entire past, natural filtrations and predictable
sigma-algebra used above. No dependency was added or changed.

Public reusable developments do exist. The inspected
[BrownianMotion source](https://github.com/RemyDegenne/brownian-motion/blob/master/BrownianMotion/Gaussian/BrownianMotion.lean)
constructs continuous modifications through
`IsPreBrownianReal.exists_continuous_modification` and `isBrownianReal_mk`;
its Kolmogorov--Chentsov prerequisites are not all in this repository's pin.
[MathFin's ItoIntegralCLM](https://github.com/formal-applied-math/formal-mathfin/blob/main/MathFin/Foundations/ItoIntegralCLM.lean)
constructs `itoIntegralCLM_T`, proves `simpleAssembly_T_denseRange` and
`itoIntegralCLM_T_norm`, using a predictable-rectangle density argument.
These are actual constructions, not just postulated isometry fields.
Their inspected toolchains are Lean 4.33.0-rc1, with a different Mathlib
revision; our toolchain remains 4.34.1 and Mathlib remains
`d13f23b723b8a846827a245b89c10fc7d3f11612`. A future selective port requires
checking the extra simple-process/predictable and continuity dependencies,
and preserving their licenses. No upstream source was copied in this run.

The next smallest substantial milestone is finite-horizon predictable L2
assembly: realize the indicator steps as classes for dt-times-probability,
prove their actual norm equals the partition energy, prove common-refinement
compatibility, and construct the isometry on their span. Only after a proved
density theorem may it be extended to the full predictable L2 domain.
The raw-natural versus completed-filtration representative issue must also
be addressed explicitly. Continuous modification is a separate supporting
development, with an existing upstream proof to inspect for a selective port.

The continuous stochastic-volatility rigidity theorem remains open. Beyond
integral completion it needs the correct terminal measurable subspace,
the derivative/time-direction identification, an actual Hilbert-valued
stochastic integral, and adaptation-preserving approximation in the relevant
derivative graph norm. These are needed to pass the genuine sensitivity
formula through closed operators. Ambient L2 density and the existing
ambient constant-kernel theorem do not discharge them. No stochastic
sensitivity limit, determinism conclusion, PRP, or manuscript correction
has been asserted or implemented here. This is the stopping boundary for
this run: those bridges require substantial new verified infrastructure.

Final verification for this milestone: full Lake build passed (4056 jobs).
All 1451 listed transitive axiom checks passed, including the 33 public
declarations in the divergence, polynomial-integral and field-norm modules.
Across the run, all 128 new public declarations are explicitly included in
`Foundation/AxiomAudit.lean`; their elaborated types and proof bodies were
checked. Independent mathematical reviews found no hidden realization,
integrability or graph-domain assumptions in these new results. The axiom
union remains exactly `propext`, `Classical.choice`, `Quot.sound`.
No admissions, custom axioms or unsafe proof shortcuts were introduced.
Original-source SHA256 hashes still match the recovered baseline; original
manuscripts, existing Lean proof bodies, dependency pins and all twelve
pre-existing untracked reports remain unchanged. Nothing was pushed.

## Paper 1 continuation: product-measure fields and cross-partition isometry

Recovery started at `d3f27db51ae3e0cf78330597f62f7c5eb08d0df0`, rather than
the older `30d3140` named in the restart request. All seven named historical
milestones and the four later Gaussian time-realization milestones are
ancestors of that HEAD. No tracked work was missing or modified; the twelve
pre-existing untracked reports were preserved. The recovered baseline passed
the complete Lake build (4056 jobs) and 1451 transitive axiom checks.

`Foundation/GaussianTimeProductL2.lean` constructs actual classes in
`Lp ℝ 2 (volume.prod gaussianProduct)`. `productTensor_memLp` proves square
integrability of h(time)*A(sample) for arbitrary separate L2 classes, using
product integration. `productTensor_inner` proves the factorization of their
pairings. `partitionL2_coeFn`, `partitionFunction_memLp` and
`partitionFunction_sq_integrable` justify the pointwise half-open interval
step function. `partitionL2_norm_eq_field` identifies its actual product-L2
norm with the existing embedded ell2-valued field norm. For monotone finite
partitions, `partitionL2_norm_sq` gives sum_i (t_(i+1)-t_i)*norm(A_i)^2.
No coefficient boundedness or adaptation is needed for these tensor facts.
Empty partitions and repeated endpoints are included.

`Foundation/GaussianTimePolynomialPairing.lean` proves
`incrementProduct_inner`: for G=p(B_(r_i)) with r_i <= s <= t and
H=q(B_(v_j)) with v_j <= a <= b, the pairing of G*(B_t-B_s) and
H*(B_b-B_a) equals the pairing of their actual embedded vector fields.
Intervals may overlap, coordinate index types may differ, and no common
partition is assumed. The proof orders s and a, applies the previously
verified Gaussian Stein identity to G*H*W(h), and uses the actual polynomial
derivative/product rule. Both coefficient derivatives vanish along the later
interval direction. All products have established finite Gaussian moments.

`elementaryTimeGraph` is the algebraic span of these genuine field/integral
pairs. `elementaryTimeGraph_pairing` and `elementaryTimeGraph_norm` extend
the isometry to arbitrary finite linear combinations by two-variable span
induction. `elementaryTimeGraph_le_cylindricalDivergence_graph` and
`elementaryTimeGraph_le_hilbertDivergence_graph` prove agreement with the
existing operators, including their domains. Thus a vanishing field assembly
has a vanishing integral assembly; no decomposition independence is assumed.

These results do not identify a full predictable L2 domain, assert continuous
sample paths, or prove continuous-time stochastic-volatility rigidity. They
remove the finite-step assembly and cross-partition pairing obstruction
without changing the existing operators, manuscripts, or dependency pins.

Verification of this increment: complete Lake build passed (4058 jobs);
all 1480 registered transitive axiom checks passed, including all 29 public
declarations of these two modules. Elaborated types were inspected. The
axiom union remains `propext`, `Classical.choice`, `Quot.sound` only.

## Paper 1: constructed integral on the closed polynomial time-field span

`Foundation/GaussianPolynomialStepCompletion.lean` defines
`elementaryFields` as the field-component image of `elementaryTimeGraph`,
and `completedFields` as its closure in the existing Gaussian vector L2.
These are explicit domains, not names for an unproved full predictable space.

`fieldAssembly_dense` and `integralAssembly_norm` prove the hypotheses for
Mathlib's `LinearMap.extendOfIsometry`, constructing
`completedIntegral : completedFields →ₗᵢ[ℝ] GaussianL2`.
`completedIntegral_assembly` proves exact agreement with every elementary
integral assembly, and `completedIntegral_norm` is the actual Itô isometry
on the completed domain. The construction assumes neither an integral
extension nor a graph-density property.

`completedIntegral_graphClosure` proves that every completed field/integral
pair is in the elementary graph closure. The existing full Gaussian
divergence is closed, so `completedIntegral_hilbertDivergence_graph`,
`completedFields_le_divergence_domain` and `completedIntegral_eq_divergence`
establish actual domain membership and the exact divergence value.
The explicit membership argument in the last theorem is redundant but
allows evaluation at any proof of membership; membership is already proved
for every element of the domain.

`completedOperator` packages this constructed integral as a partial linear
operator with domain exactly `completedFields`. `completedOperator_graph`
proves equality with the elementary graph closure in both directions;
`completedOperator_isClosed` and `completedOperator_le_divergence` follow.
Finally `exists_elementary_graph_approx` produces a SINGLE sequence of
finite elementary graph pairs converging simultaneously to the field and
its integral. Thus the elementary graph is a proved graph core for this
restricted completed operator. It is not claimed to be a core for the
entire divergence on arbitrary anticipative fields.

Independent proof review checked the construction and both graph-inclusion
directions. The remaining full-predictable-space identification needs
time-product L2 transport, density of predictable rectangles, and polynomial
cylinder density within each past sigma-algebra. Ambient Gaussian polynomial
density does not alone preserve adaptation. Continuous-time sensitivity
and rigidity additionally require approximation in the derivative graph
norm; the integral graph approximation here does not supply that theorem.

Verification: complete Lake build passed (4059 jobs); all 1499 registered
transitive axiom checks passed, including the 19 public declarations of this
module. Their elaborated types were inspected. Only `propext`,
`Classical.choice`, `Quot.sound` occur. No prior proof body or pin changed.

## Paper 1: integral completion in the actual time-probability L2 space

`Foundation/GaussianPredictableL2Completion.lean` constructs
`closedProductSteps`, the closure in `Lp ℝ 2 (volume.prod gaussianProduct)`
of the span of the actual functions 1_(s,t](x)*p(B_(r_i)(omega)), with
finitely many r_i <= s <= t and nonnegative times. Its definition contains
no integrability, isometry, domain-preservation or full-density assumptions.
All tensor classes and all generator hypotheses come from the previously
verified concrete construction.

`transportRelation_vector_image` proves equality of the corresponding
vector-field image with `elementaryFields`. `transportRelation_pairing`
and `transportRelation_norm` prove preservation of the pairings and norms
on the actual algebraic relation. In particular both assemblies have the
same kernel, so distinct finite decompositions give the same field and
integral classes. Both assembly dense-range statements are proved.

Using these results, `productToField` is a constructed SURJECTIVE linear
isometry equivalence from `closedProductSteps` to `completedFields`.
`productToField_assembly` and `productToField_step` prove that it retains
the concrete tensor interpretation. Composing it with the proved completed
integral defines `productIntegral : closedProductSteps →ₗᵢ[ℝ] GaussianL2`.
`productIntegral_norm` is the actual product-measure Itô isometry, and
`productIntegral_step` identifies every generator's value with the genuine
coefficient-times-increment class. Linearity extends this identification
to finite sums. `productIntegral_hilbertDivergence_graph` proves domain
membership and the identical full-divergence value of every transported
completed field. Independent read-only review checked the quotient,
surjectivity, and graph arguments.

`hilbertDivergence_graph_centered` proves that every actual full-divergence
value has mean zero by pairing against the previously verified constant-one
closed-derivative graph pair. `productIntegral_integrable` and
`productIntegral_centered` consequently establish genuine integrability and
zero expectation throughout the new completed product-space domain.

### Exact remaining boundary toward full predictable integration and rigidity

The two closed polynomial spans are now identified. The next unresolved
claim is their equality with ALL square-integrable predictable processes,
not a claim about completeness of these spans. Pinned Mathlib already has
`MeasureTheory.lpMeas`, `isClosed_aestronglyMeasurable`,
`lpMeasToLpTrimLie` and `Lp.induction_stronglyMeasurable` in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/AEMeasurable.lean`.
These should be reused rather than introducing another measurable L2 space.

Two bridges remain necessary. First, `timeProbability` uses real time and
our generators vanish at negative times, whereas the existing predictable
sigma-algebra is for the natural filtration indexed by nonnegative reals.
A proved nonnegative-time identification/zero extension, including the
null time-zero slice, is needed for the precise ambient-space statement.
Second, density of predictable rectangles and approximation of each
past-measurable coefficient by polynomials in finitely many PAST coordinates
must be proved. The ambient Gaussian polynomial-density theorem does not
provide the latter adaptation-preserving restriction automatically.

The integral graph core proved above does not approximate the Malliavin
derivative of the integrands. The continuous sensitivity identity still
needs its own derivative-domain estimates and adaptation-preserving graph
approximation, as well as the correct terminal measurable subspace and
time-direction derivative identification. No equality of the ambient
Gaussian sigma-algebra with the Brownian terminal sigma-algebra, continuous
modification, martingale representation, predictable representation, or
continuous-time volatility rigidity follows from this milestone.
Original bracket, Gubinelli and stochastic Ito claims are unchanged.

Verification of the product-space completion: complete Lake build passed
(4060 jobs); all 1524 registered transitive axiom checks passed, including
all 25 public declarations in this module. All new elaborated types were
inspected, and the axiom union is still exactly `propext`, `Classical.choice`,
`Quot.sound`. All eleven recovered milestone commits remain ancestors.
The original Lean/TeX SHA256 hashes match the baseline; dependencies and
the twelve unrelated untracked documents remain untouched. Nothing pushed.

## Paper 1: actual polynomial time-integral sensitivity, including a nonzero example

`Foundation/GaussianTimeSensitivity.lean` supplies a first concrete
continuous-time-indexed sensitivity milestone on the polynomial domain.
For A = p(B_(r_i)) and s <= t, `incrementProductPolynomial_eq` identifies
the actual polynomial-domain product A*W(e(1_(s,t])) with the already
constructed `incrementProductL2`. Thus domain membership is proved in
`incrementProduct_mem_polynomialDomain`, not postulated.

`incrementSensitivity` is the genuine polynomial-times-derivative L2 class,
not prescribed extra derivative data. `incrementSensitivity_coeFn` proves
its representative is (B_t-B_s)*D A, and
`incrementSensitivity_fun_memLp` establishes every finite Lq moment of that
integrand. The genuine polynomial Leibniz theorem then proves
`incrementProduct_cylindricalDerivative_graph` and
`incrementProduct_closedDerivative_graph` with exact value

    D(A*(B_t-B_s)) = A*e(1_(s,t]) + (B_t-B_s)*D A.

These differentiation statements hold even without past measurability of
A; the previously established predictable-integral interpretation uses
r_i <= s. `sum_incrementProduct_closedDerivative_graph` retains the sum
of all sensitivities for arbitrary finite families of intervals, including
overlaps. `polynomialPartitionIntegralL2_closedDerivative_graph` specializes
the formula to the EXISTING constructed predictable integral on a monotone
finite partition, with sampling times in each left endpoint's past. It
proves both membership in the closed derivative domain and the exact value.

The concrete example A=B_a, 0<a<b, is not subject to cancellation.
`incrementSensitivity_X` identifies its correction with
(B_b-B_a)*e(1_(0,a]). `incrementSensitivity_X_norm_sq` proves its actual
Gaussian vector-L2 squared norm equals a*(b-a), and
`incrementSensitivity_X_ne_zero` proves it is nonzero for 0<a<b.
Consequently `incrementProduct_X_not_originalField_graph` proves that the
pair (B_a*(B_b-B_a), B_a*e(1_(a,b])) is NOT in the actual closed derivative
graph. This rules out erasing the extra sensitivity merely from
predictability, integral isometry, or agreement with the divergence.

This is a finite-polynomial sensitivity result for the constructed time
process. It does not assert that arbitrary completed integrals belong to
the derivative domain, that sensitivity passes to limits, or that a
predictable projection of a derivative determines its full derivative.
The next substantive dependency remains adaptation-preserving graph
approximation. Before that, a focused reusable milestone is polynomial
density in the measurable subspace generated by a finite family of Gaussian
time coordinates, allowing repeated times and time zero. Finite-dimensional
span/orthonormal-basis reduction can reuse the verified correlated-cylinder
and polynomial-density results without assuming nonsingularity. Passing to
the full past sigma-algebra and predictable rectangles remains subsequent
work. Full continuous-time stochastic-volatility rigidity is still open.

Final verification: complete Lake build passed (4061 jobs). All 1541
registered transitive axiom checks passed; the 90 new public declarations
across these five modules each have explicit audit entries. Their elaborated
types were inspected. Only `propext`, `Classical.choice`, `Quot.sound` occur;
no admissions, custom axioms or unsafe shortcuts were added. The original
manuscripts and dependency pins remain unchanged, and all pre-existing
verified theorem bodies and twelve unrelated untracked reports are preserved.
This run stops at the proved completion and finite-polynomial sensitivity
milestones: identifying the full predictable domain and passing sensitivity
through adapted derivative-graph limits require the substantial bridges
specified above. No rigidity theorem has been manufactured or inferred from
integral isometry. Nothing was pushed.

Independent read-only mathematical review of the sensitivity module also
passed: it checked the underlying moment estimates, actual polynomial
product rule, old integral-class identification, norm calculation, and
single-valued-graph contradiction in the nonzero example. No hidden
projection or extra domain assumption was found.

## Paper 1: finite Gaussian observation density, including singular covariance

Recovered HEAD for this continuation is
`2626f39b53312734005b3d2dd85da08560453ce4`. The four preceding milestones
are intact ancestors, the baseline build passes (4061 jobs), and all twelve
unrelated untracked documents are preserved. Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` remain pinned.

`L2GeneratedSubspace.lean` proves `exists_L2_pullback` and
`L2_pullback_range`: for any measure-preserving observation map X, actual
L2 pullbacks exhaust Mathlib's independently defined `lpMeas` subspace for
the sigma-algebra generated by X. Doob--Dynkin is applied to strongly
measurable representatives, and L2 integrability is transferred through
the actual observation law. Neither injectivity nor nondegeneracy is
required. `aestronglyMeasurable_comap_of_ae_factor` justifies changing
observations through a measurable factorization holding only almost
everywhere. `exists_L2_pullback_approx` transfers a proved source density.

`FiniteGaussianObservationDensity.lean` proves
`exists_isonormalPolynomial_approx`: for ANY finite family h_i in ell2,
every scalar Gaussian L2 class F that is a.e. strongly measurable with
respect to sigma(W(h_i)) and every epsilon>0 admit a polynomial p in the
SAME observations with norm(F-p(W(h_i)))<epsilon. There is no covariance
inverse, independence, distinctness, rank or nonzero-vector assumption.
`isonormalPolynomial_closure` proves equality of the polynomial range's
closure with that generated measurable L2 subspace, not with a subspace
defined to be its own closure.

The proof passes through the finite Hilbert span of the original directions,
uses its orthonormal basis, the previously verified finite Gaussian law and
independent-coordinate polynomial density, then expresses basis directions
as finite linear combinations of the original h_i.
`isonormalCylinderL2_linear_substitution` proves that polynomial substitution
gives the same actual L2 class. All observation transports are justified
almost everywhere. Empty families and zero-dimensional spans are included.

`GaussianTimeObservationDensity.lean` specializes the theorem to the actual
process and old `pastCoefficient` classes. `exists_observationPolynomial_approx`
and `observationPolynomial_closure` allow arbitrary finite nonnegative
observation times, including zero, repetitions and any finite-horizon
restrictions. `observationSigma_le_natural` proves the generated sigma-algebra
lies in the raw natural filtration whenever each observation is at or before
the stated time. This milestone alone does not prove density in the entire
Brownian past or in full predictable L2, nor any derivative graph density.

Verification: complete Lake build passed (4064 jobs); all 1555 registered
transitive axiom checks passed, including all 14 public declarations in the
three new modules. Exact elaborated types were inspected. Only `propext`,
`Classical.choice`, `Quot.sound` occur. No original theorem body or pin changed.

## Paper 1: density in the full Brownian past

`GaussianGeneratedDensity.lean` extends finite-observation density to the
sigma-algebra generated by ANY family h:I→ell2 of actual first-chaos
coordinates. The index type I may be uncountable and the family may be
dependent. `familyPolynomialEmbedding` uses ordinary finite-support
multivariate polynomials. `familyPolynomial_closure` identifies the closure
of its range with the independently defined generated `lpMeas` subspace.

The proof first uses the verified finite density theorem to show an
orthogonal vector has zero integral over every finite observation cylinder.
`familyPolynomial_orthogonal_measurable_zero` then uses the cylinder pi-system
and a pi-lambda argument inside the observation sigma-algebra. It applies
Mathlib's uniqueness theorem for a.e. measurable Lp classes; the ambient
Gaussian sigma-algebra is not substituted for the generated one. Hilbert
orthogonal decomposition finishes the exact closed-subspace equality.

`GaussianTimePastDensity.pastPolynomial_closure` specializes this result to
ALL observation times in Iic s and the actual `naturalFiltration s`.
`exists_pastPolynomial_approx` produces one polynomial in finitely many
times at or before s approximating any past-measurable Gaussian L2 class.
`exists_fin_pastPolynomial_approx` gives the same theorem with Fin n indices,
matching the existing predictable-step generators; reindexing is proved
by `pastCoefficient_equiv`. No continuity of sample paths, countable-time
generation, covariance nonsingularity or completed-filtration equality is
assumed. Time zero is included without an extra hypothesis.

This proves FULL RAW BROWNIAN-PAST coefficient density. It is still separate
from density of predictable rectangles in time-probability L2, and from
adaptation-preserving derivative graph approximation.

Verification of this milestone: full Lake build passed (4066 jobs); all 1568
registered transitive axiom checks passed, including all 13 new public
declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
The elaborated types retain arbitrary coordinate families and actual
natural-filtration measurability, with no density hypothesis.

## Paper 1: arbitrary L2 past steps in the existing completed integral

`Foundation/GaussianPastStepCompletion.lean` uses the full-past density theorem
to prove `past_step_mem_closedProductSteps`: for s,t:NNReal with s<=t and
A:GaussianL2 a.e. strongly measurable for `naturalFiltration s`, the actual
product-space class `productTensor (intervalVector s t) A` belongs to the
PREVIOUSLY defined `closedProductSteps`. There is no boundedness, polynomial,
Malliavin-domain or derivative hypothesis on A. `productTensorLinear`,
`productTensor_norm`, and `productTensorContinuous` prove the needed continuity
from product integration. `past_partition_mem_closedProductSteps` gives the
corresponding result for any finite monotone partition and L2 past coefficients;
empty partitions and repeated partition times are permitted.

`past_increment_sq` extends the existing independent-increment square estimate
from genuinely measurable coefficients to a.e. past-measurable L2 classes, by
choosing a measurable version and proving a.e. equality. It proves BOTH actual
integrability of [A(B_t-B_s)]^2 and its integral `(t-s)*integral A^2`.
`past_increment_memLp` then constructs the actual L2 product `pastIncrement`.
`pastIncrement_norm` proves
`norm(pastIncrement s t A) = norm(intervalVector s t)*norm A`;
the interval norm squared is t-s. `pastIncrement_sub` verifies the actual
difference of product classes, with the correct a.e. measurability of Lp
subtraction. These facts do not assert multiplication of arbitrary L2 classes.

`pastStep` and `pastPartition` place these actual fields into the existing
closed domain. They do not define a replacement stochastic integral.
`productIntegral_pastStep` identifies the existing `productIntegral` with
`pastIncrement` by full-past polynomial approximation and the two proved norm
estimates. `productIntegral_pastStep_coeFn` states the actual a.e. formula.
`productIntegral_pastPartition_coeFn` gives the finite increment sum
`sum_i A_i*(B_(tau_(i+1))-B_(tau_i))`, with exactly the same L2 past hypotheses.
The previous `productIntegral_norm`, `productIntegral_integrable`,
`productIntegral_centered`, and `productIntegral_hilbertDivergence_graph` apply
to these new domain elements unchanged. The last graph statement uses the
previously constructed isometric vector transport `productToField`.

### Exact boundary and next paper-critical obligations

1. FULL PREDICTABLE L2 DENSITY IS STILL OPEN. Pinned Mathlib's
   `Mathlib/Probability/Process/Predictable.lean` defines
   `Filtration.predictable` on NNReal x Omega, generated by `{0} x A` and
   `(s,infinity) x A`, A measurable at s. It provides
   `measurableSet_predictable_Ioc_prod`, but does not in that module provide
   the needed predictable L2 rectangle-density theorem. The project's actual
   `timeProbability` is real Lebesgue time x Gaussian probability. A proof must
   transport the measure and measurable structure under NNReal coercion,
   identify zero extension to negative real times and handle the null time-zero
   slice. The general `measurePreserving_subtype_coe` and
   `Lp.induction_stronglyMeasurable` are reusable APIs; neither alone proves this
   identification. On finite horizons one can then prove indicator/rectangle
   density by a monotone-class argument, followed by L2 horizon truncation.
   This is a substantial next bridge, not a consequence of coefficient density
   alone. No equality with the full predictable L2 space is claimed here.
2. ADAPTATION-PRESERVING MALLIAVIN GRAPH APPROXIMATION IS STILL OPEN. The new
   approximations control coefficients, product fields and their bounded
   stochastic integrals. They provide no bound or convergence for the full
   unbounded derivative of those integrals or the sensitivity correction.
   The finite polynomial sensitivity theorem cannot be passed to this limit
   using L2 density alone. A two-variable adapted derivative core and a proved
   correction estimate are still needed for the intended regular volatility
   class.
3. CONTINUOUS-TIME STOCHASTIC-VOLATILITY RIGIDITY IS STILL OPEN. It requires
   the previous graph bridge, actual sensitivity identities with justified
   domains/versions, and the constant-kernel argument. Existing finite
   polynomial rigidity is preserved and is not promoted to this claim.

All measurability conclusions here refer to the raw natural filtration of the
constructed Gaussian time process, with a.e. representatives handled in L2.
No equality of a usual augmented filtration or of a continuous modification's
filtration is silently substituted. No original manuscript changes are made.

Verification: the complete Lake build passed (4067 jobs). All 1587 registered
transitive axiom checks passed, including all 19 declarations in the new step
module and all 46 declarations added across the three density/domain milestones.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. Every new public
declaration's elaborated type was checked; explicit measurable-space arguments
in the main step theorems were inspected. No new-module warnings remain.
Manuscript/source SHA256 checks match the baseline, dependency pins are unchanged,
and the twelve unrelated untracked documents were preserved.

## Paper 1: finite-horizon predictable transport and genuine generator density

`PredictableTimeTransport.timeMeasure T` is real Lebesgue measure restricted
to [0,T], pulled back under NNReal coercion. `coe_measurePreserving` and
`coeTime_measurePreserving` prove the actual pushforward laws. The latter uses
the product with any finite measure on the probability space.
`realTime_product_restrict` identifies the target with restriction of the real
time-product measure. `L2Equiv` is a SURJECTIVE linear isometry between the two
actual L2 spaces; surjectivity follows from the measurable embedding and the
proved measurable-factorization theorem. `L2Equiv_coeFn`, `L2Equiv_norm`,
`L2Equiv_integrable`, and `L2Equiv_integral` give the actual representative,
norm, integrability and integral statements. `coeTime_preimage_Ioc` verifies
the half-open interval convention exactly. `timeZero_slice_null` and
`timeMeasure_horizon_zero` handle time zero and horizon zero explicitly.

`L2GeneratingIndicators.lean` defines `Foundation.generatingIndicatorSpan`:
for a finite measure, the closure of
indicators of a pi-system S containing univ equals the independently defined
L2 measurable subspace for generateFrom S. `generatingIndicatorSpan_closure`
proves this by orthogonality, finite-measure integrability, pi-lambda induction
and uniqueness of measurable Lp classes; it assumes neither density nor graph
approximation. Its exact hypotheses include generateFrom S = m and m <= m0.

`PredictableGeneratingDensity.generators` is precisely Mathlib's predictable
generator family ({0} x A at time zero, (s,infinity) x A for A measurable at s),
with univ adjoined. `generators_generate`, `generators_isPiSystem`, and
`predictable_le_product` prove generation, intersection closure and ambient
measurability separately. `predictable_indicator_density` then proves full
predictable L2 density of their indicator span for timeMeasure T x mu, for
ANY NNReal filtration and finite mu. It includes T=0. It is a genuine density
theorem, not just a measurability or self-closure assertion.

The filtration remains raw. This milestone does not yet identify the existing
real-time `closedProductSteps` with full predictable L2. The next step is
norm-preserving zero extension and checking the images of these generators
against the already proved arbitrary-past-step domain theorem. No Malliavin
graph density, sensitivity limit, rigidity or operator-functional Ito formula
is inferred from this ambient predictable L2 density.

Verification: full Lake build passed (4070 jobs); all 1609 transitive axiom
checks passed, including all 22 new public declarations. Every new elaborated
type was inspected. Axioms: only propext, Classical.choice, Quot.sound.

## Full finite-horizon predictable integration (2026-10-12)

`L2ZeroExtension.lean` constructs zero extension from a restricted measure as a linear L2 isometry, with actual representative and indicator formulas. `PredictableRealL2.lean` defines the real-time predictable sigma-algebra as the pullback of Mathlib's NNReal predictable sigma-algebra under `(t,omega) -> (t.toNNReal,omega)`. The finite-horizon measure is Lebesgue times Gaussian probability restricted to `(0,T] x Omega`. Its equality with the `[0,T]` product restriction, and both directions of measure-preserving time transport, are proved. This is the raw natural Brownian filtration; no usual augmentation is asserted.

`GaussianPredictableHorizon.zeroExtension_mem` proves that EVERY L2 class measurable for this finite-horizon predictable sigma-algebra belongs, after zero extension, to the PREVIOUS `closedProductSteps`. The proof uses the new pi-system L2 density theorem and the earlier inclusion of arbitrary square-integrable past steps. It does not define predictable fields by a polynomial closure. `PredictableDomain`, `horizonEmbedding`, and `itoIntegral` expose the full finite-horizon class and the SAME existing `productIntegral`. Its norm, centering, and actual `hilbertDivergence.graph` membership are proved. `nonnegativeEmbedding` supplies direct access from Mathlib's NNReal predictable L2 class.

The full infinite-horizon domain equality remains the next obligation. No Malliavin graph density or sensitivity extension follows from this ambient L2 density. All 36 new public declarations, including the finite-measure instance, have explicit-type checks and transitive axiom checks. Full build: 4073 jobs. Complete audit: 1645 checks; only `propext`, `Classical.choice`, `Quot.sound`.

## Full predictable domain identification and integral (2026-10-12)

### Exact statements

`GaussianPredictableFull.fullPredictable` is the intersection of (i) Mathlib `lpMeas` for the pullback of `GaussianTimeProcess.naturalFiltration.predictable` under `(t,omega) -> (t.toNNReal,omega)`, and (ii) actual L2 classes vanishing a.e. outside `(0,infinity) x Omega`. The ambient measure is `volume.prod InfiniteGaussian.gaussianProduct`. The support condition is independent of any stochastic core: `L2Supported.mem_supportedL2_iff` proves its equivalence to vanishing a.e. off the measurable set. Its closedness follows from the closed range of the zero-extension isometry.

`GaussianPredictableFull.predictable_mem_closedProductSteps` proves membership in the OLD completion for every such predictable field, with no boundedness, finite-horizon, polynomial, or differentiability assumption. On each `(0,n]`, the preceding full finite-horizon theorem supplies membership after zero extension. For a vector orthogonal to the old completion, every truncated pairing is zero. Genuine L2-by-L2 integrability and monotone exhaustion of positive time show the full pairing is zero. The double-orthogonal theorem then gives membership. This does not use a totalized nonintegrable integral.

The reverse inclusion is proved by actual predictable measurability and support of arbitrary adapted L2 steps, followed by closedness. Consequently:

- `closedProductSteps_eq_fullPredictable`: equality of the actual ambient submodules.
- `mem_closedProductSteps_iff`: exact predictable-representative and time-support characterization.
- `domainEquiv`: identity on the ambient equivalence classes, as a linear isometric equivalence.
- `itoIntegral`: the PREVIOUS `productIntegral` composed with this identity equivalence.
- `itoIntegral_norm`, `itoIntegral_centered`, `itoIntegral_divergence_graph`: full-domain isometry, centering, and agreement with the previously constructed unbounded Gaussian divergence after the existing field transport.
- `itoIntegral_past_step`, `itoIntegral_past_partition`: actual increment-product/sum formulas for arbitrary L2 past coefficients.
- `itoIntegral_unique`: uniqueness among continuous linear extensions agreeing on the proved dense algebraic polynomial step domain.

These results settle the ambient predictable-density and integral-domain identification obligation for the constructed raw Brownian model, on the entire positive time axis. No usual augmentation, path-continuous modification, martingale representation property, or boundedness of the full divergence is asserted. Time zero is null for the time measure; the `(0,T]` convention is consistent with the earlier `[0,T]` transport.

### Next analytic boundary: ambient density is not derivative graph density

Inspection of `GaussianTimeSensitivity.lean`, `InfiniteGaussianKernel.lean`, the finite-sector graph approximation, and the pinned Mathlib predictable/Lp APIs reveals the next independent obligation. The existing finite-sector approximations concern Gaussian scalar/vector adjoint graphs. They do not prove approximation preserving EVERY Brownian past subspace, nor joint measurability and the causal support of derivatives of time-indexed predictable fields. The new predictable indicator approximation has no derivative estimates at all.

A precise next target is an independently defined field domain of predictable `u` whose probability slices lie in `closedCylindricalDerivative.domain` for a.e. time, with a jointly measurable derivative field `V(t,omega)` in L2 of time times probability with values in `CoefficientSpace`. Prove graph approximation by adapted polynomial step fields, simultaneously in `u` and `V`, WITHOUT defining this target as their closure. This requires an actual product-L2/Bochner-L2 slice bridge, compatibility of past conditional expectations with the closed derivative (including projection onto past deterministic directions), and adaptation-preserving time approximation. In the Brownian time representation, derivative support must be proved to lie in the past before claiming the two-time stochastic sensitivity integral is predictable and square integrable. Hilbert-valued predictable integration and its isometry are also needed for that correction.

The exact passage needed is: for every field in that independently specified domain, construct a SAME sequence of adapted polynomial step fields `u_n` with `u_n -> u` in product L2 and `D u_n -> V` in the derivative-field L2 norm. Then prove convergence of the stochastic correction using a genuine vector-valued isometry. Only those estimates allow closedness of D to give `D(Ju) = u + correction(u)`. No such approximation or correction estimate is assumed or claimed here. The existing Gaussian constant-kernel theorem can be used only AFTER the correction isometry and causal support show slice derivatives vanish. The predictable projection identity alone cannot prove determinism.

This is a substantial missing analytic bridge, not a compilation defect or an inference from the now completed ambient density. Continuous-time sensitivity, stochastic-volatility rigidity, and an operator-functional Ito theorem remain open. The verified finite polynomial sensitivity formula and its nonzero correction example are preserved. No manuscript claims or earlier theorem bodies were changed.

Verification: full Lake build PASS, 4075 jobs. Complete transitive audit PASS, 1667 checks, including all 22 public declarations in the two new modules (80 added across this run). Only `propext`, `Classical.choice`, and `Quot.sound`. Fully explicit `#check @...` statements were checked for every new declaration. No dependency pin changes and no push.

## Bochner fieldwise closed Gaussian derivative (2026-10-12)

`BochnerClosedOperator.fiberGraph mu T` consists of pairs of actual Bochner L2 classes `(u,v)` satisfying `(u(t),v(t)) in graph(T)` almost everywhere. `fiberGraph_singleValued` proves that this is the graph of a genuine partial linear map; `lift_graph`, `mem_lift_graph_iff`, and `mem_lift_domain_iff` expose the exact domain and values. In particular, a measurable square-integrable derivative VALUE is required; pointwise domain membership alone is not substituted for this requirement.

`lift_isClosed` proves closedness when T is closed. It extracts a common a.e. convergent subsequence of both graph coordinates from L2 convergence and uses the original closed graph fiberwise. `lift_dense_domain` proves ambient domain density from actual density of T's domain using finite-measure indicators and Mathlib simple-function density. No graph-core assertion is made. `tensor_graph` gives genuine agreement on separated-variable fields with coefficients in the original operator graph.

`GaussianBochnerDerivative.fieldDerivative` specializes this construction to the existing closed Gaussian derivative. Its source is `Lp GaussianL2 2 volume`, and its target is `Lp GaussianVectorL2 2 volume`, both on real time. `fieldDerivative_graph_iff`, `fieldDerivative_domain_iff`, `fieldDerivative_isClosed`, `fieldDerivative_dense_domain`, and `polynomial_tensor_graph` prove the promised actual fiber operator properties. No predictability or positive-time support is built into this domain.

`fieldDerivative_zero_iff_deterministic` proves that its kernel consists EXACTLY of fields `t -> a(t) * gaussianOne` for a SINGLE scalar `a in L2(volume)`. The forward proof constructs `a` through the bounded inner-product functional against the Gaussian vacuum. Thus time measurability and integrability of the deterministic profile are proved, not selected independently for each t. This is a fieldwise Gaussian kernel theorem, NOT yet stochastic-volatility rigidity.

The product-L2/Bochner-L2 equivalence, adapted graph-core approximation, and identification of the coefficient Hilbert space with derivative time remain distinct obligations. This milestone does not assume them. Pinned Mathlib supplies convergence in measure/subsequence extraction, continuous-map actions on Lp, and simple-function density; no direct-integral closed-operator lifting theorem was imported.

Verification: full build PASS (4077 jobs), transitive audit PASS (1692 checks, including all 25 new declarations), explicit elaborated types checked. Only propext, Classical.choice, Quot.sound. Original files and dependency pins unchanged.

## Parameterized predictable Ito integration (2026-10-12)

`BochnerLinearIsometry.lift` lifts an ACTUAL linear isometry J:E->F to an isometry of Bochner L2 spaces for an arbitrary parameter measure. Its norm equality follows from the a.e. representative formula and equality of pointwise norms; it is not an assumed structure field.

`GaussianParameterizedIntegral.parameterIntegral nu` is `Lp fullPredictable 2 nu ->Li Lp GaussianL2 2 nu`, acting almost everywhere by the existing full predictable Ito integral. `parameterIntegral_coeFn`, `parameterIntegral_norm`, `parameterIntegral_norm_sq_integrable`, `parameterIntegral_isometry`, `parameterIntegral_centered`, and `parameterIntegral_eq_zero_iff` prove actual values, integrability on both sides, norm-square integral equality, centering for almost every parameter, and injectivity.

This constructs the genuine parameterized integral needed for the stochastic correction. Its inputs are Bochner L2 functions with values in the already verified full predictable domain. It does NOT assert that an arbitrary joint derivative field has this measurability/predictability, nor identify a parameterized input with D_s u_t without proof. Causal support, the product-space equivalence, and adapted graph approximation remain to be supplied before invoking it as the sensitivity correction operator. No stochastic derivative interchange is claimed.

Verification: full build PASS (4079 jobs); full transitive axiom audit PASS (1703 checks, all 11 new public declarations audited), only propext, Classical.choice, Quot.sound. All explicit elaborated types checked. No manuscript or pin changes.

## Actual product/Bochner equivalence and field derivative (2026-10-12)

`ProductL2Curry.curryEquiv mu nu` is an onto real linear isometry from `Lp E 2 (mu.prod nu)` to `Lp (Lp E 2 nu) 2 mu`, for real Hilbert E (complete for surjectivity), S-finite measures, and second-countable inner L2. The construction proves strong measurability of actual sections using measurable distances, square integrability by Fubini, and norm preservation. Surjectivity uses genuine simple-field density and the closed range of the isometry. `curryEquiv_coeFn` and `curryEquiv_symm_coeFn` identify both directions on representatives, with the requisite iterated almost-everywhere qualifications. No product representation or tensor density is assumed.

`GaussianProductDerivative.coefficientSpace_secondCountable` derives the needed concrete coefficient-space instance from the previously constructed first-chaos isometric embedding. `scalarCurry` and `vectorCurry` therefore specialize the equivalence without extra Gaussian hypotheses. `derivative` is the actual transport of the preceding closed Bochner derivative to `TimeProbabilityL2 -> partial ProductDerivativeL2`, where the target is coefficient-Hilbert-space-valued L2 on time times probability.

`derivative_domain_iff`, `derivative_graph_iff`, and `derivative_fiber_graph_iff` specify the exact domain and graph. `derivative_isClosed`, `derivative_dense_domain`, and `polynomial_tensor_graph` prove closedness, ambient domain density, and agreement with genuine polynomial derivatives. `predictableSobolev` is independently defined as the intersection of the old full predictable subspace with this operator domain. `past_polynomial_step_mem_predictableSobolev` includes actual adapted polynomial steps. This is NOT a claim of graph density.

`derivative_zero_iff_deterministic` proves `(u,0) in graph(derivative)` iff `u = productTensor a gaussianOne` for one actual Lebesgue L2 time profile a. Both sides concern the actual product equivalence classes. The coefficient-space gradient must still be related to Brownian derivative time through the existing time Hilbert embedding, whose surjectivity has not been assumed. Adapted graph approximation and the sensitivity identity remain independent obligations.

Verification: full build PASS (4083 jobs); full transitive audit PASS (1740 checks, including all 37 new public declarations), only propext, Classical.choice, Quot.sound. Every new declaration's fully explicit type checked. No original source, manuscript, or dependency pin changes.

## Causal derivative-time coordinates on the adapted graph completion (2026-10-12)

`GaussianDerivativeTimeCoordinates.timeProjection` is the adjoint of the existing isometric embedding of actual real-time L2 into CoefficientSpace. `timeProjection_embedding` proves its left-inverse identity. `timeCoordinates` maps coefficient-valued time/probability fields into actual scalar L2 on `(time x Omega) x derivativeTime`. `reconstruct` is an isometry in the reverse direction. Reconstruction and equality of norms are proved ONLY on the embedding range; surjectivity of the original time embedding is neither assumed nor needed.

`past_gradient_timeProjection` computes the time-coordinate derivative of every polynomial in finitely many Brownian past values from the genuine polynomial derivative. `past_gradient_reconstruction` proves that no part of that derivative is lost. `GaussianAdaptedGraphCore.stepGradient_time_range` and `stepGradient_causal` prove, for every finite family r_i <= s and polynomial p, that the derivative of `1_(s,t] p(B_(r_i))` is in this range and vanishes jointly almost everywhere outside `0 < derivativeTime <= integrationTime`. The proof uses actual Gaussian gradient formulas, indicator representatives, and measurable product null-set arguments. It does not infer predictability of derivative sections from joint measurability.

`completedGraph` is explicitly the closed span of these genuine adapted polynomial GRAPH PAIRS. `completedGraph_le_derivative` and `completedGraph_mem_predictableSobolev` prove inclusion in the independently defined closed field-derivative graph and predictable Sobolev domain. `completedGraph_causal` passes lossless range membership and causal support to graph limits using closed subspaces; `completedGraph_time_norm` retains the entire derivative norm. No equality between this restricted graph completion and the independent Sobolev graph is claimed. This distinction is essential: the existing ambient predictable density does not establish adapted graph density.

The remaining next step is to prove that these derivative fields belong to the parameterized predictable integral input space, identify the finite polynomial correction there, and pass the sensitivity formula to this restricted graph completion. Extension to EVERY independently specified predictable Sobolev field still needs an adaptation-preserving graph approximation theorem.

Verification: full build PASS (4085 jobs), full transitive audit PASS (1773 checks; all 33 public declarations added), explicit types inspected. Only propext, Classical.choice, Quot.sound. Original manuscripts and pins unchanged.

## Continuous sensitivity and rigidity on the adapted polynomial graph completion (2026-10-12)

`ProductL2Curry.flip` interchanges actual scalar Bochner L2 parameters using the proved product equivalence and measure-preserving swap. Its tensor formula, and `BochnerLinearIsometry.lift_tensor`, connect all parameterized maps to actual representatives.

`GaussianSensitivityIntegral.Inputs = Lp fullPredictable 2 volume` uses derivative time as parameter and the existing full raw-predictable Ito domain as fiber. `kernelEmbedding` is an actual isometry into coefficient-valued time/probability L2: it forgets the predictable subtype, interchanges the two L2 parameters, and applies the original time Hilbert embedding. `integral` applies the SAME verified parameterized Ito integral, followed by the same time embedding. `integral_norm` proves equality with the complete input-field norm. `correction` extends this map to the ambient derivative-field space via the adjoint of kernelEmbedding, solely to use continuous closed-graph arguments. Its lossless norm and zero-kernel conclusions require and USE proved membership in kernelEmbedding.range; they are NOT asserted off that range.

`GaussianSensitivityCore.stepInput` constructs the actual predictable derivative-time family of a past polynomial step: a finite sum of timeVector(r_i) tensored with the predictable step whose coefficient is the genuine partial derivative polynomial. `kernelEmbedding_stepInput` proves that it reconstructs the whole genuine field derivative. `integral_stepInput` and `correction_stepGradient` prove equality with the OLD `GaussianTimeSensitivity.incrementSensitivity`, including its nonvanishing random-coefficient term. `completedGraph_admissible` extends actual membership in the parameterized predictable input range to the previously defined graph completion, by closed range of an isometry. Thus predictability is proved, not inferred from joint measurability. Causal support is independently proved in the preceding milestone.

`GaussianContinuousRigidity.fieldEmbedding` is a global isometry from actual time/probability fields into the original Gaussian coefficient-field space. `fieldEmbedding_tensor` proves its formula. `completedGraph_sensitivity` states: for EVERY `(u,v)` in `GaussianAdaptedGraphCore.completedGraph`, the actual pair `(itoIntegral u, fieldEmbedding u + correction v)` belongs to `closedCylindricalDerivative.graph`. The proof checks this on genuine polynomial generators and takes closure under a continuous map into the existing closed derivative graph. It never assumes differentiability of the completed integral. `integral_mem_derivative_domain` gives that domain membership explicitly.

`rigidity_graph` and `rigidity_value` prove the following equivalence on this explicit graph completion: the FULL closed Gaussian derivative of the constructed integral equals `fieldEmbedding u` iff there exists ONE deterministic `a : Lp real 2 volume` with `u = productTensor a gaussianOne`. The forward proof uses the actual sensitivity identity, lossless correction isometry, and the independently proved full field-derivative constant-kernel theorem. The reverse uses that kernel theorem and uniqueness of the existing closed derivative graph. There is no predictable projection in the asserted derivative equality and no assumption that the correction vanishes.

SCOPE: this is a genuine continuous closed-graph extension beyond a single finite polynomial expression, on an explicitly restricted graph completion. Equality with the independently defined `GaussianProductDerivative.predictableSobolev` domain is still UNPROVED. No theorem silently substitutes that equality. The remaining strongest-domain obligation is adaptation-preserving simultaneous graph approximation. The construction integrates in stochastic time with derivative time as parameter; the proved causal support makes it the intended future-time sensitivity correction on this domain. No general operator-functional Ito or full Brownian PRP follows from this result.

Verification: full build PASS (4089 jobs), full transitive audit PASS (1811 checks; all 38 public declarations added), fully explicit types checked. Only propext, Classical.choice, Quot.sound. No manuscript or dependency pin changes; nothing pushed.

## Concrete predictable adjoint and verified scope obstructions (2026-10-12)

`GaussianPredictableAdjoint.predictableField_divergence_graph` proves agreement between the SAME Ito integral and the full Gaussian divergence for every full raw-predictable positive-time L2 integrand, using the new actual field embedding. `predictableAdjoint` is the actual bounded Hilbert adjoint of this isometry; `predictableProjection` is the adjoint of the isometric predictable-field embedding. `predictableAdjoint_eq_projected_derivative` proves J*F = Phi*(D F) for every F in the ACTUAL closed derivative domain. This theorem does not extend the unbounded derivative to all L2. `predictableAdjoint_integral`, `representation_residual_orthogonal`, and `representation_norm_decomposition` establish the concrete left inverse and GKW orthogonal decomposition without assuming PRP.

There is a genuine scope obstruction to PRP on the whole ambient Gaussian product. `GaussianAmbientRepresentationObstruction.invisiblePolynomial` is the genuine first-chaos variable W(E 1_(-1,0]), where E is the existing isometric time Hilbert embedding. It is centered and has norm squared one. Its full Gaussian derivative is the embedded negative-time indicator. Every full predictable integrand vanishes off positive time, so this derivative is orthogonal to the predictable field subspace. `invisiblePolynomial_predictableAdjoint` proves J*F=0; `invisiblePolynomial_not_representable` and `exists_centered_not_representable` prove F is outside range J. No assumption of independence or nonrepresentation is used. Thus the appropriate future PRP target is the Brownian-generated scalar subspace, not all of InfiniteGaussian.GaussianL2. This does not refute classical Brownian PRP.

`GaussianBrownianBracket.predictableAdjoint_wiener` identifies J*B_t with the actual deterministic interval indicator, and `predictableAdjoint_wiener_norm_sq` proves its norm squared is t. `integrated_projected_energy` proves, for every NNReal T, integral_0^T ||J*B_s||^2 ds = T^2/2. `integrated_projected_energy_one_ne_variance` proves that at T=1 this is not ||B_1||^2=1. These concern genuine constructed variables and operators. They do NOT claim a pathwise quadratic-variation construction.

This directly contradicts the proposed Brownian normalization of the manuscript's whole-Hilbert-norm intrinsic bracket (C:/Operator/OperatorDerivative.tex:770-774). The projected derivative is an interval-valued Hilbert element; it is not the scalar diagonal coefficient one. The manuscript's operator Ito formula at line 850 and its claimed Brownian specialization cannot be certified with that bracket. The earlier concerns about the terminal-to-running-time replacement in line 867 and the promotion argument at line 886 are not resolved by continuous linear stochastic Fubini. No alternate textbook Ito theorem has been relabeled as the manuscript result, and no TeX was modified.

Verification: full build PASS (4092 jobs); transitive audit PASS (1837 checks, including all 26 new public declarations), explicit elaborated types checked. Only propext, Classical.choice, Quot.sound. Original Lean/TeX SHA256 hashes and dependency pins match the starting checkpoint. No unsafe/native proof shortcuts or source proof holes were introduced.

### Exact remaining mathematical boundaries

1. Prove equality of completedGraph with the independently specified predictable part of GaussianProductDerivative.derivative.graph. The missing analytic bridge is Gaussian-past conditional expectation/orthogonal projection commuting with the closed derivative, followed by a simultaneous time-step and Gaussian polynomial graph approximation preserving each past. Existing ambient predictable density alone is insufficient.
2. The sensitivity and rigidity theorem already holds on completedGraph. Extension to the larger independent domain needs (1); it must not be advertised before that proof. The deterministic conclusion is an L2 equivalence-class statement with one measurable square-integrable profile, not an every-time version claim.
3. Prove predictable representation on the Brownian-generated scalar L2 subspace. Whole-ambient centered PRP is now formally refuted. The concrete adjoint/projection identity and GKW decomposition are proved, but residual-zero/Clark-Ocone reconstruction on that generated subspace remains open.
4. State a corrected genuine operator Ito target using the appropriate local covariance/quadratic-variation input. The existing whole-norm bracket cannot serve as its Brownian correction. Adjointness, Leibniz, and stochastic Fubini do not alone supply the missing local second-order argument.
5. The original Gubinelli remainder claims and Volterra normalization defects in the preserved earlier audit remain unresolved. No rough-path result, path-continuous modification, or usual augmentation was constructed in this run.

Paper 1 is NOT complete. These are explicit mathematical/domain boundaries, including two now machine-checked scope obstructions, rather than unreported failed Lean proofs. All newly registered modules compile; the original manuscript and prior untracked audit documents remain preserved.

## Independent deterministic predictable graph core (2026-10-12)

`GaussianDeterministicGraphCore.vacuumProjection` is the actual Gaussian mean projection F -> <1,F>1. `meanProjection` lifts it to time/probability L2 through the verified Bochner equivalence. `meanProjection_tensor` proves its action on separated fields; `gaussianOne_inner_self` justifies normalization, including `meanProjection_deterministic`.

`constant_step_graph` proves genuine zero-derivative graph membership of constant predictable interval steps. `meanProjection_graph` maps the OLD ambient predictable approximants into these graph pairs and uses continuity of the mean projection. Here ambient density is legitimately sufficient because the projected derivatives are all proved zero, rather than merely presumed to converge.

`deterministic_mem_completedGraph` includes every actual field a(t)1 with a in real Lebesgue L2 and that field in fullPredictable. `independent_zero_graph_mem_completedGraph` equivalently includes every independently predictable field with (u,0) in the independently constructed derivative graph. `deterministic_integral_derivative` proves (J(a1),fieldEmbedding(a1)) belongs to the genuine closed Gaussian derivative graph. No step-function, finite-support, finite-horizon, or polynomial assumption is imposed on a. This is the zero-gradient independent subclass; full random predictable Sobolev graph equality remains open.

Verification: full Lake build PASS (4093 jobs); transitive axiom audit PASS (1849 declarations; all 12 new public declarations included). Fully explicit public types elaborated. Dependencies only propext, Classical.choice, Quot.sound. Original manuscripts, pins, and all twelve unrelated untracked documents preserved.

## Deterministic first-chaos reconstruction and local increment energy (2026-10-12)

`GaussianDeterministicIntegral.firstChaos_closedDerivative_graph` identifies the FULL derivative of W(Ea) with fieldEmbedding(a*1) for every real Lebesgue L2 profile a, without a predictability hypothesis. `eq_of_same_derivative_mean` proves uniqueness from equal full derivatives and equal Gaussian means. `itoIntegral_deterministic` identifies J(a*1)=W(Ea) whenever a*1 belongs to the actual full predictable domain. `predictableAdjoint_deterministic_firstChaos` and `firstChaos_reconstruction` give the corresponding exact adjoint and projected-full-derivative reconstruction. This is first-chaos representation only, not full Brownian PRP.

`GaussianLocalIncrementEnergy.increment_closedDerivative_graph`, `incrementDomain`, and `increment_derivative` refer to the existing closed derivative of the actual random variable B_t-B_s. `incrementEnergy` is its actual squared derivative norm. `incrementEnergy_eq` proves it equals t-s for every 0<=s<=t; `normalized_incrementEnergy` proves energy(t,t+h)/h=1 for h>0. `incrementEnergy_add`, `incrementEnergy_eq_variance`, and `integrated_local_density` prove additivity, agreement with the actual Gaussian increment variance, and recovery of T by integrating the proved unit local density. All boundaries include zero-length increments; division is only asserted for h>0.

This repairs the local increment normalization, not the manuscript's whole-gradient integral (which still equals T^2/2). These identities alone do NOT prove convergence of random quadratic-variation sums, nor identify random-volatility Malliavin energy with a bracket. No such identification is asserted.

Verification: full build PASS (4095 jobs), transitive audit PASS (1863 declarations; all 14 new public declarations checked). Explicit elaborated public types passed. Only propext, Classical.choice, Quot.sound; no proof holes or unsafe shortcuts. Original manuscripts and pins unchanged.

## Correct Brownian-generated scalar range (2026-10-12)

`GaussianBrownianGeneratedSpace.brownianSigma` is the sigma-algebra generated by all actual nonnegative-time Brownian observations on the countable Gaussian product. `brownianL2` is Mathlib's independently measurable L2 subspace; `centeredBrownianL2` intersects it with the actual expectation kernel. `mem_centeredBrownianL2_iff` spells out measurable representatives and the zero genuine integral. Both subspaces are proved closed.

`brownianPolynomial_closure` reuses the already verified arbitrary-family Gaussian density theorem and identifies the closure of all finite-observation polynomials with the entire generated L2 space. `incrementProduct_mem_brownianL2` checks actual measurable polynomial step integrals, and `itoIntegral_mem_brownianL2` passes to the old completed integral. `itoIntegral_mem_centeredBrownianL2`, `integralRange_le_centeredBrownianL2`, `integralRange_isClosed`, and `integral_representation_unique` establish the correct range inclusion, closedness, and uniqueness without a representation assumption.

The reverse range inclusion is NOT proved. The remaining substantive PRP obligation is representation of centered finite Brownian polynomials; density plus the proved closed range would then suffice. Ambient Gaussian PRP remains false by the earlier negative-time counterexample. This module does not silently replace that reverse inclusion with the existing ambient density theorem.

Verification: full build PASS (4096 jobs), transitive audit PASS (1879 declarations, including all 16 new public declarations). Explicit types elaborated. Axioms only propext, Classical.choice, Quot.sound. No manuscripts, dependency pins, or previous theorem bodies changed.

## Actual Brownian quadratic variation and constructive square representation (2026-10-12)

`GaussianQuadraticIncrement.centeredSquare h` is the genuine polynomial W(h)^2-||h||^2. Its representative, derivative 2 W(h)h, equality with the genuine rank-one divergence, centering, and covariance are all proved. `centeredSquare_inner` gives E[(W(h)^2-||h||^2)(W(k)^2-||k||^2)]=2<h,k>^2 from actual Gaussian IBP. No fourth-moment formula is assumed. The polynomial moments guarantee genuine integrability.

`GaussianBrownianQuadraticVariation.quadraticVariation` is an actual Gaussian L2 random variable whose representative is the sum of squared Brownian increments (`quadraticVariation_coeFn`). For every finite monotone NNReal partition, including repeated times and the empty partition, `quadraticVariation_error_norm_sq` proves its squared L2 distance to the elapsed-time constant is exactly 2 times the sum of squared interval lengths. `uniform_quadraticVariation_error` gives 2*T^2/(n+1), and `uniform_quadraticVariation_tendsto` proves L2 convergence to the actual constant T for every T>=0. This is a genuine random quadratic-variation limit on uniform partitions; no almost-sure or all-partition/pathwise theorem is claimed.

`GaussianQuadraticRepresentation.leftStepField` is the finite sum of the actual predictable fields 1_(t_i,t_(i+1)] B_(t_i). `integral_leftStepField_coeFn` checks its existing Ito integral. `leftStep_square_identity` retains the random squared-increment sum in the exact finite telescoping formula. `leftStep_integral_tendsto` then uses the separately proved quadratic-variation limit. `terminalSquare_half_mem_integralRange` constructs membership of (B_T^2-T)/2 in the closed integral range, without PRP. `quadraticIntegrand`, `integral_quadraticIntegrand`, and `leftStepField_tendsto` identify a unique predictable L2 integrand and convergence of the SAME left-point fields. At this checkpoint its limiting running-time representative is still to be proved; it has not been silently identified with B_s by definition.

Verification: full build PASS (4099 jobs), transitive audit PASS (1914 declarations, all 35 new public declarations checked). Fully explicit types elaborated. Axioms only propext, Classical.choice, Quot.sound. Sources contain no proof holes or unsafe shortcuts. No original manuscripts or dependency pins changed.

## Genuine Brownian quadratic Ito formula (2026-10-12)

`GaussianQuadraticIto.stepValue_on_interval`, `stepValue_outside`, and `uniformTime_covers` handle exact half-open partition membership, including boundaries. `stepValue_tendsto` proves convergence of the Brownian Gaussian L2 slices to B_s on (0,T] and zero elsewhere, using the independently proved increment variance and the vanishing mesh. `scalarCurry_leftStepField` connects these slices to the actual predictable stochastic-sum fields.

`quadraticIntegrand_slices` now identifies the previously constructed integrand: scalarCurry(quadraticIntegrand T)(s)=1_(0,T](s)*wienerL2(s.toNNReal), for Lebesgue-a.e. s. It follows by an actual a.e.-convergent Bochner L2 subsequence and uniqueness of the already proved slice limits, not by prescribing the integrand. Predictability and square integrability come from the original fullPredictable subtype and its proven norm convergence.

`brownian_quadratic_ito` proves B_T^2 = 2*J(quadraticIntegrand T)+T almost everywhere on the Gaussian probability space, for EVERY NNReal T, including zero. Together with the slice identification this is a genuine quadratic Brownian Ito formula with the existing integral. The correction T comes from actual random quadratic variation, not the false integrated whole-gradient energy. No C2 functional/path-dependent Ito theorem, continuous path modification, or usual augmentation is claimed.

Verification: full Lake build PASS (4100 jobs), transitive axiom audit PASS (1923 declarations; all nine new declarations checked). Explicit types elaborated; only propext, Classical.choice, Quot.sound. Original sources/manuscripts and dependency pins unchanged.

## Independent running-Brownian graph approximation and quantified sensitivity (2026-10-12)

`GaussianBrownianSobolevField.firstChaosGradient` is the bounded map constVector composed with the first-chaos embedding adjoint. It is NOT the definition of the full Malliavin derivative. `firstChaosGradient_apply` and `firstChaosGradient_past_linear` prove agreement on actual first-chaos variables. `fieldFirstChaosGradient` transports its pointwise Bochner lift to the actual product spaces; its tensor formula is proved.

`linear_past_step_graph` and `leftStepField_graph` put the actual first-chaos predictable steps and their genuine derivatives in completedGraph. `quadraticIntegrand_graph` passes BOTH coordinates to the SAME stochastic-sum limit using continuity of this bounded first-chaos map. `quadraticIntegrand_mem_independentSobolev` proves membership in the independently defined predictable derivative domain. More explicitly, `runningBrownian_graph_of_slices` assumes only a fullPredictable field whose actual Bochner slices are 1_(0,T] B_s and PROVES its adapted graph-core membership; no derivative or graph-approximation assumption is imposed on that field. This is a concrete nonpolynomial random-time-field subclass, not full predictable graph density.

`quadraticIntegrand_sensitivity` and `quadraticIntegrand_sensitivity_norm` apply the actual continuous sensitivity theorem. `quadraticIntegrand_gradient_norm` identifies the derivative-field norm with the input norm on this first-chaos field. `quadraticIntegrand_norm_sq` proves the latter is T^2/2. `quadraticIntegralDomain` explicitly includes its existing stochastic integral in the full closed derivative domain; `quadraticIntegral_sensitivity_energy` proves ||D(Ju)-fieldEmbedding(u)||^2=T^2/2.

`quadraticIntegral_derivative` identifies D(Ju)=B_T E1_(0,T], using the genuine centered-square polynomial derivative. `predictableProjection_terminalBrownian` proves that the actual predictable projection of this terminal-valued derivative is the running Brownian integrand. This is a concrete quadratic Clark--Ocone projection; the terminal-to-running replacement is now PROVED for this example, not presumed for general nonlinear functionals.

`quadraticIntegral_full_energy` gives ||D(Ju)||^2=T^2. `quadraticIntegral_full_energy_ne_variance` proves this differs from ||Ju||^2=T^2/2 whenever T>0. Thus even expected stochastic energy for random volatility cannot be recovered by blindly taking the full Malliavin derivative norm. No random pathwise bracket was asserted.

Verification: full build PASS (4101 jobs), transitive audit PASS (1944 declarations; all 21 new public declarations checked). Explicit types elaborated. Axioms only propext, Classical.choice, Quot.sound. No prior theorem bodies or dependency pins changed.

## Deterministic causal Volterra kernels in the actual integral (2026-10-12)

`GaussianDeterministicVolterra.predictable_time_measurable` proves measurability of the time coordinate for the raw predictable sigma-algebra. `positive_profile_predictable` proves every actual real Lebesgue L2 profile vanishing a.e. on nonpositive times yields a fullPredictable deterministic field. No continuity, step-function, finite-horizon, or separate predictability hypothesis is assumed.

`positiveProfiles` is independently specified by a.e. support; `profileField` and `profileIntegral` use the SAME existing predictable Ito integral. `profileIntegral_eq_isonormal` proves equality with W(Ea), `profileIntegral_derivative` gives its full closed derivative, and `profileIntegral_law` proves Gaussian variance ||a||^2, including a=0. `profile_pair_integrable` and `profileIntegral_pair_integrable` justify both covariance integrals. `profileIntegral_covariance` gives integral a(r)b(r) dr exactly.

`causal_profile_mem` handles a kernel supported in (0,t] at EACH given time. `volterraProcess` uses a family K:NNReal->Lp(real,2,volume), with that a.e. support for every t. `volterraProcess_eq`, `volterraProcess_isGaussianProcess`, and `volterraProcess_covariance` identify its actual stochastic integral, finite-dimensional Gaussian laws, and covariance integral K_s K_t. No nondegeneracy, independence, or covariance normalization is imposed. In particular the representer norm is variance, not a derivative of variance.

Scope: a rigorous deterministic-kernel Volterra realization. No joint time measurability/continuity is asserted without hypotheses on K, and no fBM kernel formula, fractional predictable projection, random-kernel calculus, stochastic Fubini, or rough-path assertion is proved here. The legacy Volterra claims need these qualifications; no manuscript was edited.

Verification: full build PASS (4102 jobs), transitive audit PASS (1960 declarations; all 16 new public declarations checked). Explicit types elaborated. Only propext, Classical.choice, Quot.sound. Original manuscripts and dependency pins preserved.

## Finite Brownian quadratic cylinders and Clark--Ocone (2026-10-12)

`GaussianQuadraticCylinders.brownianProduct` is the actual polynomial product B_s B_t; `brownianProduct_coeFn` checks its random-variable representative. For s<=t, `orderedCrossField` is 2 times the running-Brownian integral field on (0,s] plus B_s on (s,t]. `orderedCrossField_integral` proves its existing Ito integral is B_s B_t-s. `crossField_integral` treats arbitrary order, coincident times, and zero times by min/max, with centering min(s,t).

For any finite index type, arbitrary real c,a_i,b_ij and arbitrary nonnegative times t_i, `quadraticCylinder` is the genuine class c + sum a_i B_(t_i) + sum b_ij B_(t_i)B_(t_j). `quadraticCylinderIntegrand` explicitly sums deterministic interval fields and the proved cross fields. `quadraticCylinder_representation` proves J(u)=F-m, and `quadraticCylinder_mean` proves m is the actual expectation, namely c+sum b_ij min(t_i,t_j). No symmetry of b, independent observations, or nonsingular covariance is required.

`quadraticCylinder_mem_derivative_domain` proves membership in the actual full closed Malliavin derivative domain. `predictableAdjoint_constant` follows from actual centering of the Ito integral. `predictableProjection_quadraticCylinder` identifies the actual predictable projection of DF with the explicit integrand; `quadraticCylinder_clarkOcone` proves F=E[F]+J(PredProj DF). The representation was established before applying the adjoint identity, so this does not assume PRP. All integrals are of genuine Gaussian L2 classes on a probability space. This proves the entire finite quadratic-cylinder class, not higher-degree polynomial or full Brownian-generated L2 representation.

Verification: full Lake build PASS (4103 jobs), transitive audit PASS (1976 declarations; all 16 new public declarations checked). Explicit elaborated types checked. Axioms only propext, Classical.choice, Quot.sound. No earlier theorem bodies, manuscripts, or dependency pins modified.

## First-chaos projection preserves the complete Brownian past (2026-10-12)

`GaussianPastFirstChaos.projection` is W W*, the actual bounded orthogonal projection onto the complete first-chaos range. Idempotence and orthogonality of the residual are proved. `projection_closedDerivative_graph` proves that for EVERY ambient Gaussian L2 class F, its projected class belongs to the existing full closed derivative domain, with constant derivative W*F. This is agreement with the original derivative, not a newly prescribed derivative.

`adjoint_pastPolynomial` derives W*[p(B_r)] = sum_i E[partial_i p(B_r)] E(timeVector r_i) from genuine Gaussian integration by parts, with integrability of every coefficient and finite sum. `projection_pastPolynomial` identifies the resulting scalar projection as sum_i E[partial_i p(B_r)] B_(r_i). Dependent and repeated observations are permitted. `projection_pastPolynomial_measurable` proves this is past-measurable when every r_i<=s.

`projection_preserves_past` extends that conclusion to EVERY Gaussian L2 class measurable for the raw Brownian past at s. It uses polynomial density and continuity of this actual bounded projection into the closed measurable subspace. This use of ambient density is legitimate for the bounded map; it does not assert density in the full derivative graph norm. Higher-chaos past-preserving truncations and the full past conditional-projection/gradient intertwining identity remain unproved.

Verification: full Lake build PASS (4104 jobs); transitive audit PASS (1984 declarations; all eight new public declarations checked). Fully explicit public types elaborated. Only propext, Classical.choice, Quot.sound. Existing manuscripts, theorem bodies, and pins preserved.

## Independent predictable first-chaos graph core (2026-10-12)

`GaussianFirstChaosGraphCore.fieldProjection` is the actual bounded pointwise first-chaos orthogonal projection transported through scalarCurry. `fieldProjection_tensor` proves its tensor action. `productTensor_sum_smul` and `wiener_step_graph` justify the finite linear combinations used in `projected_past_step_graph`. The latter uses the IBP-derived projection coefficients, not a prescribed derivative.

`projectedGraph` maps u to (Q_1 u, B Q_1 u), where B is the existing bounded first-chaos gradient lift. `fieldProjection_graph` proves this pair is in completedGraph for EVERY independently specified fullPredictable u. The proof applies this continuous pair map to the existing dense predictable polynomial steps. Each projected step was independently proved to have its ACTUAL derivative B Q_1 u. Consequently both graph coordinates converge simultaneously; this is not an inference of graph density from unprojected ambient density.

`fieldProjection_eq_of_firstChaos_slices` assumes exactly that scalarCurry(u)(t) belongs to the actual range of the isonormal first-chaos isometry for Lebesgue-a.e. real t. `firstChaos_slices_mem_completedGraph` assumes this slice condition and u:fullPredictable and PROVES (u,Bu) belongs to completedGraph. `firstChaos_slices_mem_independentSobolev` proves actual domain membership as a consequence. No prior Sobolev membership, finite horizon, finite observation family, or graph approximation is required. `firstChaos_slices_sensitivity` proves (J(u),Phi(u)+correction(Bu)) belongs to the full closed derivative graph.

`firstChaos_slices_gradient_norm` gives ||Bu||=||u||. `firstChaos_slices_correction_norm` gives ||correction(Bu)||=||u|| for predictable fields in this independent subclass. `firstChaos_slices_rigidity` gives the deterministic-profile characterization using the existing full derivative; `firstChaos_slices_rigidity_zero` strengthens it here to (J(u),Phi(u)) in graph(D) iff u=0. The zero conclusion is appropriate because first chaos is centered. Constants plus first chaos, arbitrary higher chaoses, and all predictable Sobolev fields are not silently included in this theorem.

Verification: full Lake build PASS (4105 jobs). Complete transitive axiom audit PASS (1999 declarations; all 15 new public declarations and all 162 campaign declarations included). Public types elaborated with explicit arguments. Only propext, Classical.choice, Quot.sound. All thirteen new modules scanned for proof holes, custom axioms, unsafe/native shortcuts; none found. Existing Lean theorem bodies, dependency pins, original manuscripts, and twelve pre-existing untracked documents preserved.

## Paper 1 campaign checkpoint and exact remaining obligations (2026-10-12)

Starting verified commit: 59f9eafb022757f1f94eb0898aa856b1aa74ac4d. Ten separately verified milestones now establish the independent deterministic and predictable first-chaos graph subclasses; the correct Brownian-generated scalar space and closed integral range inclusion; actual Brownian L2 quadratic variation on uniform partitions; genuine quadratic Ito with the existing predictable integral and proved running-Brownian slices; finite quadratic-cylinder predictable representation and Clark--Ocone; exact random-volatility sensitivity energies; and deterministic causal Volterra realization.

Paper 1 is NOT complete. The precise principal missing step is a Brownian-past-compatible graph approximation beyond first chaos. A sufficient route is to prove, on the actual closed derivative domain, D Q_K F = (Q_K tensor P_K) D F for the actual Gaussian conditional orthogonal projection onto a Brownian past subspace K, with all operator domains justified. One must then prove simultaneous predictable time/randomness approximations in the derivative graph norm. Alternatively, past-preserving higher-chaos truncations with actual gradient action and graph convergence would support the same strategy. The existing finite ambient coordinate projections cannot simply be assumed to preserve every Brownian past. Automatic causal support for the entire independently predictable Sobolev domain likewise remains to be proved.

Full Brownian-generated PRP remains open: the proved representation now covers every finite quadratic cylinder, including dependent/repeated times, but not arbitrary higher-degree Brownian polynomials. Representation of those polynomials, together with the already proved generated-space density and closed integral range, would finish PRP. Full-domain Clark--Ocone then requires using that equality on the correct generated space; whole ambient Gaussian PRP is still false.

The Brownian bracket result at this checkpoint is actual L2 convergence of uniform squared-increment sums to T with exact error 2*T^2/(n+1), plus the local increment energy identity t-s. No pathwise/all-partition assertion or general random-volatility bracket process has been proved. The running-Brownian example proves why full Malliavin energy is not the stochastic energy: for J(1_(0,T] B), full derivative energy is T^2 whereas variance is T^2/2.

A genuine quadratic Brownian Ito theorem and finite quadratic-cylinder Clark--Ocone are verified; general polynomial, C2, or path-functional Ito remains open. No Malliavin/Dupire identification was asserted. Deterministic L2 causal Volterra kernels are realized with their true covariance, but random-kernel stochastic Fubini, fractional normalization claims, and Gubinelli/rough-path repairs remain open. No IBM development or manuscript rewrite was begun.

The next primary milestone should establish higher-chaos Brownian-past-compatible derivative projection or the precise closed-domain Gaussian-past intertwining lemma above. The absence of that proof is an analytic/formalization obligation, not evidence that the desired graph-core theorem is false. No conclusion-equivalent assumption has been inserted to bypass it.

## All-order actual Gaussian number sectors and complete orthogonal decomposition (2026-10-12)

New modules: GaussianNumberSectors, GaussianNumberHermite, GaussianChaosDecomposition. All declarations are in the GaussianNumberSectors namespace. `sector n` is the actual subspace of f for which there exists g with (f,g) in graph(D) and (g,n*f) in graph(D*). This is the genuine number-operator eigenspace, with both domains explicit; no decomposition or projection properties are assumed. `sectorGraph_energy`, `sector_isClosed`, and `gradient_norm` prove the energy identity, closedness, and ||Df||=sqrt(n)||f|| on this space, including n=0. `projection` is Mathlib's actual orthogonal projection onto the proved closed subspace. Its contraction, idempotence, genuine derivative graph, and mutual sector orthogonality are proved.

`tensor_coordinate_number` and `tensor_number_polynomial` derive delta(grad H_alpha)=|alpha| H_alpha from the actual normalized Hermite raising/lowering identities. `finiteHermite_mem_sector` lifts this to the infinite Gaussian operators using their genuine graph inclusions. `sector_total` proves completeness using the independently verified finite tensor Hermite completeness and infinite polynomial-cylinder density. No finite-dimensional assumption is imposed on the ambient Gaussian product.

`sector_isHilbertSum`, `coefficients`, and `coefficients_eq_projection` construct the Hilbert-sum isometry and identify its components with the actual orthogonal projections. `projection_hasSum`, `projection_hasSum_norm_sq`, and `truncation_tendsto` prove unconditional reconstruction, Parseval, and convergence of the finite order sums for EVERY ambient Gaussian L2 class. `sector_zero_iff` and `projection_zero` identify the vacuum with the actual Gaussian expectation. These are all natural orders, not just a finite chaos cutoff.

Scope: this is an ambient spectral decomposition. It does not yet assert that higher-order projections preserve an arbitrary Brownian past or even the Brownian-generated scalar subspace. Negative-time noise has not been identified with positive-time Brownian information. No PRP or predictable graph-core equality follows from ambient scalar convergence alone.

Verification: full Lake build PASS (4108 jobs); transitive axiom audit PASS (2039 declarations, including all 40 new public definitions/theorems/instances). Explicit public types elaborated. Only propext, Classical.choice, Quot.sound. Original files, previous theorem bodies, pinned dependencies, and twelve untracked documents preserved.

## Same-sequence all-chaos convergence in the actual derivative graph (2026-10-12)

`GaussianChaosGraphConvergence` proves `simultaneous_graph_tendsto`: for every actual (f,g) in graph(D), the SAME truncation sequence satisfies (sum_(n<=N) Q_n f, sum_(n<=N) D Q_n f) -> (f,g). `truncation_graph` verifies every approximating pair belongs to the original closed derivative graph. No graph-core, convergence, or summability assumption is added.

The proof uses actual adjoint duality to establish `derivative_projectedGradient_pairing` and `projectedGradient_finite_bound`. Orthogonality of the genuine gradient ranges then proves summability of projected derivatives. Scalar convergence and closedness identify the vector sum with the ORIGINAL derivative g. `derivative_domain_iff_weighted_chaos` proves both directions of f in dom(D) iff sum_n n||Q_n f||^2 is finite. `derivative_energy_hasSum` proves its sum is exactly ||Df||^2. Order zero and the infinite Gaussian ambient space are included. This is derivative graph convergence, not just scalar L2 convergence.

Scope: the homogeneous gradient is proved as an actual bounded map into vector Gaussian L2, with its full derivative graph and spectral norm. Identification with the componentwise order-(n-1) vector-chaos projection has not yet been established. Brownian-past preservation and independent predictable graph-core equality remain separate obligations at this checkpoint.

Verification: full build PASS (4109 jobs); complete transitive audit PASS (2055 declarations, including all 16 new public declarations). Fully explicit types checked. Only propext, Classical.choice, Quot.sound. No changes to existing theorem bodies or dependency pins.

## All-order projection preserves correlated cylinders and every Brownian past (2026-10-12)

`GaussianChaosCylinders.cylinder_gradient_expansion` proves the genuine finite-rank expression for the derivative of any polynomial cylinder. `orthonormal_rankDivergence` derives the actual Gaussian coordinate-divergence formula on an arbitrary orthonormal Hilbert family. `orthonormal_tensor_mem_sector` then proves the number-eigenvalue identity for Hermite tensors in ANY such directions, not only the ambient coordinate axes.

`projection_of_sector` proves the exact Kronecker action of each orthogonal projection on every eigenspace. `projection_orthonormal_polynomial` uses algebraic Hermite spanning. Crucially, `projection_polynomial` removes the orthonormality assumption: for ANY finite family h and polynomial p, there exists a polynomial q in the SAME family such that Q_n[p(W(h))]=q(W(h)). The proof chooses an orthonormal basis of span(h), proves the two polynomial substitutions, and returns to the original observations. Singular covariance, repetitions, zero directions and the zero-dimensional span require no extra assumptions.

`projection_pastPolynomial_measurable` and `projection_preserves_past` establish preservation of the actual raw Brownian past at EVERY time by EVERY natural-order projection, for all past-measurable Gaussian L2 classes. Extension uses the existing past-polynomial density and closedness of the actual measurable subspace under the bounded projection. No conditional expectation commutation or PRP is assumed.

Verification: full Lake build PASS (4110 jobs); complete transitive audit PASS (2064 declarations, all nine new public declarations included). Explicit theorem types checked. Only propext, Classical.choice, Quot.sound. This resolves higher-chaos past preservation. Time-probability graph approximation is still a separate step; this entry does not yet claim full predictable graph-core equality.

## Full independent predictable Sobolev graph core and rigidity (2026-10-12)

`GaussianPredictableChaosCore.completedGraph_eq_independent` proves the exact equality between the existing adapted polynomial graph completion and the graph of the ORIGINAL fieldwise derivative restricted to independently defined predictable L2 fields. `completedGraph_iff_independent` states both inclusions explicitly. No graph density, causal support, finite-chaos hypothesis, or extra Sobolev condition is assumed.

The proof first applies each genuine scalar chaos projection and its actual bounded gradient map to the existing ambient predictable polynomial approximations. `projected_step_graph` identifies each projected step with a polynomial in the SAME Brownian observations, using the proved correlated-cylinder theorem; derivative values follow from the actual closed derivative's uniqueness. Thus ambient density becomes graph approximation only AFTER both components have been proved continuous for each fixed projection. `truncated_field_graph` sums these graph pairs. `field_graph_truncation_tendsto` proves simultaneous convergence in actual product L2, using scalar and derivative contraction bounds, actual fiber graphs, and the new generic `BochnerL2Dominated.tendsto_of_ae_norm_bound`. This last theorem is proved by genuine dominated integration of squared errors. Closedness finishes `independent_graph_mem_completed`.

`exists_polynomial_graph_sequence` extracts a SINGLE sequence of adapted polynomial graph pairs converging in both coordinates. `independent_derivative_causal` proves causal support on the full independent domain. `independent_sensitivity_graph`, `independent_sensitivity_value`, `independent_sensitivity_norm`, and `independent_rigidity` extend the existing genuine sensitivity identity, exact norm equality, and deterministic-profile characterization to this whole domain. `independentIntegralDomain` supplies the proved domain membership of the actual predictable integral. No claim is made for predictable fields outside the derivative domain.

Verification: full Lake build PASS (4112 jobs); complete transitive axiom audit PASS (2089 declarations, all 25 new public declarations included). Explicit public types checked. Only propext, Classical.choice, Quot.sound. Original theorem bodies and pins unchanged. This resolves the previously principal independent graph-core obstruction. Full Brownian-generated PRP, arbitrary-degree polynomial Ito, and componentwise vector-chaos lowering identification remain separate obligations.

## Full-domain Gaussian Poincare and quantitative predictable rigidity (2026-10-12)

`GaussianSpectralPoincare.gaussian_poincare_sq` and `gaussian_poincare` (GaussianNumberSectors namespace) prove ||F-E[F]|| <= ||DF|| on the ACTUAL infinite-dimensional closed derivative graph. The proof compares the proved Parseval series with the weighted derivative-energy series, using n>=1 off the vacuum. It assumes neither Gaussian log-Sobolev nor a spectral gap. The constant is exactly one.

`GaussianQuantitativeRigidity.field_poincare_sq` and `field_poincare` integrate this genuine fiberwise inequality on the original product-L2 derivative graph. The integrals are finite because both coordinates are actual Bochner L2 classes; no representative convergence or integrability is postulated. `meanProjection_deterministic_profile` identifies the mean of every independently predictable field with a deterministic L2 time profile via the existing zero-derivative characterization.

`quantitative_rigidity` proves that for u in fullPredictable and (u,v) in the original derivative graph, there EXISTS a deterministic time profile a with ||u-a tensor 1|| <= ||D(Ju)-fieldEmbedding(u)||. `distance_deterministic_le_sensitivity` gives the exact distance-to-set formulation. The right side is the actual closed derivative value on the proved integral domain; equality of its norm with ||v|| comes from the full independent graph-core theorem. No extra finite-chaos or adapted-completion hypothesis occurs. This is a formalized Gaussian consequence, not a claim of new mathematics.

Verification: full Lake build PASS (4114 jobs); transitive audit PASS (2096 declarations, all seven new public declarations). Explicit types inspected. Only propext, Classical.choice, Quot.sound. No old theorem body, manuscript, or dependency pin modified.

## Actual Gaussian conditional expectations and generated-space polynomial graph cores (2026-10-12)

`GaussianConditionalGraph` treats arbitrary index types I and families h:I->CoefficientSpace, without countability, independence or nondegeneracy assumptions. `generated h` is the actual L2 subspace measurable for sigma(W(h_i)). `conditionalProjection_eq_condExpL2` and `conditionalProjection_ae_condExp` identify its orthogonal projection with Mathlib's real conditional expectation. `projection_familyPolynomial` and `projection_preserves_generated` prove that EVERY Q_n preserves the same family polynomial algebra and its entire generated L2 subspace. `projection_conditional_commute` proves Q_n P_h=P_h Q_n, using actual orthogonal projection symmetry and the established preservation.

`conditionalProjection_mem_domain` proves preservation of the ORIGINAL closed derivative domain. `conditional_derivative_norm_le` proves ||D(P_h F)|| <= ||DF||; `conditionalProjection_norm_le` supplies the scalar contraction. Both follow from the proved weighted chaos characterization and actual projection commutation, with no Sobolev stability hypothesis. This includes conditioning on every closed Hilbert subspace (take its subtype-indexed family). The componentwise tensor formula D(P_h F)=P_h applied to the appropriately Hilbert-projected gradient remains unproved; graph contraction does not by itself identify that vector formula.

`projection_preserves_brownian` and `truncation_preserves_brownian` specialize to the existing full nonnegative-time Brownian-generated scalar space. Combining these with `truncation_tendsto` gives genuine finite-chaos density there, excluding the unrelated ambient negative-time noise.

`GaussianGeneratedGraphCore.completedFamilyGraph_eq_independent` proves exact polynomial graph density in EACH generated scalar subspace, with the original closed derivative. `familyCore` embeds actual polynomial evaluations in the already verified polynomial derivative domain; it supplies no artificial derivative data. `projected_polynomial_graph` proves the projected function remains a family polynomial and its genuine derivative is the projectedGradient. Bounded pair maps extend this to each projected generated-space function; simultaneous chaos graph convergence proves the closure equality. `exists_polynomial_graph_sequence` gives one sequence of actual family polynomials whose values and derivatives converge together. This supports future Brownian Clark--Ocone limits, but is not predictable representation.

Verification: full Lake build PASS (4116 jobs); complete transitive axiom audit PASS (2124 declarations, all 28 new public declarations including the completeness instance). Explicit public types checked. Only propext, Classical.choice, Quot.sound. No modifications to original manuscripts, previous theorem bodies, or dependency pins.

## Orthogonal sensitivity geometry on the full independent domain (2026-10-12)

`GaussianSensitivityGeometry.correction_predictableProjection_zero` and `correction_orthogonal_predictable` prove that, whenever u is independently predictable and (u,v) belongs to the original field derivative graph, the ACTUAL correction(v) is orthogonal to EVERY embedded predictable field. This follows from the proved predictable adjoint identity, J*J=identity, and the full-domain sensitivity theorem. No PRP assumption is needed and no orthogonality hypothesis is inserted.

`sensitivity_energy` proves ||D(Ju)||^2 = ||u||^2 + ||v||^2, with v the original fieldwise derivative. `sensitivity_graph_energy` adds the genuine stochastic isometry to obtain ||Ju||^2+||D(Ju)||^2 = 2||u||^2+||v||^2. Thus the stochastic term and sensitivity correction form a true orthogonal decomposition. Global Malliavin energy remains distinct from local quadratic variation; these identities do not assert a bracket formula for random volatility.

Verification: full Lake build PASS (4117 jobs); complete transitive audit PASS (2129 declarations, all five new public theorems). Explicit public types inspected. Only propext, Classical.choice, Quot.sound. No changes to original sources or dependency pins.

## Exact all-order Hilbert-component chaos lowering (2026-10-12)

`GaussianChaosLowering.component k` is the actual L2 lift of the Hilbert functional v |-> <k,v>. `component_scalarTensor` verifies its action on true finite-rank fields. `tensor_derivative_component_mem` derives order lowering directly from the normalized tensor Hermite polynomial differentiation formula, including zero-degree coordinates. `projectedGradient_finiteHermite` identifies the actual derivative of each projected finite Hermite cylinder. `component_projectedGradient_mem` extends to EVERY ambient scalar L2 input by boundedness, closedness of the lower sector, finite Hermite completeness, and the independent cylinder density.

`component_derivative_intertwining` proves <k,D Q_(n+1) F> = Q_n <k,DF> for every natural n, arbitrary Hilbert vector k, and every ORIGINAL graph pair (F,DF). It follows by applying the actual bounded component/projection map to the proved gradient series and proving all terms except order n+1 vanish. `projectedGradient_zero` handles order zero separately. `projectionDomain`, `derivative_projection_value`, and `closedDerivative_projection_component` state the same result directly using the actual closed derivative and proved domain memberships. Neither F nor k has finite-coordinate support as a hypothesis. This resolves the previously open lowering formula in all Hilbert components; a separately packaged projection on arbitrary vector-valued Gaussian L2 has not been introduced.

Verification: full Lake build PASS (4118 jobs); complete transitive axiom audit PASS (2139 declarations, all ten new public declarations). Fully explicit public theorem types elaborated. Only propext, Classical.choice, Quot.sound. No prohibited proof shortcuts found in campaign source files.

## Campaign checkpoint: resolved graph obstruction and remaining stochastic obligations (2026-10-12)

Starting HEAD: b2ddb19c878616556893e9ec3f788d301ce79de3. The campaign adds complete ambient Gaussian number sectors, all-order orthogonal chaos projections, exact scalar derivative spectral domain, same-sequence graph convergence, preservation of arbitrary correlated polynomial families and every raw Brownian past, full independently defined predictable Sobolev graph-core equality, causal support and full-domain sensitivity/rigidity, scalar and fieldwise Poincare, quantitative distance-to-deterministic-fields control, actual Gaussian conditional graph contractions, generated-space polynomial graph cores, exact orthogonal sensitivity energies, and all-order componentwise lowering. No finite chaos ceiling remains in these results.

The full independent graph equality is now established, so earlier entries listing it as missing are historical checkpoints. Brownian-generated chaos truncations and scalar graph approximants remain inside the correct generated space. They do not identify that space with the larger ambient Gaussian sigma-algebra.

Paper 1 is NOT complete. Full Brownian-generated PRP remains unproved; actual predictable representation and Clark--Ocone still cover the previously verified finite quadratic cylinders. The full-domain predictable-adjoint/projected-derivative identity is available, but does not prove that its scalar residual vanishes on every centered Brownian-generated L2 class. The new graph-core theorem must not be used as a substitute for that missing assertion.

A concrete next stochastic lemma is the space-time Hermite martingale representation H_n(B_T,T) = n J(1_(0,T] H_(n-1)(B_t,t)) for n>=1, where H_0=1, H_1=x, and H_(n+1)(x,t)=x H_n(x,t)-n*t H_(n-1)(x,t). The integrand must be constructed as a jointly predictable L2 class and the equality proved from actual stochastic sums or an independently justified generator argument. Polynomial moment bounds must control all remainder terms. Extending this to ordered disjoint increments with past polynomial factors, while proving all products integrable, would yield arbitrary finite Brownian polynomial representation. Only then can the proved generated-space polynomial density and closed range finish PRP and full Clark--Ocone. An alternative is a genuine symmetric chaos-kernel / ordered-simplex isometry; that infrastructure is also not yet established. These are outstanding formalization obligations, not counterexamples to classical Brownian PRP.

General polynomial and smooth Ito, operator/path-functional Ito, and random-volatility local quadratic variation remain open. The existing results are genuine quadratic Ito and L2 uniform-partition Brownian quadratic variation; no new pathwise or arbitrary-partition assertion was added. The proved sensitivity energy identity is global Malliavin energy and does not replace a local bracket. Random-kernel stochastic Fubini, Gubinelli remainder estimates, and IBM remain outside this checkpoint. No manuscript correction or IBM branch was begun.

Preservation: original OperatorDerivative.lean and OperatorDerivative.tex hashes match the recovered baseline; Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 remain pinned. Existing theorem bodies and all twelve unrelated untracked documents were preserved. Milestones were committed separately; nothing was pushed.

## PRP campaign P1: canonical time-space Hermite algebra and actual Gaussian covariance (2026-10-12)

Starting HEAD efe6cefd85c7c2d5ed26888515183b3d89d90e4f. `GaussianTimeSpaceHermite.polynomial` is the actual one-variable multivariate polynomial sequence defined by X*p-t*pderiv(p). `polynomial_derivative` proves the genuine lowering identity; `polynomial_recursion` proves H_(n+2)=x H_(n+1)-(n+1)t H_n. `value_zero`, `value_one`, `value_two`, and `polynomial_at_zero` fix all normalizations without division by time. Time zero and zero Hilbert directions are included.

`core` evaluates these actual polynomials in an arbitrary isonormal direction. `core_derivative` proves its actual intrinsic cylindrical derivative, and `core_memLp` proves every finite moment. `wick` uses variance ||h||^2; `wick_raising` identifies the resulting next-order polynomial with the already constructed genuine rank-one divergence. `wick_centered`, `wick_inner_succ`, `wick_inner`, and `wick_norm_sq` derive the exact all-order covariance E[H_n(W(h),||h||^2) H_m(W(k),||k||^2)] = 1_(n=m) n! <h,k>^n from Gaussian IBP. Correlated, dependent, and zero directions require no additional assumptions.

`brownianCore`, `brownianCore_coeFn`, `brownianCore_memLp`, `brownianCore_inner`, and `brownianCore_norm_sq` specialize to the existing actual Brownian process, giving covariance 1_(n=m)n!min(S,T)^n and squared norm n!T^n. This is an algebra/covariance prerequisite for P1, not yet stochastic representation, an Ito formula, or PRP.

Verification: full Lake build PASS (4119 jobs); transitive audit PASS (2173 declarations, including all 34 new public declarations); explicit public types elaborated. Only propext, Classical.choice, Quot.sound. Existing theorem bodies, pins, manuscripts and twelve untracked documents preserved.

## PRP campaign P1 complete: all-order genuine predictable Hermite representation (2026-10-12)

`GaussianHermiteStochasticSums.step` is the original actual predictable step field with polynomial past coefficient H_n(B_s,s). `integral_step` identifies its actual J value with the proved rank divergence. `terminal_step_inner`, `stepSum_norm_sq`, and `stochasticSum_error` derive an exact stochastic-sum squared L2 error from Gaussian IBP and time-interval orthogonality. No Ito formula, martingale representation, or unproved stochastic limit is used.

`GaussianHermiteRepresentation.uniform_stochasticSum_error_bound` bounds that error by (n+1)! (n+1) T^(n+1)/(N+1). `scaled_stochasticSum_tendsto` and `stochasticSum_tendsto` prove the required genuine L2 limits. Closedness of the ACTUAL J range then proves `hermite_mem_integralRange`. Only after this proof is `hermiteIntegrand` defined using J*. `integral_hermiteIntegrand` and `hermite_representation` establish H_(n+1)(B_T,T)=(n+1) J(hermiteIntegrand n T), for every n and T>=0. `stepSum_tendsto` also proves convergence of the same explicit predictable fields in the actual full predictable L2 space.

`GaussianHermiteIntegrand.brownianCore_continuous` follows from the proved covariance, not an assumed continuous process version. `hermiteIntegrand_slices` identifies the constructed field, as an equality of Gaussian L2 slices at almost every Lebesgue time, with 1_(0,T](t) H_n(B_t,t). It uses an actual almost-everywhere subsequence of the proved Bochner L2 convergence. `hermiteIntegrand_integrable_sq` supplies genuine product-measure integrability; membership in the original independently defined predictable space is built into its verified construction. `brownian_hermite_stochastic_identity` gives the terminal random-variable equality almost everywhere. `hermiteIntegrand_zero_time`, `integral_hermiteIntegrand_order_one`, and `hermiteIntegrand_order_two` verify T=0 and agreement with the existing linear and quadratic normalizations.

P1 is complete. P2 arbitrary finite Brownian polynomial representation, P3 full raw Brownian-generated PRP, and P4 full Clark--Ocone are not consequences of terminal-time Hermite representation alone and remain separate obligations. No claim about ambient PRP or general Ito is made.

Verification: full Lake build PASS (4122 jobs); complete transitive axiom audit PASS (2206 declarations, all 33 new public declarations); explicit public types checked. Only propext, Classical.choice, Quot.sound; no prohibited shortcuts. Earlier theorem bodies, dependency pins, original sources, and all twelve unrelated untracked documents preserved.

## PRP campaign P2 prerequisite: all terminal polynomials and single-observation L2 (2026-10-12)

`GaussianTerminalRepresentation.polynomial_span` proves algebraic completeness of the canonical time-space Hermite polynomials for EVERY real variance parameter, including zero. The proof uses the actual recursion to show their span is stable under multiplication by X and then ordinary polynomial induction. It does not assume a nondegenerate Gaussian law.

`centering` is the actual bounded map F |-> F-E[F]*1. `terminalPolynomial` is actual evaluation at B_T. `terminalPolynomial_hermite`, `centered_hermite_mem_range`, and `centered_terminalPolynomial_mem_range` use the independently proved P1 representation to put every centered single-time polynomial in range(J). `terminalPolynomialIntegrand` is J* of that centered random variable, and `terminalPolynomial_representation` proves its actual integral value. Defining it with J* alone is not the representation proof: range membership is proved first.

`terminalPolynomial_closure` identifies the actual closure with L2 of sigma(B_T), reusing the previously verified arbitrary-family polynomial density. `centered_terminalL2_mem_range` passes to this closure by bounded centering and closedness of range(J). `terminalL2_representation` states, for every T>=0 and F in ambient Gaussian L2 which is AEStronglyMeasurable for comap(process T), J(J*(F-E[F]))=F-E[F]. There is no derivative, smoothness, boundedness, nonzero-time, or polynomial hypothesis on F. This is representation of every SINGLE-OBSERVATION random variable; sigma(B_T) is strictly different from the entire Brownian past and Brownian-generated sigma-algebra.

Verification: full Lake build PASS (4123 jobs); complete transitive axiom audit PASS (2218 declarations, all twelve new public declarations); explicit public types elaborated. All axioms are among propext, Classical.choice, Quot.sound. No prohibited proof shortcuts. Dependency pins and original source hashes match the initial checkpoint. The twelve unrelated untracked documents are preserved; nothing pushed.

### Exact remaining multitime obligation

P2 is NOT complete. The next substantive lemma is the shifted, past-weighted Hermite identity

    G H_n(B_T-B_s,T-s)
      = n J(1_(s,T](t) G H_(n-1)(B_t-B_s,t-s)),

for 0<=s<=T, n>=1, and G any actual polynomial in finitely many observations at times <=s. Its predictable product field and its L2 integrability must be constructed, and the stochastic-sum limit must be proved with the unbounded polynomial G. A viable continuation extends the P1 exact covariance/error proof to shifted increments, using genuine independence of the entire future-increment family from the past coefficient. In particular, the weighted squared error should factor by E[G^2]; mere L2 convergence before multiplication by unbounded G does not suffice. Existing `GaussianPredictableStep.pastCoefficient_indep_increment` and `GaussianTimeDivergence` supply one-step independence, actual finite product moments, and rank divergence formulas; no general completed-integral past-factor pull-out theorem was found or assumed.

This lemma, algebraic tensor Hermite expansion in an ordered independent-increment partition, and induction over the partition would establish the requested arbitrary finite polynomial representation. Repeated observation times must be merged or zero-length intervals treated explicitly. The single-observation results above must NOT be presented as that induction, and density of the union of single-observation spaces must NOT be assumed.

P3 remains the reverse range inclusion for the FULL raw Brownian-generated centered L2 space. Existing finite-family density and closedness of J would finish it only after the multitime polynomial lemma. The previously proved forward inclusion and uniqueness are preserved. P4 remains full Brownian Clark--Ocone: the projected-derivative/J* identity is available, but full Brownian PRP has not been established in this campaign. P5 was not needed for the verified milestones. P6 was not begun, as P2--P4 are still open. No claim is made for ambient Gaussian PRP, general polynomial Ito, smooth Ito, or operator/path-functional Ito.

### Public declaration inventory for this campaign

All names below have prefix `OperatorDerivativeRewrite.Foundation.`. Locations refer to the actual new source files; every listed public declaration has a corresponding transitive audit entry.

Foundation/GaussianTimeSpaceHermite.lean: `GaussianTimeSpaceHermite.raise` (line 13); `GaussianTimeSpaceHermite.raise_smul` (line 16); `GaussianTimeSpaceHermite.pderiv_raise` (line 21); `GaussianTimeSpaceHermite.polynomial` (line 26); `GaussianTimeSpaceHermite.polynomial_zero` (line 30); `GaussianTimeSpaceHermite.polynomial_succ` (line 32); `GaussianTimeSpaceHermite.polynomial_one` (line 35); `GaussianTimeSpaceHermite.polynomial_derivative` (line 38); `GaussianTimeSpaceHermite.polynomial_recursion` (line 47); `GaussianTimeSpaceHermite.polynomial_two` (line 52); `GaussianTimeSpaceHermite.polynomial_at_zero` (line 56); `GaussianTimeSpaceHermite.value` (line 61); `GaussianTimeSpaceHermite.value_zero` (line 63); `GaussianTimeSpaceHermite.value_one` (line 64); `GaussianTimeSpaceHermite.value_two` (line 65); `GaussianTimeSpaceHermite.value_recursion` (line 67); `GaussianTimeSpaceHermite.core` (line 71); `GaussianTimeSpaceHermite.core_coeFn` (line 74); `GaussianTimeSpaceHermite.core_memLp` (line 79); `GaussianTimeSpaceHermite.core_derivative` (line 83); `GaussianTimeSpaceHermite.core_zero` (line 96); `GaussianTimeSpaceHermite.core_zero_derivative` (line 101); `GaussianTimeSpaceHermite.core_one` (line 108); `GaussianTimeSpaceHermite.wick` (line 114); `GaussianTimeSpaceHermite.wick_raising` (line 116); `GaussianTimeSpaceHermite.wick_centered` (line 145); `GaussianTimeSpaceHermite.wick_inner_succ` (line 151); `GaussianTimeSpaceHermite.wick_inner` (line 162); `GaussianTimeSpaceHermite.wick_norm_sq` (line 189); `GaussianTimeSpaceHermite.brownianCore` (line 195); `GaussianTimeSpaceHermite.brownianCore_coeFn` (line 199); `GaussianTimeSpaceHermite.brownianCore_memLp` (line 213); `GaussianTimeSpaceHermite.brownianCore_inner` (line 217); `GaussianTimeSpaceHermite.brownianCore_norm_sq` (line 224).

Foundation/GaussianHermiteStochasticSums.lean: `GaussianHermiteStochasticSums.brownianCore_past` (line 15); `GaussianHermiteStochasticSums.brownianCore_eq_pastCoefficient` (line 23); `GaussianHermiteStochasticSums.step` (line 29); `GaussianHermiteStochasticSums.integral_step` (line 33); `GaussianHermiteStochasticSums.terminal_step_inner` (line 44); `GaussianHermiteStochasticSums.stepSum` (line 64); `GaussianHermiteStochasticSums.stepSum_coe` (line 67); `GaussianHermiteStochasticSums.stepSum_norm_sq` (line 72); `GaussianHermiteStochasticSums.terminal_sum_inner` (line 82); `GaussianHermiteStochasticSums.stochasticSum_error` (line 94).

Foundation/GaussianHermiteRepresentation.lean: `GaussianHermiteRepresentation.power_increment_upper` (line 14); `GaussianHermiteRepresentation.uniform_power_error_upper` (line 32); `GaussianHermiteRepresentation.uniform_stochasticSum_error_bound` (line 63); `GaussianHermiteRepresentation.scaled_stochasticSum_tendsto` (line 75); `GaussianHermiteRepresentation.stochasticSum_tendsto` (line 88); `GaussianHermiteRepresentation.hermite_mem_integralRange` (line 94); `GaussianHermiteRepresentation.hermiteIntegrand` (line 99); `GaussianHermiteRepresentation.integral_hermiteIntegrand` (line 102); `GaussianHermiteRepresentation.hermite_representation` (line 109); `GaussianHermiteRepresentation.stepSum_tendsto` (line 113).

Foundation/GaussianHermiteIntegrand.lean: `GaussianHermiteIntegrand.brownianCore_continuous` (line 14); `GaussianHermiteIntegrand.stepValue` (line 26); `GaussianHermiteIntegrand.stepValue_on_interval` (line 30); `GaussianHermiteIntegrand.stepValue_outside` (line 44); `GaussianHermiteIntegrand.horizonValue` (line 52); `GaussianHermiteIntegrand.stepValue_tendsto` (line 55); `GaussianHermiteIntegrand.scalarCurry_stepSum` (line 80); `GaussianHermiteIntegrand.hermiteIntegrand_slices` (line 97); `GaussianHermiteIntegrand.brownian_hermite_stochastic_identity` (line 110); `GaussianHermiteIntegrand.hermiteIntegrand_integrable_sq` (line 120); `GaussianHermiteIntegrand.hermiteIntegrand_zero_time` (line 124); `GaussianHermiteIntegrand.integral_hermiteIntegrand_order_one` (line 131); `GaussianHermiteIntegrand.hermiteIntegrand_order_two` (line 138).

Foundation/GaussianTerminalRepresentation.lean: `GaussianTerminalRepresentation.polynomial_span` (line 14); `GaussianTerminalRepresentation.centering` (line 41); `GaussianTerminalRepresentation.centering_apply` (line 45); `GaussianTerminalRepresentation.terminalPolynomial` (line 50); `GaussianTerminalRepresentation.terminalPolynomial_hermite` (line 53); `GaussianTerminalRepresentation.centered_hermite_mem_range` (line 59); `GaussianTerminalRepresentation.centered_terminalPolynomial_mem_range` (line 78); `GaussianTerminalRepresentation.terminalPolynomialIntegrand` (line 90); `GaussianTerminalRepresentation.terminalPolynomial_representation` (line 93); `GaussianTerminalRepresentation.terminalPolynomial_closure` (line 104); `GaussianTerminalRepresentation.centered_terminalL2_mem_range` (line 120); `GaussianTerminalRepresentation.terminalL2_representation` (line 132).

## Long PRP campaign: shifted Hermite representation and whole-error independence (2026-10-12)

Initial HEAD fdcb0d1b22770da42deaab3ea72cf55454377e0c. Phase A is now proved without classical Ito or PRP. `GaussianShiftedHermite.incrementCore s r n` is the actual polynomial H_n(B_(s+r)-B_s,r). The direction identities prove covariance min(r,q), all finite moments, and genuine past measurability. `integral_step`, `terminal_step_inner`, `stepSum_norm_sq`, and `stochasticSum_error` derive the exact shifted stochastic-sum error from Gaussian IBP and actual J. No shifted integral or substitute domain was introduced.

`GaussianShiftedRepresentation.uniform_stochasticSum_error_bound` gives the bound (n+1)!(n+1)T^(n+1)/(N+1), independent of s. Genuine L2 convergence and closedness of range(J) prove `hermite_representation`: incrementCore s T (n+1)=(n+1) J(hermiteIntegrand s n T). `GaussianShiftedIntegrand.hermiteIntegrand_slices` identifies its actual Gaussian L2 slices with 1_(s,s+T](r) H_n(B_r-B_s,r-s), expressed using elapsed time r-s. `shifted_hermite_stochastic_identity` is the corresponding random-variable identity. `hermiteIntegrand_integrable_sq`, `hermiteIntegrand_zero_duration`, and `integral_hermiteIntegrand_order_one` prove actual product-space square integrability and the degenerate/linear cases. Every 0<=s<=t is included by T=t-s; these results impose no positive-duration condition.

The critical analytic prerequisite of Phase B is also proved. `GaussianPastFutureProducts.past_future_independent` derives independence of ANY measurable functional of the raw past at s from ANY measurable functional of the ENTIRE future-increment process, using the actual constructed process and Mathlib's `IsPreBrownianReal.indepFun_shift`. `past_future_sq_integrable`, `past_future_memLp`, and `past_future_sq_integral` establish genuine L2 multiplication and E[(GE)^2]=E[G^2]E[E^2] when both factors are square integrable. No boundedness hypothesis is used. `weighted_future_error_tendsto` derives the legitimate weighted convergence principle from this factorization, not from continuity of arbitrary L2 multiplication.

`GaussianHermiteFutureError.sumFunctional` and `errorFunctional` are explicit measurable functions of the whole future path. `integral_stepSum_coeFn` and `error_coeFn` identify the actual J sum and its whole error with those functions. `error_memLp` and `error_sq_integral` establish actual integrability and the exact norm identification. `weighted_error_sq_integrable` and `weighted_error_sq_tendsto` apply the whole-process independence to THESE stochastic-sum errors, for every measurable square-integrable past coefficient, including unbounded ones. Thus the previous weighted-error analytic obstruction is resolved; assembling and identifying the weighted predictable limit is the next obligation. Arbitrary multitime representation, full raw Brownian PRP, and full Clark--Ocone are not yet claimed.

Verification: full Lake build PASS (4128 jobs), all 60 new public types explicitly elaborated, complete transitive axiom audit PASS (2278 declarations). Only propext, Classical.choice, Quot.sound. Existing verified declarations, pins, source/manuscript files, and twelve unrelated untracked documents preserved; nothing pushed.

## Long PRP campaign Phase B: genuine unbounded-past-weighted Hermite representation (2026-10-12)

`GaussianWeightedHermite.coefficient_memLp` constructs G*H_n(B_(s+r)-B_s,r) in actual Gaussian L2 for G=a(B|_[0,s]), with a measurable and G square integrable. G is not assumed bounded, polynomial, differentiable, or finite-coordinate. `coefficient_past` proves its raw-past measurability at s+r. Actual predictable `step` and `stepSum` use the original domain and J. `integral_stepSum_coeFn`, `error_coeFn`, and `stochasticSum_error_sq` identify their whole weighted error. `scaled_stochasticSum_tendsto` and `stochasticSum_tendsto` apply the previously proved whole-error independence factorization. No arbitrary L2 multiplication continuity is invoked.

`weighted_hermite_mem_range`, `integral_hermiteIntegrand`, and `hermite_representation` prove G H_(n+1)(B_(s+T)-B_s,T)=(n+1) J(U). `stepSum_tendsto` proves actual predictable L2 convergence to U. `coefficient_difference_norm_sq` factors the squared norm of differences of running coefficients by E[G^2], and `coefficient_continuous` derives their actual Gaussian L2 continuity.

`GaussianWeightedIntegrand.hermiteIntegrand_slices` identifies U at almost every Lebesgue time, as a Gaussian L2 slice, with 1_(s,s+T](r) G H_n(B_r-B_s,r-s). `weighted_hermite_stochastic_identity` is the actual terminal random-variable identity, and `hermiteIntegrand_integrable_sq` proves product-measure integrability. `exists_unique_weighted_representation` covers EVERY real G measurable for the raw natural filtration at s and in L2, by the verified measurable-past factorization theorem. Uniqueness follows from J's actual isometry and n+1 != 0. All s,T>=0 are included, including T=0; there is no division by duration. The field is constructed and its running coefficient identified, rather than simply defined by a desired stochastic equation.

Phase B is complete for square-integrable RAW-past-measurable coefficients and hence for the intended polynomial coefficients. This is stronger than a bounded-coefficient intermediate result. Phase C arbitrary multitime polynomials is still a distinct algebraic assembly obligation; the scalar generated-space density alone has not been used as a substitute for it. Full Brownian PRP/Clark--Ocone and general Ito remain unclaimed.

Verification: full Lake build PASS (4130 jobs); complete transitive axiom audit PASS (2307 declarations, all 29 new public declarations); fully explicit public types elaborated. Only propext, Classical.choice, Quot.sound. Protected sources, earlier declarations, pins, and the twelve unrelated untracked documents preserved; nothing pushed.

## Long PRP campaign Phases C–E: multitime representation, raw Brownian PRP, and Clark–Ocone (2026-10-12)

`GaussianTimeSpaceTensor.tensorPolynomial_span` proves algebraic spanning by products of the canonical time-space Hermite polynomials at arbitrary coordinate variances. Zero variances and an empty index type are included; this is a polynomial spanning statement, not an orthogonality claim for arbitrary correlated coordinates.

`GaussianOrderedTensorRepresentation.positive_tensor_mem_range` treats any finite ordered family of nonoverlapping intervals [s_i,t_i], allowing equality of endpoints and zero durations. The last nonzero Hermite degree determines the represented increment. The other factors form an actual square-integrable coefficient measurable in its raw Brownian past (`tensorValue_memLp`, `tensorValue_past`). Phase B supplies its genuine predictable representation. All-zero tensors are constants. `centered_incrementPolynomial_mem_range` then uses the tensor span and linearity. No division by an interval length occurs.

`GaussianMultitimeRepresentation.partition_direction_span` proves the finite Hilbert-space coordinate transformation by telescoping actual time indicators. `centered_observationPolynomial_mem_range` sorts the finite observation set, prepends zero, and applies the verified polynomial linear-substitution theorem. It applies to any finite index type and arbitrary nonnegative observation times, including repetitions, zero observations, and the empty family. `centered_brownianPolynomial_mem_range` covers the entire polynomial algebra indexed by nonnegative time. `multitimePolynomial_representation` and `multitimePolynomial_exists_unique` provide actual L2 representation and isometric uniqueness, not merely a formal Hermite expansion.

`GaussianBrownianPRP.centered_brownianL2_mem_range` combines this finite-polynomial result with the previously proved polynomial density and CLOSED range of the existing isometric J. `integralRange_eq_centeredBrownianL2` proves exactly Ran(J)=L2(raw sigma(B_t:t>=0)) intersect {mean zero}. `brownian_representation` and `brownian_representation_exists_unique` identify the unique integrand as the genuine Hilbert adjoint J*F for every Brownian-generated L2 variable. No ambient Gaussian PRP is asserted: the Gaussian source includes information not generated by positive-time Brownian observations. No usual augmentation or continuous-path modification has been introduced.

`GaussianBrownianPRP.clark_ocone` proves F-EF=J(predictableProjection(DF)) for F in the EXISTING closed cylindrical derivative domain AND Brownian-generated L2. `clark_ocone_representer_unique` identifies any such representer. `multitime_representer_agrees` establishes compatibility with the polynomial construction. The proof uses the previously verified full-domain identity J*F=predictableProjection(DF); no derivative of an arbitrary nondifferentiable L2 variable is asserted. Thus C, D and E are complete on the stated raw Brownian domains.

Verification: complete Lake build PASS (4134 jobs), complete transitive axiom audit PASS (2336 declarations, all 29 new public declarations), all new public types elaborated explicitly. Only propext, Classical.choice, Quot.sound. No prohibited proof shortcuts. Existing verified declarations, pins, original sources/manuscripts and twelve unrelated untracked documents preserved. Polynomial/time-dependent Ito and the manuscript's stronger operator-functional Ito remain distinct obligations; full PRP is not being presented as an Ito proof.

## Long PRP campaign Phase F analytic prerequisite: justified stochastic Fubini and C1-weighted Hermite Ito (2026-10-12)

`BochnerL2Fubini.columns_integrable` proves almost every column integrable for a finite parameter measure and a uniform majorant. `pairing_integrable` proves actual product-measure integrability against every L2 test vector when the majorant is L2. `integral_eq_of_slices` then identifies an L2-valued Bochner integral by pointwise column integrals using genuine Fubini and Hilbert duality. This avoids the invalid use of pointwise evaluation as a continuous functional on L2.

`GaussianHermiteTimeIntegral.hermiteIntegrand_continuous`, `hermite_time_integrable`, and `core_time_integrable` establish genuine continuity and Bochner integrability on every finite time interval. `integratedHermite` is an integral in the original closed predictable Hilbert space. `integral_integratedHermite` proves J commutes with this integral by the continuous-linear-map integration theorem; all integrability hypotheses are independently proved, not inferred from totalized integrals.

`GaussianHermiteTimeKernel.kernel_bound` supplies a uniform L2 majorant on [0,T]. `kernel_column` computes the actual column integrals using FTC under Continuous q and HasDerivAt a (q t) t at every t. `integratedHermite_slices` identifies the Bochner field with 1_(0,T](r) (a(T)-a(r)) H_n(B_r,r). Negative times and zero horizons are handled explicitly. `tailField` is constructed via proved L2 membership, not by a prescribed stochastic equation.

`GaussianWeightedTimeHermite.weightedIntegrand_slices` identifies the actual predictable field U with 1_(0,T](r) a(r) H_n(B_r,r). `weighted_hermite_ito` has the exact hypothesis ContDiff R 1 a and uses Mathlib deriv a; it gives ONE U with both this slice formula and a(T)H_(n+1)(B_T,T)=(n+1)J(U)+integral_0^T a'(t)H_(n+1)(B_t,t)dt. Product-space square integrability is proved. The intermediate `weighted_hermite_identity` is an algebraic identity for arbitrary continuous q; its interpretation as a weighted running stochastic integral requires the separate actual-derivative slice theorem, and the combined public Ito theorem includes it.

Two approaches to arbitrary polynomial Ito were compared: direct telescoping polynomial sums would require new high-moment remainder and centered quadratic-sum estimates; deterministic integration of existing Hermite identities reuses the all-order verified stochastic sums. The latter is now analytically justified. Remaining Phase F work is the bivariate time-space Hermite spanning/heat algebra and its linear assembly into arbitrary polynomial Ito. No smooth C2 or operator-functional Ito is claimed.

Verification: full Lake build PASS (4138 jobs); transitive axiom audit PASS (2359 declarations, all 23 new public declarations); all new public types explicitly elaborated. Only propext, Classical.choice, Quot.sound. Protected files, previous proofs, dependency pins and twelve unrelated untracked documents preserved; nothing pushed.

## Long PRP campaign Phase F: arbitrary polynomial and time-dependent polynomial Ito (2026-10-12)

`GaussianPolynomialHeat` works with actual MvPolynomial (Fin 2) R, with coordinate 0=time and 1=space. `mixed_pderiv` proves commuting polynomial partials. `heat` is EXACTLY pderiv 0 + (1/2) pderiv 1 composed with pderiv 1. `hermite_heat`, `basis_heat`, and `basis_spatial_succ` establish the backward-heat and lowering identities. `basisPolynomial_span` proves that t^k H_n(x,t) span ALL bivariate polynomials. `specialize_hermite`, `specialize_basis`, and `eval_specialize` identify them with the already constructed time-space Hermite family; no derivative data are prescribed independently.

`GaussianPolynomialProcess.valueL2_coeFn` identifies evaluation with p(t,B_t). `valueL2_continuous` derives genuine L2 continuity by the proved algebraic span and Hermite covariance continuity. `valueL2_intervalIntegrable` proves every finite-time drift Bochner-integrable in Gaussian L2. `timeIntegral` is a genuine linear time-integration map. Zero degree and zero time are handled explicitly. `noiseTarget` is the terminal-minus-initial-minus-heat-drift linear map, not an assumed representation.

`GaussianPolynomialIto.spatialValue`/`spatialField` construct the actual L2-in-time field 1_(0,T] (partial_x p)(t,B_t), independently of its predictability and stochastic equation. `basis_representation` proves both its original predictable-domain membership and its stochastic value using the C1-weighted Hermite/Fubini theorem. `polynomial_representation` extends by the proved span. `polynomial_ito` supplies a UNIQUE actual predictable U, with scalarCurry U=spatialField T p and p(T,B_T)-p(0,B_0)=J(U)+integral_0^T (partial_t p+(1/2)partial_xx p)(t,B_t)dt. These are genuine Gaussian L2 identities with Bochner drift integrals. The theorem includes T=0 and all polynomial degrees.

`GaussianPolynomialDifferentiation.eval_hasDerivAt_space`, `eval_hasDerivAt_time`, and `heat_eval_actual` verify these partials are ACTUAL Mathlib real derivatives, including the second derivative. `spatialPolynomial_spatial` and `spatialPolynomial_heat` identify the embedded univariate Polynomial.derivative and its second derivative.

`GaussianScalarPolynomialIto.scalar_polynomial_ito` is the standard arbitrary real Polynomial corollary: ONE unique U has slices 1_(0,T] p'(B_t), and p(B_T)-p(0)=J(U)+(1/2)integral_0^T p''(B_t)dt. `polynomialValue_coeFn` identifies all scalar random variables, `polynomialValue_zero` proves the B_0=0 specialization, and `polynomialValue_intervalIntegrable` proves the time integrability. No boundedness restrictions on polynomials were introduced. The drift is a genuine Gaussian-L2 Bochner integral; no simultaneous pointwise path version is being asserted without its separate measurable-version argument.

The original manuscript's general operator-functional Ito is NOT thereby proved. In C:/Operator/OperatorDerivative.tex around the thm:ito proof (lines 839 onward), Step 2 replaces the projected derivative of a terminal composition by a running-time composition without the necessary conditional projection calculation. Step 4's mean-to-random-integrand replacement is not implied by continuous-linear-map Fubini alone. Our proof instead constructs the running derivative field, proves stochastic Fubini with L2 domination, and computes the full random drift. A formal cubic diagnostic is being developed separately. No original manuscript or legacy claim has been silently edited. Smooth C2/C1,2, arbitrary semimartingale, general Volterra/fBM and operator-functional Ito remain separate mathematical obligations.

Verification: full Lake build PASS (4143 jobs); complete transitive axiom audit PASS (2419 declarations, all 60 new public declarations including the polynomial type abbreviation); all new public types explicitly elaborated. Only propext, Classical.choice, Quot.sound. No prohibited proof shortcuts. Prior declarations, original source/manuscript, pinned dependencies and twelve unrelated untracked documents preserved; nothing pushed.

## Long PRP campaign: quantitative terminal/running derivative diagnostic (2026-10-12)

`Foundation/GaussianCubicDiagnostic.lean` proves the actual terminal representer of B_T^3 is 1_(0,T](r) 3(B_r^2+T-r). `cubic_predictableAdjoint` identifies the existing Hilbert adjoint J*, `cubicIntegrand_slices` gives its genuine L2-time slices, and `cubic_spatial_value` identifies the actual running polynomial derivative 3 B_r^2. `cubic_projection_difference_slices` proves their difference is 1_(0,T](r) 3(T-r), and `cubic_projection_difference_norm_sq` computes its EXACT squared TimeScalarL2 norm as 3 T^3. `cubic_projection_ne_running_derivative` proves non-equality for every T>0; T=0 is included in the norm identity. No representer or derivative identity is an assumption.

This independently verified polynomial diagnostic exposes the projection substitution in the original manuscript's thm:ito proof, Step 2 (C:/Operator/OperatorDerivative.tex, lines 867-870). It is not presented as a counterexample satisfying that theorem's bounded-C3 hypothesis: the cubic is unbounded. The separate bounded smooth case and the general operator-functional Ito claim remain analytic obligations. Our proved polynomial Ito includes the necessary random drift and does not use that substitution.

Verification: full Lake build PASS (4144 jobs); complete transitive axiom audit PASS (2429 declarations, all 10 new public declarations); fully explicit public types elaborated. Only propext, Classical.choice, Quot.sound. No prior proof bodies, pins, original sources or unrelated untracked documents changed. Nothing pushed.

## Long PRP campaign Phase G: raw conditional Ito and conditional Clark--Ocone (2026-10-12)

`GaussianPredictableCutoff.cut` is the actual restriction to (0,T] followed by zero extension in Lebesgue-time times Gaussian L2. `cut_coeFn`, `cut_norm_le`, `cut_inner`, `cut_cut`, `cut_tensor`, and `sub_cut_tensor` prove its representative formula, contraction, symmetry, nested projection law, and exact elementary-step splitting. `cut_mem` proves that it preserves the EXISTING independently defined full predictable domain using the previously established finite-horizon zero-extension theorem. `predictableCut` is the restricted continuous linear map. `cut_tendsto` proves strong L2 convergence along integer horizons, including all nonpositive-time support cases, by genuine dominated convergence.

`GaussianConditionalIto.pastProjection` is the existing Mathlib L2 orthogonal conditional projection for the raw natural filtration, with its actual conditional-expectation identification `pastProjection_ae`. The calculation `pastPolynomial_inner_future_increment` uses the actual polynomial derivative, product rule and Gaussian Stein identity; both past factors have zero directional derivative in the future increment. All pairings are genuine L2 inner products, and the polynomial products have the previously proved finite moments. `integral_cut_step_mem_past` and `pastPolynomial_inner_future_step` handle intervals before, after, and straddling T, including empty pieces. `integral_cut_mem_past` and `past_inner_future_integral` pass to the TWO independently proved dense spaces: polynomial predictable steps and polynomials in the full raw past. `pastProjection_integral` proves E[J(U)|F_T]=J(1_(0,T] U) for EVERY original full-predictable L2 integrand U. No martingale or conditional interchange is assumed.

`GaussianConditionalClarkOcone.natural_le_brownian` proves the sigma-algebra inclusion. `past_representation` and `predictableAdjoint_pastProjection` identify the actual cutoff of J*F with the unique representer of E[F|F_T]-EF. `conditional_representation` and `conditional_representer_unique` prove F-E[F|F_T]=J((I-cut_T)J*F) for every Brownian-generated L2 F. `future_representer_coeFn` identifies the actual field as 1_(T,infinity) times the original U; endpoints are harmless but explicitly fixed, and positive-time support is used. `conditional_clark_ocone` replaces J*F by the independently verified predictable projection of the closed derivative ONLY for F in its genuine domain. `conditional_variance_identity` gives the exact squared L2 error. `past_representer_supported` and `finite_horizon_representation` prove unique representation supported in (0,T] for every F in the raw past L2, rather than presuming finite support. `pastProjection_tendsto` establishes L2 convergence E[F|F_n] -> F on the entire Brownian-generated space using actual cutoff exhaustion.

These are raw-filtration assertions, not usual augmentation or simultaneous continuous versions. No claim of ambient Gaussian PRP is made. The cutoff of the projected terminal derivative is not replaced by an unproved running derivative; the cubic diagnostic remains applicable. General smooth or operator-functional Ito is still separate.

Verification: full Lake build PASS (4147 jobs); complete transitive axiom audit PASS (2467 declarations, all 38 new public declarations); fully explicit public types elaborated. Only propext, Classical.choice, Quot.sound. Prior proofs, original manuscripts/sources, pins and unrelated untracked documents preserved; nothing pushed.

## Long PRP campaign Phase G: actual polynomial martingales and conditional Dynkin formula (2026-10-12)

`GaussianHermiteMartingale.scalarCurry_cut` identifies actual time cutoffs with sliced L2 indicators, using the proved product-measure AE Fubini theorem. `cut_hermiteIntegrand` proves horizon consistency. `pastProjection_brownianCore` and `hermite_condExp` establish E[H_n(B_T,T)|F_S]=H_n(B_min(S,T),min(S,T)) and its ordered-time specialization, including n=0 and zero/repeated times. `hermite_integrable` proves actual integrability; `hermite_martingale` establishes Mathlib's Martingale predicate for the original adapted polynomial functions, not just an L2 equation or a supplied martingale field.

`GaussianPolynomialMartingale.cut_polynomial_integrand` compares the genuine polynomial running-gradient fields across horizons. `pastProjection_noiseTarget` proves the conditional martingale identity for every heat-compensated bivariate polynomial in Gaussian L2, with its genuine Bochner drift. `valueL2_zero` identifies the deterministic initial value. `evaluation_stronglyAdapted`, `evaluation_integrable`, and `valueL2_mem_past` supply actual raw measurability and integrability. `pastProjection_heatPolynomial` and `heatPolynomial_martingale` apply to EVERY real bivariate polynomial p with the explicit algebraic PDE heat p = partial_t p + (1/2)partial_xx p = 0. The PDE is not an assumed conditional expectation: the latter is derived from the previously constructed Ito integrands. The existing `GaussianPolynomialDifferentiation.heat_eval_actual` independently identifies the partials with actual Mathlib derivatives.

`polynomial_conditional_drift`, `pastProjection_timeIntegral`, and `polynomial_conditional_dynkin` establish E[p(T,B_T)|F_S]-p(S,B_S)=E[integral_S^T heat p(r,B_r)dr|F_S] for all nonnegative S<=T. The drift is an actual Gaussian-L2 Bochner integral. Its adaptedness is proved by conditional projection commuting with that integral and the actual integrability of the continuous polynomial curve. No pointwise path-integral representative, smooth approximation, or arbitrary operator-functional Ito is smuggled into the statement.

Verification: full Lake build PASS (4149 jobs); complete transitive axiom audit PASS (2484 declarations, all 17 new public declarations); fully explicit public types elaborated. Only propext, Classical.choice, Quot.sound. Protected sources, prior declarations, pins and unrelated untracked documents preserved; nothing pushed.

## Long PRP campaign Phase G: unbounded past-weighted quadratic variation (2026-10-12)

`GaussianWeightedHermiteOrthogonality.coefficient_norm_sq` proves the exact identity E[(G H_n(delta B,r))^2]=E[G^2] n! r^n using independence of the WHOLE future process from the raw past and the verified Hermite norm. G is an arbitrary measurable function of the entire raw past with MemLp G 2; it is not required to be bounded or polynomial. `cut_weightedIntegrand_of_le` identifies the genuine weighted Hermite integrand as zero before its starting time. `pastProjection_coefficient_zero` proves conditional mean zero for positive-order weighted increments. `past_inner_coefficient_zero` and `coefficient_inner_of_disjoint` prove actual L2 orthogonality against the entire past and between ordered disjoint weighted increments. No all-L2 multiplication or independence between the weights themselves is assumed.

`GaussianWeightedQuadraticVariation.errorTerm` is the genuine L2 class G_i*((B_ti+1-B_ti)^2-delta_i); `errorTerm_coeFn` and `weightedError_coeFn` identify the representatives. Each G_i is parametrized by a measurable function a_i of the whole raw past up to t_i. The previously proved `GaussianPredictableStep.measurable_natural_iff_exists_pastCoefficient` shows this parametrization covers every raw-past measurable real coefficient. No finite-coordinate hypothesis is introduced. `errorTerm_norm_sq`, `errorTerm_inner_lt`, and `weightedError_norm_sq` prove EXACTLY

    ||sum_i G_i*((delta B_i)^2-delta_i)||_2^2 = 2 sum_i delta_i^2 E[G_i^2].

The only hypotheses for this equality are a finite monotone nonnegative-time partition (repeated times and the empty partition allowed), measurability of each raw-past coefficient, and its actual square integrability. All sums are formed from already proved L2 classes. `weightedError_mesh_bound` gives the upper bound 2*M*epsilon*(last_time-first_time) if E[G_i^2]<=M, M>=0 and each interval length<=epsilon. `weightedError_tendsto_of_mesh` proves genuine Gaussian-L2 convergence to zero for arbitrary sequences of such partitions with bounded total duration, vanishing nonnegative mesh bounds, and uniformly bounded coefficient SECOND moments. The coefficients may vary with the partition and need not be essentially bounded. This establishes the weighted random quadratic correction required for a future Taylor proof; it is not merely convergence of expected quadratic variation.

Verification: full Lake build PASS (4151 jobs); complete transitive axiom audit PASS (2498 declarations, all 14 new public declarations); fully explicit public types elaborated. Only propext, Classical.choice, Quot.sound. All campaign source files scanned for prohibited proof shortcuts. Previous proofs, original source/manuscript hashes, dependency pins and twelve unrelated untracked documents preserved; nothing pushed.

### Remaining smooth and operator-functional Ito obligations; two routes assessed

Route 1 (adapted Taylor sums) now has actual first-order predictable stochastic integration, arbitrary polynomial Ito, raw conditional projections, and weighted quadratic-variation convergence. It still needs a theorem controlling actual third-order Taylor remainders in L2 (for a bounded-C3 core, sixth Gaussian increment moments and a quantitative remainder bound), convergence of adapted derivative step fields to the running derivative field, and convergence of the ordinary drift Riemann sums in Gaussian L2. Pinned Mathlib supplies `taylor_mean_remainder_lagrange_iteratedDeriv` and `taylor_mean_remainder_bound` in Mathlib/Analysis/Calculus/Taylor.lean; their deterministic estimates are not by themselves the missing stochastic L2 estimate. This route avoids falsely treating terminal conditional gradients as running derivatives.

Route 2 (pass from polynomial Ito by approximation) needs ONE sequence with compatible terminal-value, initial-value, running first-derivative L2, and running second-derivative Bochner convergence. Existing GaussianSobolevGlobalApprox supplies first-order Gaussian graph approximation, not the second-order/time-family theorem. Local C2 polynomial approximation alone does not control Gaussian tails; cutoff approximants are no longer polynomials, and stopped-process Ito would itself require a localization theorem. No such convergence has been assumed. The first route is currently shorter; the new weighted estimate is a substantive completed prerequisite.

The original manuscript's abstract operator-functional claim remains unresolved. C:/Operator/OperatorDerivative.tex:809-810 still asserts an invalid L2-times-L2-to-L2 consequence in rem:domain; ordinary Cauchy--Schwarz yields L1 there. The implication from gamma>=H to 2gamma+2H>=2gamma+1 in the Skorokhod-remainder proof is algebraically false for H<1/2. The projection substitution in thm:ito Step 2 has the verified cubic diagnostic, though the cubic is not a bounded-C3 counterexample. The mean-to-random-integrand step is not supplied merely by bounded-operator Bochner Fubini. None of these manuscript statements or protected files were edited. A valid Brownian smooth Ito result would still not establish the general Volterra or operator-functional theorem.

### Campaign status using the preceding P2--P6 labels

P2: COMPLETE, arbitrary finite multitime polynomial representation, including repeated/zero observations; no terminal-only substitution. P3: COMPLETE on the full raw Brownian-generated centered L2 space, with genuine isometric closed range; no ambient Gaussian PRP. P4: COMPLETE on the existing closed derivative domain intersected with Brownian-generated L2, now also conditional and finite-horizon forms. P5: the optional general projected conditional-gradient tensor formula was not needed and is not claimed; the actual time-cutoff/conditional-expectation identities and conditional Clark--Ocone were proved. P6: COMPLETE for all univariate and bivariate time-dependent polynomials, with actual derivatives, genuine predictable integrands, and Bochner drift; also Hermite/heat-polynomial martingales and conditional Dynkin. Smooth, multivariate stochastic, and general operator-functional Ito remain open with the exact missing analytic steps above.

## Close Brownian chapter I: continuous adapted fields and Lipschitz compositions (2026-10-12)

New `Foundation/GaussianContinuousIntegrands.lean`: `partition_tendsto` (line 123) proves strong product-L2 convergence of uniform left-endpoint step fields for EVERY continuous curve v : nonnegative real time -> GaussianL2. `runningField` (line 99) is defined independently by the actual Bochner-L2 slices 1_(0,T] v(t); `runningField_slices` identifies them. `runningField_mem` (line 177) proves membership in the pre-existing, independently predictable-measurable domain if each v(t) is AE raw-past measurable. `predictableStep_tendsto`, `integral_step_tendsto` (line 201), and `integral_step_coeFn` (line 208) prove convergence of the existing J applied to those steps and identify every step integral with the actual sum v(t_i)(B_(t_i+1)-B_ti). `drift_sum_tendsto` (line 243) proves convergence of the ordinary duration-weighted left sums to the actual Gaussian-L2 Bochner time integral. The proofs use compact-time norm bounds, actual integrability, dominated convergence, closedness of the verified predictable domain, and the existing isometry J. They do not assume a stochastic representation or path continuity. All statements include T=0.

New `Foundation/GaussianLipschitzIntegrands.lean`: `composition` and `composition_coeFn` (lines 25, 28) construct actual phi(A) in Gaussian L2 for any K-Lipschitz real phi, allowing phi(0) nonzero. `composition_norm_sub_le` (line 45) proves the K-Lipschitz estimate on equivalence classes. `valueL2_continuous`, `valueL2_past`, and `valueL2_increment_bound` (lines 68, 71, 77) prove continuity/adaptation of phi(B_t) and ||phi(B_t)-phi(B_s)||_2^2 <= K^2(t-s), s<=t. `integrand_slices`, `integrand_integrable_sq`, `stochastic_sum_tendsto`, `stochastic_sum_coeFn`, and `drift_sum_tendsto` (lines 88--114) identify and approximate the actual running phi(B_t) field and its stochastic/drift integrals. `deriv_lipschitz` (line 122) uses the actual Mathlib derivative: differentiability of deriv f and a uniform nnnorm bound on deriv(deriv f) give a Lipschitz running first derivative. No arbitrary derivative candidate is substituted.

Scope: A3/A4/A5 are established for continuous adapted Gaussian-L2 curves, with explicit actual Lipschitz-composition applications. Applying to f' and f'' requires their stated regularity/bounds. This is not yet smooth Ito: the Taylor remainder and final second-order assembly remain separate. Neither C2-general, time-dependent smooth Ito nor the original operator-functional theorem is claimed.

Verification: full Lake build PASS (4153 jobs); transitive axiom audit PASS (2537 declarations, 39 new public declarations), only propext, Classical.choice, Quot.sound. All public declarations elaborated with explicit types. Prior verified source bodies, dependency pins, original manuscripts and twelve unrelated untracked documents preserved. Nothing pushed.

## Close Brownian chapter II: actual Taylor remainders and sixth moments (2026-10-12)

`Foundation/GaussianTaylorRemainder.lean`: `remainder` (line 17) is exactly f(y)-f(x)-f'(x)(y-x)-(1/2)f''(x)(y-x)^2, with actual Mathlib derivatives. `remainder_bound` (line 20) assumes ContDiff real 3 f and a uniform real bound M on the norm of iteratedDeriv 3 f, and proves |R(x,y)| <= (M/6)|y-x|^3. It treats equal endpoints separately and uses Mathlib's Lagrange remainder with verified identification of interval and ordinary derivatives. No boundedness of f, f', or f'' is required for this estimate.

`cube_coeFn`, `cube_norm_sq`, `incrementCube_coeFn`, and `incrementCube_norm_sq` (lines 51--91) derive the actual sixth moment E[(B_t-B_s)^6]=15(t-s)^3 for s<=t. The proof realizes W(h)^3 as H3(W(h))+3||h||^2 H1(W(h)) and uses the already verified Hermite orthogonality; it imports no moment assumption. `remainder_measurable`, `remainder_memLp`, `remainderL2_coeFn`, and `remainderL2_norm_sq` (lines 92--135) establish actual measurability, square integrability and ||R(B_s,B_t)||_2^2 <= 15(M/6)^2(t-s)^3. `remainderSum_coeFn`, `remainderSum_norm_sq`, and `remainderSum_tendsto` (lines 147--194) prove the actual uniform-partition Taylor error sum has squared norm <= 15(M/6)^2 T^3/(N+1) and tends to zero in Gaussian L2. Independence of remainder terms is NOT assumed: finite-sum Cauchy--Schwarz is proved as `norm_sum_sq_le`.

`Foundation/GaussianLipschitzQuadraticVariation.lean`: `weight` evaluates an actual Lipschitz function at the last raw-past coordinate; measurability and MemLp are proved. `error_coeFn` (line 28) identifies the genuine sum phi(B_ti)[(delta B_i)^2-delta t_i]. `weight_energy` and `error_tendsto` (lines 35, 45) prove its Gaussian-L2 convergence to zero by applying the previously verified weighted mesh theorem. Phi need not be bounded: compact-time boundedness of its Gaussian-L2 norm follows from the previous milestone's continuity. No adapted independence or Gaussian moments are assumed anew. Horizon zero is included.

Verification: complete Lake build PASS (4155 jobs); all 2562 transitive axiom checks PASS, including all 25 new public declarations; only propext, Classical.choice, Quot.sound. Public elaborated theorem types inspected. This completes the quantitative A1 prerequisite for the explicitly restricted C3 class; it does not yet claim C2-general, time-dependent, or operator-functional Ito. Protected original files, prior declarations, pinned dependencies and twelve unrelated documents unchanged.

## Close Brownian chapter III: genuine restricted smooth scalar Ito (2026-10-12)

`Foundation/GaussianSmoothIto.lean` now assembles scalar smooth Ito from the preceding independently proved limits. `finite_taylor_identity` (line 37) is an EXACT Gaussian-L2 identity for each uniform partition: the terminal increment equals the actual predictable stochastic sum plus one half the sum of the weighted quadratic-variation error and ordinary second-derivative drift sum, plus the actual Taylor remainder sum. Its proof is pointwise telescoping after all constituent terms have already been proved square integrable; it never invokes a stochastic chain rule.

`ito_of_lipschitz_derivatives` (line 86) assumes ContDiff real 3 f, explicit Lipschitz bounds for f, deriv f, and deriv(deriv f), and a finite uniform bound M for iteratedDeriv 3 f. For EVERY nonnegative T, it proves in the actual Gaussian L2 space:

    f(B_T)-f(B_0) = J(integrand f' T) + (1/2) integral_0^T f''(B_t) dt.

The running integrand is the previously independently defined predictable product-L2 field, with its actual slices proved in GaussianLipschitzIntegrands.integrand_slices/valueL2_coeFn. The drift is the actual Gaussian-L2 Bochner integral. `bounded_derivatives_ito` (line 103) derives all three Lipschitz hypotheses from C3 plus uniform bounds on the ACTUAL first, second, and third derivatives; no boundedness of f is imposed. Its existential Lipschitz proofs supply concrete existing L2 compositions, not assumed stochastic conclusions. `valueL2_zero`, `drift_integrable`, and `smooth_ito_ae` (lines 128, 136, 143) identify the deterministic initial value f(0), explicitly establish drift integrability, and give the AE random-variable formula. Zero horizon is included in all results.

Scope and limitations: this is genuine scalar Brownian Ito for C3 with bounded first three derivatives, hence covers smooth compactly supported functions and affine functions, among others. It is NOT general C2, C1,2 time-dependent, or the manuscript's abstract functional/Volterra theorem. No pathwise simultaneous-in-time version or pointwise path-time integral identification is claimed. The original operator-functional proof's terminal-projection substitution is not used.

Verification: full Lake build PASS (4156 jobs); transitive axiom audit PASS (2570 declarations, all 8 new public declarations). All elaborated public types inspected. Only propext, Classical.choice, Quot.sound. Existing proofs and original files preserved; dependency pins unchanged; no push.

## Close Brownian chapter IV: conditional smooth calculus and a restricted functional repair (2026-10-12)

`Foundation/GaussianSmoothConditional.lean`: `cut_predictableField` (line 16) proves the exact cutoff/min-horizon identity for ANY continuous adapted Gaussian-L2 curve; `cut_integrand` (line 40) specializes it to actual Lipschitz Brownian functions. `pastProjection_drift` (line 44) proves raw-past measurability of the actual Bochner drift through conditional projection and justified integral commutation. Under the explicit scalar C3/Lipschitz/bounded-third-derivative hypotheses, `pastProjection_compensated` (line 65) proves the conditional martingale identity of f(B_t)-(1/2)integral_0^t f''(B_s)ds. `smooth_conditional_dynkin` (line 80) proves C_S f(B_T)-f(B_S)=(1/2)C_S integral_S^T f''(B_t)dt for S<=T. These are actual Gaussian-L2 conditional projections, identified with Mathlib conditional expectation by the existing `pastProjection_ae`; no unproved raw measurability of arbitrary chosen representatives is asserted.

`Foundation/GaussianSmoothCylinders.lean`: `cylinder` (line 15) independently defines Phi(x)=sum_i f_i(x_i). `cylinder_directional_hasDerivAt` (line 17) and `cylinder_second_directional_hasDerivAt` (line 28) prove its genuine directional differential and diagonal Hessian by actual Mathlib differentiation. `stoppedValue` and `stoppedValue_coeFn` (lines 43,45) give the actual L2 class sum_i f_i(B_min(T,r_i)). `stoppedIntegrand_slices` (line 56) identifies the predictable integrand as 1_(0,T](t) sum_i 1_(0,r_i](t) f_i'(B_t). `stoppedDrift` (line 83) specifies the correction using actual second derivatives. `stopped_cylinder_ito` (line 89) proves the stochastic change-of-variables formula for these additive stopped-observation cylinders by the already proved scalar theorem and genuine J linearity. Arbitrary finite dimensions, empty families, zero and repeated observation times are included. This is a useful restricted smooth path-functional theorem, not an arbitrary nonlinear mixed cylinder theorem. No unknown gradient or correction is prescribed to force the identity.

`PAPER1_BROWNIAN_ITO_REPAIR.md` supplies the focused original-claim/dependency map and precise mathematical verdict. It distinguishes full unbounded D from bounded J*, diagnoses the intrinsic-bracket time-type problem, retains the cubic diagnostic as polynomial-only, and records that the original time-indexed Lean theorem is a divergence product identity rather than the manuscript's stochastic Ito formula. The original source/manuscript remain untouched. The manuscript theorem still needs revision; neither new smooth scalar Ito nor the additive functional theorem proves its full abstract/Volterra statement.

Source-location clarification for the preceding two entries (authoritative declaration starts): GaussianTaylorRemainder.remainder 16, remainder_bound 19, cube_coeFn 54, cube_norm_sq 72, incrementCube_norm_sq 86, remainder_memLp 104, remainderL2_norm_sq 121, remainderSum_coeFn 146, remainderSum_norm_sq 163, remainderSum_tendsto 184. GaussianSmoothIto.finite_taylor_identity 39, ito_of_lipschitz_derivatives 83, bounded_derivatives_ito 99, valueL2_zero 122, drift_integrable 129, smooth_ito_ae 135.

Verification: full Lake build PASS (4158 jobs); transitive axiom audit PASS (2584 declarations, all 14 new public declarations), only propext, Classical.choice, Quot.sound. Explicit public theorem types inspected and new sources scanned. Prior sources and original files, pins, and twelve unrelated untracked documents preserved. Nothing pushed.

## Close Brownian chapter V: justified time weighting and separable smooth time dependence (2026-10-12)

`Foundation/GaussianContinuousStochasticFubini.lean`: `kernel_stronglyMeasurable` (22), `kernel_bound` (29), and `kernel_column` (47) establish measurability, an actual L2 majorant, and the ordinary FTC column integral for 1_(0<x<=t) q(t) v(x), v a continuous Gaussian-L2 curve. Given a continuous predictable-field curve U whose actual slices are 1_(0,t]v, `integrated_slices` (100) proves the Bochner integral of q(t)U_t has slices 1_(0,T](x)(a(T)-a(x))v(x), whenever q is continuous and is an actual derivative of a. This uses the already verified BochnerL2Fubini.integral_eq_of_slices and proves its domination hypotheses, not an unchecked pointwise evaluation map on L2. `weighted_slices` (127) identifies a(T)U_T-integral qU with the desired time-weighted field. `integral_weighted_field` (147) is the justified existing-J Fubini identity. In the application below q is exactly Mathlib deriv a and all U hypotheses are proved.

`Foundation/GaussianTimeWeightedSmoothIto.lean`: `primitive_hasDerivAt` (21) and `weighted_primitive_identity` (49) establish actual Bochner FTC/integration by parts. `weightedField` (30) is defined independently through GaussianContinuousIntegrands.predictableField for the actual curve a(t)phi(B_t); `weightedField_slices` (37) identifies it. For the already verified C3 spatial core, `smooth_integrand_continuous` (74) PROVES horizon continuity of the genuine spatial-derivative field, using the established scalar Ito identity and the J isometry. `weightedField_eq` (89) then identifies the independently constructed weighted field with the time-Fubini expression. There is no circularity: scalar Ito preceded this argument and used Taylor sums, not time-weighted Ito.

`time_weighted_ito` (104) and `time_weighted_ito_combined` (152) prove, for a : real -> real of class C1 and f in the explicit scalar C3/Lipschitz/bounded-third-derivative core,

    a(T) f(B_T)-a(0) f(B_0)
      = J(1_(0,T] a(t) f'(B_t))
        + integral_0^T [a'(t) f(B_t) + (1/2) a(t) f''(B_t)] dt.

The drift is genuinely integrable in Gaussian L2, and the stochastic field is in the existing predictable product L2 domain. There is no global bound imposed on a or a': compact-time continuity supplies all required estimates. `time_partial` (167), `space_partial` (170), and `second_space_partial` (173) independently prove the actual first time derivative and first/second space derivatives of a(t)f(x). This is a genuine restricted time-dependent smooth theorem, C1 in time and C3 in space; it is NOT an arbitrary nonseparable C1,2 theorem. Every result allows T=0.

Verification: full Lake build PASS (4160 jobs); transitive axiom audit PASS (2607 declarations, all 23 new public declarations); explicit elaborated types inspected. Only propext, Classical.choice, Quot.sound. Prior proofs, pins, original files and twelve unrelated documents preserved; nothing pushed.

## Brownian campaign VI — explicit smooth heat martingales (2026-10-12)

`Foundation/GaussianSmoothHeatMartingale.lean` derives martingales from an independently stated differential equation, not from a martingale or stochastic representation hypothesis. The scalar function f is C3, f/f'/f'' are globally Lipschitz, and its actual third derivative is uniformly bounded. The time coefficient a is C1. The only additional mathematical hypothesis is the explicit backward heat equation a'(t)f(x)+(1/2)a(t)f''(x)=0 for t >= 0.

- `heat_drift_zero` (line 31), `heat_representation` (47): the actual Bochner drift vanishes; a(T)f(B_T)-a(0)f(0) equals J of the independently specified predictable field 1_(0,T] a(t)f'(B_t).
- `heat_projection` (67), `heat_condExp` (78), `heat_martingale` (89): actual orthogonal projection, conditional expectation, and Mathlib Martingale statements, including time zero. Strong adaptation is proved for the explicitly chosen pointwise process.
- `heat_mean` (97) gives a(T)E[f(B_T)]=a(0)f(0).
- `expHalf_deriv` (117), trigonometric Lipschitz/third-derivative bounds (120–143), and `sin_heat_equation` / `cos_heat_equation` (147/152) prove the concrete hypotheses.
- `sin_heat_martingale` (157) and `cos_heat_martingale` (164) prove that exp(t/2)sin(B_t) and exp(t/2)cos(B_t) are actual martingales. `cos_mean` (171) derives E[cos(B_T)]=exp(-T/2).

Dependencies: the proved smooth Taylor-sum Ito theorem, C1 stochastic Fubini/time weighting, genuine conditional J identity, and Mathlib real calculus. This is a separable backward-heat class; no general C1,2 characterization or full functional Ito theorem is asserted. Verification: complete Lake build, all public declarations checked with their elaborated arguments, and full transitive axiom audit; only propext, Classical.choice, Quot.sound permitted.
Campaign VI verification completed: 4,161 Lake jobs; 2,630 audited declarations, zero nonstandard axioms. All 23 new public declaration types inspected.

## Brownian campaign VII — bounded smooth projection diagnostic (2026-10-12)

`Foundation/GaussianSmoothProjectionDiagnostic.lean` supplies a C_b^3 diagnostic that the prior cubic calculation did not provide:

- `sin_bounded_C3` (line 17): sine is C3 and every actual iterated derivative of order 0 through 3 has norm at most one.
- `sin_predictableAdjoint` (30): for every T>=0, J*[sin(B_T)] = exp(-T/2) times the independently constructed predictable field 1_(0,T] exp(t/2)cos(B_t). This follows from `GaussianSmoothHeatMartingale.heat_representation` and the genuine isometry identity J*J=id; no target projection formula is assumed.
- `sin_predictableAdjoint_slices` (49) identifies the exact product-L2 slices as 1_(0,T] exp(-(T-t)/2)cos(B_t).
- `sin_projection_ne_running_derivative` (69): for every T>0 this bounded predictable adjoint differs from the independently defined running field 1_(0,T]cos(B_t). Equality would imply equality of almost every time slice. The proved mean E cos(B_t)=exp(-t/2)>0 then forces t=T almost everywhere on (0,T), contradicting the positive measure of that interval.

This directly disproves the terminal-adjoint/running-spatial-derivative substitution in its bounded predictable-adjoint formulation even on a bounded smooth test function. It is not merely a failure caused by cubic growth. The theorem does not assert new full Malliavin-domain membership for sine by fiat; the existing equality J*=predictable projection of D retains its exact domain restriction. Nor is this a blanket counterexample to every possible precisely repaired abstract theorem. The manuscript's Step 2 cannot be justified by the bounded-adjoint Brownian representation theorem, and its correction needs the actual time-dependent/conditional representer rather than the running spatial derivative.

No additional integrability assumptions are hidden: values are constructed through Lipschitz L2 composition, weighted predictable fields use compact-time bounded coefficients, and all expectations are integrals of genuine L2 functions under the probability measure. Time zero is included in the formula and excluded exactly where non-equality requires a positive interval.
Campaign VII verification completed: 4,162 Lake jobs; 2,634 audited declarations, zero nonstandard axioms; all four new theorem types inspected explicitly. Original source/manuscript SHA256 hashes and dependency pins unchanged. The full campaign added 136 audited public declarations in eleven new Lean modules; prior verified theorem bodies were preserved.

## Finish Brownian foundation I: actual C2-to-C3 approximation (2026-10-12)

Starting HEAD ceefa5895a3e5d2d726f40aec4d641a2a2c98eeb. New `RealSteklovApprox.lean` defines average(f,e,x)=(integral_x^(x+e) f)/e (line 12). `average_hasDerivAt` (19) proves its actual derivative by FTC; `average_contDiff_succ` (31) improves C^n to C^(n+1). `deriv_average_eq_average_deriv`, `second_average`, `third_average` (39,50,55) prove actual derivative identities. For positive e and C2 f the third derivative is (f''(x+e)-f''(x))/e and has bound 2M/e if |f''|<=M (`average_third_bound`,70). No third derivative of f is required. `average_tendsto`, `average_deriv_tendsto`, `average_second_tendsto` (77,82,87) prove pointwise simultaneous convergence as e tends to zero from above. `average_error_le` (93) proves uniform error <=K e for K-Lipschitz f. `width` (113) is 1/(n+1), positive and tending to zero; `approximation_C3`, `approximation_first_bound`, `approximation_second_bound` (123,126,132) give one explicit sequence with preserved first/second derivative bounds.

`BochnerL2Approximation.tendsto_of_dominated` (line 11) proves strong L2 convergence with a separate genuine L2 majorant, by dominated convergence of squared differences. `GaussianBoundedApproximation` independently constructs the actual bounded continuous composition phi(B_t) (`bounded_memLp`,14; `boundedValue`,19; `boundedValue_coeFn`,22). `values_tendsto` (43) proves L2 convergence for pointwise convergent uniformly bounded Lipschitz approximants to a bounded continuous function, with varying Lipschitz constants. `value_uniform_error` (62) transfers uniform spatial approximation errors. `drift_tendsto` (72) proves both integrability of the limiting Gaussian-L2 curve and convergence of its actual Bochner interval integrals; continuity of the limit is not an assumption. `integrands_tendsto` (94) proves convergence in the ORIGINAL independently defined predictable domain of uniformly bounded pointwise-convergent Lipschitz running functions. No stochastic representation assumption or new domain definition is used.

This milestone proves the approximation prerequisites, not yet the limiting C2 Ito formula. All time intervals include zero. Full Lake build PASS (4165 jobs); 2666 transitive axiom checks, all only propext/Classical.choice/Quot.sound; all 32 new declaration types inspected. No original files, previous theorem bodies, pins or unrelated untracked documents changed.

## Finish Brownian foundation II: genuine bounded-derivative C2 Ito (2026-10-12)

`Foundation/GaussianC2Ito.lean` completes the limiting theorem. Exact hypotheses of `c2_ito` (line 107) and `c2_ito_ae` (125): f : real -> real, ContDiff real 2 f, K0 K1 nonnegative real, pointwise nnnorm(deriv f)<=K0 and nnnorm(deriv(deriv f))<=K1; arbitrary nonnegative T. No boundedness of f, no third derivative, no Lipschitz or uniform continuity of f'', and no assumed stochastic limit/representation. The conclusions are the actual Gaussian-L2 and AE identities

    f(B_T)-f(0) = J(1_(0,T] f'(B_t)) + (1/2) integral_0^T f''(B_t)dt.

`functionLip`/`derivativeLip` (19/22) derive the needed Lipschitz bounds. `curvatureValue` (30) is defined independently as the actual L2 class of the bounded continuous f''(B_t), identified by `curvatureValue_coeFn` (33). `smoothApprox` (37) is the actual average over [x,x+1/(n+1)], not a selected function assumed to satisfy Ito. `terminal_tendsto` (64), `stochastic_tendsto` (75), `curvature_tendsto` (86), and `curvature_integral_tendsto` (96) prove all three limits along this same sequence. The last theorem also proves genuine interval integrability of the Gaussian-L2 drift. The earlier C3 Ito theorem is applied only to these genuinely C3 approximants, with third-derivative bound allowed to grow with n. Taking limits does not require a uniform third-derivative bound. Time zero is included.

This establishes Objective 1A for C2 functions with bounded first two derivatives, including C2 compactly supported functions. Arbitrary polynomial growth/localization remains a separate obligation; it is not inferred from this result. Full Lake build PASS (4166 jobs), all 2683 transitive checks standard axioms only; all 17 new public types inspected. No existing theorem bodies, manuscripts, pins or twelve unrelated documents changed.

## Finish Brownian foundation III: corrected adjoint and mixed quadratic stopped cylinders (2026-10-12)

`GaussianC2OperatorCorrection.terminal_adjoint` (line 21) proves on the C2 bounded-first/second-derivative class: J*f(B_T)=1_(0,T]f'(B_t)+(1/2)J*V_T, V_T the independently specified actual Bochner integral of f''(B_t). `projection_difference` (31) and `terminal_adjoint_eq_running_iff` (40) characterize the missing term exactly: the substitution holds iff J*V_T=0. This criterion is a conclusion, never a hypothesis of Ito. `compensated_projection` (49) proves the actual conditional projection identity for f(B_T)-V_T/2. `full_derivative_projection` (64) transfers this formula to Pi D only with explicit terminal membership in the EXISTING full closed derivative domain; it neither asserts membership without proof nor equates J* and D. The bounded-sine diagnostic remains a counterexample to the manuscript substitution, not a defect of the integration-first framework.

`GaussianMixedStoppedIto.crossRunning` (49) is independently specified as 1_(0,s] B_min(t,s') + 1_(0,s'] B_min(t,s). `past_coordinate_step_slices`, `orderedCrossField_slices`, and `crossField_slices` (21,32,71) identify the actual previously constructed predictable cross fields with this running product-rule coefficient, for arbitrary time order. `stopped_product_ito` (84) proves B_min(T,r) B_min(T,s)=J(crossField)+min(T,r,s). `mixed_covariance_integral` (96) proves the integral of the product of the two actual active-coordinate indicators is precisely min(T,r,s). It does not assert a new general mixed quadratic-variation convergence theorem.

`quadratic` (115) independently defines Phi(x)=c+sum_i a_i x_i+sum_ij b_ij x_i x_j, with arbitrary finite index type and matrix b, without a symmetry assumption. `quadratic_hasDerivAt` (124) and `firstDirectional_hasDerivAt` (144) prove the actual directional derivative and mixed Hessian H(v,w)=sum_ij b_ij(v_i w_j+w_i v_j). `half_hessian_contraction` (158) proves H(d,d)/2=sum_ij b_ij d_i d_j. `quadraticCylinder_coeFn` (167) proves actual evaluation, and `stopped_quadratic_ito` (197) gives

    Phi(B_min(T,r_i))-c = J(quadraticCylinderIntegrand) + sum_ij b_ij min(T,r_i,r_j).

The finite-dimensional mixed coefficients, genuine derivative calculation, cross-field slice identification, and integrated covariance formula all agree. Empty families, repeated observations, zero times, singular covariance, and nonsymmetric coefficient presentations are included. This extends the additive smooth result to a truly nonlinear mixed QUADRATIC class; arbitrary smooth mixed cylinders remain unproved. Its stochastic identity reuses the actual proved quadratic representation, whose running integrand is now identified, not a newly assumed Ito formula.

`GaussianBoundedContinuity.boundedValue_continuous` (11) proves Gaussian-L2 continuity of phi(B_t) for every bounded continuous phi, without Lipschitz regularity. It uses the actual L2 continuity of Brownian coordinates, almost-everywhere subsequences, and genuine L2 domination. This supports the next C2 time-weighted extension.

Verification: complete Lake build PASS (4169 jobs), 2706 standard-only transitive axiom checks, all 23 new public types inspected. Source/manuscript files, previous theorem bodies, pins and twelve unrelated untracked documents preserved; no push.

## Finish Brownian foundation IV: finite-rank C1,2 time dependence (2026-10-12)

`Foundation/GaussianC2TimeWeighted.lean` uses exactly f : real -> real, ContDiff real 2 f, and uniform bounds K0,K1 on the first and second ACTUAL derivatives. Its time coefficient a is C1 on the real line. No bound on f itself, third derivative, Lipschitz second derivative, or global bound on a/a' is assumed. Compact time intervals provide the deterministic coefficient bounds. `curvature_continuous` (21) proves continuity of the Gaussian-L2 curve f''(B_t), using the independently proved bounded-continuous composition result. `primitive_hasDerivAt` (27), `primitive_continuous` (33), and `weighted_primitive_identity` (36) supply genuine Bochner FTC and deterministic integration by parts. `smooth_integrand_continuous` (57) uses the already proved scalar C2 identity and J isometry to prove horizon continuity; it is not an assumption used to prove that scalar identity. `weightedField_eq` (72) identifies the independently defined predictable field with the proved stochastic-Fubini expression. `time_weighted_ito` (87) and `time_weighted_ito_combined` (135) give the actual time-weighted C2 formula, with all drift integrability established.

`Foundation/GaussianFiniteRankTimeIto.lean` defines, for any finite index type (including the empty type),

    F(t,x) = sum_i a_i(t) f_i(x),

where every a_i is C1 and every f_i is C2 with globally bounded first and second derivatives. This finite-sum class contains genuinely nonseparable time-space functions; it is a restricted C1,2 theorem, NOT arbitrary C1,2. `function` (16), `time_hasDerivAt` (18), `space_hasDerivAt` (22), and `second_space_hasDerivAt` (26) define F independently and prove its actual partial derivatives. `value`, `field`, and `generatorValue` (37,40,43) construct actual Gaussian-L2 values, the existing predictable-domain field, and the Gaussian-L2 drift. `value_coeFn` (47), `field_slices` (58), and `generator_coeFn` (75) identify them with F(t,B_t), 1_(0,T] partial_x F(t,B_t), and partial_t F(t,B_t)+(1/2) partial_xx F(t,B_t). `generator_continuous` (98) proves compact-time Bochner integrability. `finite_rank_ito` (109) proves, for every T>=0,

    F(T,B_T)-F(0,B_0)
      = J(1_(0,T] partial_x F(t,B_t))
        + integral_0^T [partial_t F(t,B_t)+(1/2)partial_xx F(t,B_t)] dt.

This is an equality of actual Gaussian-L2 classes; the displayed time integral is Bochner in Gaussian L2. The proof sums the proved C2 time-weighted formula and justifies the interchange with the integral. It does not assume an Ito identity or finite-rank approximation theorem. `moving_sine_finite_rank` (128) exhibits the representation of sin(t+x) by two summands. Its regularity and derivative bounds are the ordinary sine/cosine bounds; the example theorem itself asserts the exact finite-rank representation, not a separately instantiated stochastic identity.

Verification: full Lake build PASS, 4,171 jobs. Transitive axiom audit PASS, 2,728 audited declarations, no axioms outside propext/Classical.choice/Quot.sound. All 22 new public declaration types were inspected explicitly. Across this campaign from ceefa5895a3e5d2d726f40aec4d641a2a2c98eeb, 94 public declarations were added in nine focused modules. Previous theorem bodies are unchanged; project imports and axiom checks were extended.

## Brownian readiness: exact scope and remaining obligations (2026-10-12)

The completed part is scalar C2 Ito with bounded first/second derivatives, actual simultaneous terminal/stochastic/drift approximation, finite-rank C1,2 time dependence, arbitrary mixed quadratic stopped cylinders, and the corrected bounded-adjoint identity. Neither compilation nor this restricted functional extension validates the original manuscript's general operator-functional theorem. In particular, the sine counterexample diagnoses the terminal-adjoint/running-derivative substitution in the manuscript, not the independently constructed integration-first calculus.

Remaining Brownian obligations, in priority order:

1. Arbitrary C1,2: prove approximation simultaneously controlling F, partial_t F, partial_x F, and partial_xx F in the terminal Gaussian L2, predictable product L2, and integrable Gaussian-L2 drift topologies; alternatively prove the corresponding time-freezing partition estimates. Finite-rank density in these simultaneous norms has NOT been proved or assumed. Merely dense scalar values would be insufficient.
2. Arbitrary smooth mixed stopped cylinders: a controlled multivariate Taylor remainder and convergence of adapted mixed quadratic-variation sums, with all gradient/Hessian integrability. The new quadratic theorem has an exact Hessian contraction and integrated active-coordinate covariance, but it is not a general mixed quadratic-variation limit theorem. Additive C3 and mixed quadratic classes do not exhaust smooth cylinders.
3. Polynomial-growth/localized C2 beyond the present bounded-derivative class: prove simultaneous derivative cutoff/localization error estimates with the needed Gaussian moments. Existing scalar polynomial Ito is a separate result, not a density theorem for arbitrary growth classes.
4. Full Malliavin-domain membership and a smooth-cylinder chain theorem remain separate from the new bounded J* formulas. `GaussianC2OperatorCorrection.full_derivative_projection` states the domain condition explicitly; `c2_ito` has no such extra condition. Horizontal/vertical path derivatives have not been identified with full D by relabeling.
5. Current stochastic equalities are Gaussian-L2 identities, and where supplied, AE identities for each fixed horizon. A common-null-set continuous pathwise version and identification with arbitrary pointwise time-integral representatives are not claimed automatically. The manuscript's abstract bracket/time-field typing and Volterra-domain issues remain.

### Readiness for the next research tracks

All paths below are relative to C:/OperatorDerivativeRewrite; Gaussian namespaces have prefix OperatorDerivativeRewrite.Foundation.

**Isonormal/fractional Brownian construction: ready for a separate construction milestone, not fractional Ito.** `Foundation/SeparableHilbertEmbedding.lean:60`, `exists_hilbertEmbedding`, constructs a linear isometry from any complete separable real Hilbert space into the coefficient l2. `Foundation/GaussianHilbertProcess.lean` supplies `isonormalEmbedding` (25), `isonormal_law` (53), `isonormal_memLp` (59), `isonormal_covariance` (78), and `isonormal_isGaussianProcess` (85): these are actual jointly Gaussian coordinates with covariance the Hilbert inner product. `Foundation/InfiniteGaussianCylinders.lean` supplies `isonormalCylinder_memLp` (49), `isonormalCylinderGradient_memLp` (61), `isonormalCylinderShift_hasFDerivAt` (127), and `isonormalCylinderShift_product_rule` (165). Later representation-independence and closed-domain results already apply to these Gaussian coordinates. A fractional model still needs an explicit separable Hilbert/Volterra kernel, proof of its covariance and square integrability, and increment/path regularity. Brownian min(s,t) covariance, predictable Itô isometry and Brownian PRP do not transfer to Hurst parameters other than 1/2. Choice and justification of Young, rough, or divergence integration and its correction terms are new obligations.

**Gaussian Ornstein-Uhlenbeck/energy geometry: substantial concrete infrastructure already verified.** `Foundation/GaussianMehler.lean` has `mehler_zero` (47), `integral_mehler` (158), and `mehler_compose` (181). `Foundation/GaussianFisherDecay.lean` has `hasDerivAt_mehler_C1` (51) and `fisherInformation_decay` (369). `Foundation/GaussianEntropyDissipationProof.lean:453`, `hasDerivAt_entropy_dissipation`, and `Foundation/GaussianLogSobolevFull.lean:231`, `gaussian_logSobolev_of_hasDerivAt`, give concrete one-dimensional Gaussian results with their proved regularity/integrability. These can support a carefully scoped tensor/chaos-generator identification project alongside the existing closed Gaussian derivative and adjoint. They do NOT establish abstract Bakry-Emery Gamma_2 curvature theory for arbitrary invariant diffusions: generator domains, Markov/invariance hypotheses, curvature calculus, and entropy approximation outside this Gaussian setting still need proofs.

**Fractional stochastic evolution/convolutions: reusable ingredients, not yet a convolution theory.** `Foundation/BochnerL2Approximation.lean:11`, `tendsto_of_dominated`, is a genuine Hilbert-valued L2 limit theorem. `Foundation/GaussianContinuousStochasticFubini.lean`, `integrated_slices` (100) and `integral_weighted_field` (147), proves the specific continuous compact-time kernel interchange used here. `Foundation/GaussianContinuousRigidity.lean`, `completedGraph_sensitivity` (46), `integral_mem_derivative_domain` (69), and `rigidity_graph` (76), retains explicit graph-domain restrictions. A stochastic convolution project still needs operator-valued kernel measurability, Hilbert-Schmidt/radonifying summability or corresponding covariance estimates, a genuine Hilbert-valued integration extension, control of singular time boundaries, and unbounded-generator domain interchanges. Scalar Brownian Fubini alone proves none of these.

Recommendation: this is a useful verified Brownian checkpoint, but do not label the general functional Brownian chapter complete. If completing Paper 1 remains primary, prioritize the arbitrary mixed-cylinder/time-dependent approximation obligations and a smooth full-D chain/domain theorem before claiming the manuscript's functional result. A separately scoped isonormal fBM construction or concrete Gaussian OU project is technically feasible now; it must not conceal the remaining Brownian functional gaps. No model-specific fBM, SPDE, or new abstract curvature formalization was started in this campaign.

### Complete new declaration inventory for this campaign

The following 94 public definitions and theorems all have explicit transitive axiom checks. Each name is relative to OperatorDerivativeRewrite.Foundation followed by the module namespace shown. The preceding sections explain which declarations are the substantive mathematical conclusions.

- **RealSteklovApprox**: `average`, `average_eq_primitive`, `average_hasDerivAt`, `average_deriv`, `average_contDiff_succ`, `deriv_average_eq_average_deriv`, `deriv_contDiff_one`, `second_average`, `third_average`, `average_norm_le`, `average_third_bound`, `average_tendsto`, `average_deriv_tendsto`, `average_second_tendsto`, `average_error_le`, `width`, `width_pos`, `width_tendsto`, `approximation_C3`, `approximation_first_bound`, `approximation_second_bound`.
- **BochnerL2Approximation**: `tendsto_of_dominated`.
- **GaussianBoundedApproximation**: `bounded_memLp`, `boundedValue`, `boundedValue_coeFn`, `gaussian_norm_le`, `boundedValue_norm_le`, `value_norm_le`, `values_tendsto`, `value_uniform_error`, `drift_tendsto`, `integrands_tendsto`.
- **GaussianC2Ito**: `functionLip`, `derivativeLip`, `second_continuous`, `curvatureValue`, `curvatureValue_coeFn`, `smoothApprox`, `smoothApprox_C3`, `approximateFunctionLip`, `approximateDerivativeLip`, `curvatureLipConstant`, `approximateCurvatureLip`, `terminal_tendsto`, `stochastic_tendsto`, `curvature_tendsto`, `curvature_integral_tendsto`, `c2_ito`, `c2_ito_ae`.
- **GaussianC2OperatorCorrection**: `drift`, `terminal_adjoint`, `projection_difference`, `terminal_adjoint_eq_running_iff`, `compensated_projection`, `full_derivative_projection`.
- **GaussianMixedStoppedIto**: `past_coordinate`, `past_coordinate_step_slices`, `orderedCrossField_slices`, `crossRunning`, `ordered_cross_running`, `crossField_slices`, `stopped_product_ito`, `mixed_covariance_integral`, `quadratic`, `firstDirectional`, `secondDirectional`, `quadratic_hasDerivAt`, `firstDirectional_hasDerivAt`, `half_hessian_contraction`, `quadraticCylinder_coeFn`, `stopped_quadratic_ito`.
- **GaussianBoundedContinuity**: `boundedValue_continuous`.
- **GaussianC2TimeWeighted**: `curvature_continuous`, `primitive`, `primitive_hasDerivAt`, `primitive_continuous`, `weighted_primitive_identity`, `smooth_integrand_continuous`, `weightedField_eq`, `time_weighted_ito`, `time_weighted_ito_combined`.
- **GaussianFiniteRankTimeIto**: `function`, `time_hasDerivAt`, `space_hasDerivAt`, `second_space_hasDerivAt`, `value`, `field`, `generatorValue`, `value_coeFn`, `field_slices`, `generator_coeFn`, `generator_continuous`, `finite_rank_ito`, `moving_sine_finite_rank`.

## Brownian endgame A1: arbitrary nonlinear stopped-coordinate coefficients (2026-10-12)

Starting HEAD aaace0f09965d2f3b13b9ed6f536c836b8e1c49f. `Foundation/GaussianStoppedComposition.lean` treats any finite index type and arbitrary deterministic nonnegative horizons r_i, with no independence, nondegeneracy, ordering, or distinctness assumption. `coordinates` (18) is the actual vector (B_min(t,r_i)); `vector` (21) is its independently constructed finite-product Gaussian-L2 class. `vector_coeFn` (24), `vector_continuous` (35), `coordinates_stronglyMeasurable` (41), `coordinates_past` (45), and `coordinates_memLp` (53) prove representation, strong L2 continuity, actual raw-past measurability, and square integrability. Empty coordinate families are included.

For an arbitrary globally Lipschitz multivariate Phi, `value` (66), `value_coeFn` (69), `value_memLp` (79), `value_continuous` (83), and `value_past` (87) supply genuine nonlinear composition. Phi need not be bounded or additive. The centering in the Nemytskii construction does not change Phi; the constant part is restored using the actual probability-space unit.

For arbitrary bounded CONTINUOUS multivariate Phi, `boundedValue` (93), `boundedValue_coeFn` (98), `boundedValue_continuous` (103), and `boundedValue_past` (129) prove these properties without a Lipschitz assumption. L2 continuity follows from convergence-in-measure subsequence extraction for the actual finite-vector L2 curve, pointwise continuity, and a separate constant L2 majorant. It does not assume sample-path continuity or convergence of totalized integrals.

`boundedField` (136) belongs to the already independently defined full predictable subspace. `boundedField_slices` (140) identifies its actual time slices. `bounded_stochastic_sum_tendsto` (146) proves convergence of adapted left-step J integrals to J of this field. `bounded_drift_sum_tendsto` (152) proves actual Gaussian-L2 Bochner convergence of left Riemann sums. These are analytic prerequisites for arbitrary nonlinear smooth cylinders, not an asserted Ito formula. Actual derivative/Hessian coefficient identification and the mixed Taylor/quadratic-variation assembly remain separate obligations. Existing scalar C2, finite-rank C1,2, and mixed quadratic theorems are preserved.
A1 verification: full Lake build PASS (4,172 jobs); transitive axiom audit PASS (2,749 declarations, all 21 new public declarations, zero nonstandard axioms). Public types checked with explicit arguments. No previous theorem body, dependency pin, original source/manuscript or protected untracked document changed.

## Brownian endgame A2/B prerequisite: actual smooth fields and covariance-Hessian calculus (2026-10-12)

`Foundation/FiniteCovarianceHessian.lean` defines `partialDerivative` (16), `hessian` (19), and `mixedPartial` (22) from Mathlib fderiv of the given Phi, not independently prescribed fields. `differential_expansion` (31) and `hessian_expansion` (36) prove the finite coordinate expansions. `line_hasDerivAt` (50) and `line_second_hasDerivAt` (57) identify the actual first and second scalar derivatives of s |-> Phi(x+s v). The second statement assumes exactly C2 regularity. `partial_hasFDerivAt` (142), `mixedPartial_eq_fderiv_partial` (148), and `mixedPartial_symmetric` (154) verify actual iterated partial derivatives and symmetry. `partial_contDiff_one`, `mixedPartial_continuous`, `partial_bound`, and `mixedPartial_bound` (71,75,80,86) supply the precise coefficient regularity and norm estimates.

`covariance` (96) is the independently defined matrix C_ij=sum_a k_ai k_aj, for an arbitrary finite family of noise directions. `covariance_symmetric` (99), `covariance_nonneg` (102), and `covariance_hessian_contraction` (126) prove symmetry, positive semidefiniteness, and sum_a D2Phi(x)[k_a,k_a]=sum_ij partial_ij Phi(x) C_ij. There is no invertibility assumption, so singular covariance and empty families are included. This algebraic covariance-Hessian engine does not assert existence of a new stochastic integral or Ito formula for arbitrary kernels.

`Foundation/GaussianStoppedSmoothFields.lean` applies the A1 construction to arbitrary Phi : (iota -> real) -> real, C2, with uniform bounds K0,K1 on the operator norms of its actual first and second Frechet derivatives. The index type is any finite type, and r_i are arbitrary nonnegative deterministic horizons. No additive, quadratic, finite-rank-in-space, or independent-coordinate assumption is imposed. `functionLip` (21) derives global Lipschitz continuity of Phi. `gradientValue` and `hessianValue` (24,28) are genuine Gaussian-L2 classes of the actual partial derivatives at the stopped vector; the coeFn, continuity, adaptation and interval-integrability results (32--52) prove all needed analytic properties.

`gradientField` (57) is an element of the pre-existing full predictable L2 domain, defined by summing the actual coordinate-derivative fields up to min(T,r_i). `gradientField_slices` (66) identifies its time slices; `gradientField_slices_strict` (104) proves they equal 1_(0,T](s) sum_i 1_(s<r_i) partial_i Phi(X_s) almost everywhere in time. Finitely many deterministic endpoints are explicitly removed using the atomless Lebesgue measure theorem, not silently ignored. `hessianDrift` (62) independently defines one half of the sum of genuine Bochner integrals of partial_ij Phi(X_s) up to min(T,r_i,r_j). Its integrability is already proved.

`gradient_steps_tendsto` (81) and `hessian_steps_tendsto` (89) prove convergence of the corresponding stochastic and drift sums along a single natural-number refinement parameter. Each coordinate/pair currently uses its own capped uniform partition. THIS IS NOT YET A COMMON-PARTITION TAYLOR IDENTITY. The outstanding assembly obligation is to coordinate the partitions (or prove equivalent refinement estimates), control the mixed weighted quadratic-variation error, and prove a multivariate Taylor remainder limit. No conclusion asserting Phi(X_T)-Phi(X_0)=J(gradientField)+hessianDrift has been added by assumption. The existing mixed quadratic theorem remains the strongest complete nonlinear stopped-cylinder Ito identity at this checkpoint.
A2/B verification: full Lake build PASS (4,176 jobs); transitive axiom audit PASS (2,785 declarations; all 36 new public declarations; only propext, Classical.choice and Quot.sound). Exact public theorem arguments inspected, including the distinct K0-only gradient and K1-only Hessian assumptions. Prior verified bodies and dependency pins preserved.

## Brownian endgame A3: genuine mixed weighted quadratic variation (2026-10-12)

`Foundation/GaussianStoppedQuadraticVariation.lean` introduces the geometric cell condition r<=s OR t<=r for a cell [s,t]. It excludes a stopping horizon strictly inside the cell, includes repeated/zero horizons and zero-length cells, and is not a stochastic convergence hypothesis. `stopped_increment` (20) proves the actual pointwise increment identity Delta B_stopped = active(t,r) Delta B. `stopped_time_increment`, `active_mul`, `min_aligned`, and `covariance_cell` (29,37,40,48) prove that the mixed covariance cell is exactly min(t,p,q)-min(s,p,q), including boundary cases.

For arbitrary bounded continuous multivariate Psi and arbitrary finite stopped-coordinate family r, `weight` (56) is Psi(X_s) times the two deterministic activity factors, expressed as an actual measurable function of the Brownian past. `weight_measurable`, `weight_bound`, `weight_memLp`, and `weight_energy` (60,65,73,81) prove its measurability, L2 integrability, and second-moment bound M^2. No independence or integrability is postulated for the product errors: the established whole-past weighted Hermite orthogonality theorem supplies it.

`rawMixedError` (97) is independently defined as the sum over partition cells of

    Psi(X_left) * [Delta B_stopped(p) * Delta B_stopped(q)
                   - (min(right,p,q)-min(left,p,q))].

`mixedError_coeFn` (103) identifies this actual sum with the constructed Gaussian-L2 error when the partition is monotone and aligned with p and q. `mixedError_mesh_bound` (126) proves squared norm <=2 M^2 mesh * (last-first). `rawMixedError_memLp` (143) proves genuine square integrability; `rawMixedError_integral_sq` (150) identifies its actual squared integral with that norm. `rawMixedError_sq_tendsto` (164) proves mean-square convergence to zero for any sequence of aligned monotone partitions whose nonnegative mesh bounds tend to zero and whose total lengths are uniformly bounded. Its hypotheses concern only partition geometry and the bounded continuous coefficient; they do not assume convergence of the errors or graph density. Each actual bounded continuous Hessian entry from A2 supplies such a coefficient without new assumptions.

Exact limitation: this proves mixed weighted quadratic-variation convergence on ALIGNED refining meshes, not arbitrary meshes. Construction of a common refining mesh containing every stopping horizon, and convergence of all first/second-derivative sums on that same mesh, remain assembly obligations. The earlier independently capped uniform-sum convergence theorems are not silently substituted for a common-partition argument. No general nonlinear Ito identity is asserted at this milestone.
A3 verification: full Lake build PASS (4,177 jobs); transitive axiom audit PASS (2,804 declarations; all 19 new public declarations; standard three foundational axioms only). Exact elaborated raw-error convergence hypotheses inspected. No earlier theorem body or dependency pin changed.

## Brownian endgame A4: multivariate Taylor and genuine Gaussian remainder convergence (2026-10-12)

`Foundation/FiniteTaylorRemainder.lean` defines the actual affine-line composition, derivative of the actual Hessian, and second-order remainder (16,18,22). For any finite coordinate type (including empty), `third_line` (29) identifies the third actual scalar derivative along x+t v with D(D2Phi)(x+t v)[v,v,v]. `third_line_bound` (43) and `remainder_bound` (50) assume Phi is C3 and the explicit trilinear bound

    forall z v w u, norm(D(D2Phi)(z)[v,w,u]) <= M norm(v) norm(w) norm(u), M>=0.

This is a bound on an actual derivative, not a hypothesis about a Taylor error or independently prescribed derivative data. It is expressed on vector arguments to avoid nested continuous-linear-map norm elaboration issues in the pinned environment. It yields norm(R(x,v)) <= (M/6) norm(v)^3. `line_contDiff`, `remainder_continuous`, and `taylor_identity` prove regularity and the finite actual mixed-partial expansion. The algebraic expansion alone is not presented as the substantive Taylor estimate.

`Foundation/GaussianStoppedTaylor.lean` treats cells s<=t aligned with EVERY stopping horizon: r_i<=s or t<=r_i. `vector_increment` (25) identifies the entire stopped-coordinate increment as Delta B times its deterministic active vector; `activeVector_norm_le` and `vector_increment_norm_le` (20,33) give a dimension-free bound in the finite-product sup norm. `rawRemainder` (44) is the actual multivariate Taylor error. `rawRemainder_measurable`, `rawRemainder_bound`, and `rawRemainder_memLp` (48,54,61) prove measurability, the pointwise cubic estimate, and genuine L2 integrability from the existing actual Gaussian cubic increment. No integrability or independence of errors is assumed.

`remainderL2_coeFn` (69) and `remainderSum_coeFn` (99) identify the constructed L2 elements with the actual individual and summed pointwise remainders. `remainderL2_norm_sq` (72) proves

    norm(R_cell)^2 <= 15 (M/6)^2 (t-s)^3.

`remainderL2_mesh_bound` (81) and `remainderSum_mesh_bound` (113) prove

    norm(sum R_cell) <= (M/6) sqrt(15) sqrt(mesh) (last-first).

The argument uses the triangle inequality and a telescoping sum of interval lengths, not false independence or cancellation of Taylor errors. `remainderSum_tendsto` (126) proves convergence to zero in actual Gaussian L2 along any monotone, aligned meshes with nonnegative mesh bounds tending to zero and uniformly bounded total lengths. Empty coordinates, repeated/zero horizons and zero-length cells are allowed. There are no hidden first-/second-derivative boundedness assumptions in this remainder theorem; those bounds enter the independently verified derivative-field constructions when assembling Ito.

Remaining A obligation at this checkpoint: construction of one common aligned mesh and stochastic/drift approximation on that same mesh, followed by the exact finite Taylor identity and limit assembly. The mixed quadratic-variation and multivariate remainder limits are now proved, but an arbitrary nonlinear stopped-cylinder Ito identity is NOT yet claimed. This milestone does not extend to unrestricted C2 multivariate Phi or general nonseparable C1,2 time dependence.
A4 verification: full Lake build PASS (4,179 jobs); all 2,829 transitive axiom checks PASS, including all 25 new public declarations; only propext, Classical.choice and Quot.sound. Explicit public types inspected. Earlier theorem bodies and dependency pins unchanged.

## Brownian endgame A5: simultaneous common-mesh stochastic and Hessian approximation (2026-10-12)

`Foundation/GaussianRefiningPartitions.lean` removes the uniform-grid restriction without assuming any stochastic approximation. `covers` (10) proves finite adjacent-interval coverage from the endpoints, including zero cells; monotonicity is not even needed for coverage. For a continuous Gaussian-L2 curve v and monotone partitions tau_N from 0 to T with cell lengths bounded by epsilon_N -> 0, `step_tendsto` (23), `step_bound` (52), and `partition_tendsto` (64) prove strong product-L2 convergence to the previously independently defined running field. The proof uses genuine finite-interval domination and Gaussian-L2 continuity. No sample-path regularity is assumed. `drift_sum_tendsto` (124) gives Bochner-L2 drift convergence on exactly the same meshes.

For v measurable with respect to the actual raw Brownian past at every time, `predictableStep` (150) belongs to the existing independently defined full predictable space. `predictableStep_tendsto` (156) and `integral_step_tendsto` (167) prove convergence there and under the original integral J. `integral_step_coeFn` (179) identifies every step integral with its actual weighted Brownian increment sum. `cap_mesh_bound` (193) and `cap_monotone` (204) prove that capping a monotone mesh at r preserves monotonicity and does not increase its mesh. `capped_drift_sum_tendsto` (207) and `capped_integral_step_tendsto` (221) establish the corresponding limits up to min(T,r), including r=0 and repeated capped times.

`Foundation/GaussianStoppedMeshFields.lean` applies these results simultaneously to an arbitrary finite-dimensional C2 Phi with uniformly bounded actual first and second Frechet derivatives, and arbitrary deterministic stopping horizons. `gradientSum` (18) and `hessianSum` (22) use caps of ONE common underlying partition, with the same N and the same cell index set for all coordinates and pairs. `gradientSum_tendsto` (27) proves convergence to J(gradientField); `hessianSum_tendsto` (40) proves convergence to the independently defined half-Hessian Bochner drift. These results supersede the assembly limitation of separately capped UNIFORM grids in A2. Bounds on third derivatives are unnecessary for these approximation results.

Precise remaining A obligations: construct a common sequence containing all clipped stopping horizons and with mesh -> 0; identify these capped sums with the first and deterministic second-order terms of the actual finite Taylor sum; aggregate the already proved pairwise mixed-error and remainder limits; then pass to the actual endpoint identity. The present declarations do NOT assume or conclude that final Ito identity. General nonseparable C1,2 approximation, general deterministic-kernel Ito, independent second-order closure, and an unrestricted operator-functional formula remain unproved.
A5 verification: full Lake build PASS (4,181 jobs); all 2,846 transitive axiom checks PASS, including all 17 new public declarations. Only propext, Classical.choice and Quot.sound. Exact theorem types inspected. The campaign adds 118 audited public declarations across eight new modules; prior theorem bodies, original hashes, pinned dependencies and the twelve unrelated untracked documents are preserved. See BROWNIAN_ENDGAME_REPORT.md for the full declaration inventory, A--G statuses and nonclassical readiness assessment.

## Volterra / stochastic-volatility campaign A1 (2026-10-12)

Starting checkpoint: 61548d19f1f0020b35942783b8056b8b4b826fe4; preceding Brownian campaign finished its build/audit/report. The 12 unrelated untracked documents are preserved.

Foundation/GaussianVolatilityProcess.lean constructs value U T = J(cut T U) for every U in the independently defined full predictable product-L2 subspace. process is an actually adapted conditional-expectation representative; process_ae proves equality with this actual integral at every fixed time. process_martingale proves Mathlib Martingale on the raw natural Brownian filtration. process_memLp proves square integrability, process_centered proves zero mean, value_projection/process_condExp prove the exact cutoff conditional identity. process_pair_integrable and process_product_integral give genuine pairing integrability and E[M_U(S) M_V(T)] = integral_(0,min(S,T)] U V dt dP; process_isometry specializes this to the actual second moment. No conditional second-moment isometry or pathwise quadratic variation is claimed.

bounded_memLp, boundedField and boundedField_coeFn construct a finite-horizon field from an actual predictably measurable real coefficient and a uniform norm bound on that horizon. boundedField_lower transports an explicitly supplied pointwise lower bound; positivity is not inferred. No Malliavin conclusion is assumed in this construction. Differentiability of a particular bounded nonconstant example remains a separate obligation, while the pre-existing GaussianPredictableChaosCore.independent_sensitivity_graph already proves the integral's derivative under an independently specified product-derivative graph condition.

Verification: full Lake build PASS (4182 jobs); transitive audit PASS (2866 printed declarations, including all 20 new public declarations), only propext, Classical.choice and Quot.sound. No earlier theorem body or statement changed. The actual adapted representatives are per-time AE versions; common-null-set path continuity is not asserted.
## Volterra campaign E1: actual singular power kernel (2026-10-12)

Foundation/GaussianPowerVolterra.lean defines kernel beta t s = 1_(0,t](s) (t-s)^beta. For beta > -1/2, kernel_sq_integrable and kernel_memLp prove genuine Lebesgue integrability and L2 membership, using reflection of the time interval and the integrable power exponent 2 beta > -1. kernel_energy and vector_norm_sq prove exactly t^(2 beta+1)/(2 beta+1), including t=0; the endpoint value at s=t follows Real.rpow's convention and is immaterial to the L2 class.

The independently constructed L2 vector has proved causal support. value is the existing actual predictable Ito integral. value_law proves its centered Gaussian law with that variance; value_isGaussianProcess proves Gaussian finite-dimensional laws; kernel_pair_integrable justifies the covariance integral; value_covariance gives the actual two-kernel overlap integral. value_derivative proves membership of (value, embedded deterministic profile) in the pre-existing full closed Gaussian derivative graph. vector_zero/value_zero handle time zero. vector_exponent_zero/value_exponent_zero recover the pre-existing Brownian time vector and Gaussian-L2 variable exactly, not merely in law.

normalizedVector H hH t = sqrt(2H) times the vector at beta=H-1/2 has norm squared t^(2H) for every H>0. This covers H<1/2 and H>1/2 at the level of genuine singular/nonsingular L2 kernels. It is a Riemann--Liouville-type covariance; equal marginal variance DOES NOT prove the standard fBM two-time covariance or stationary increments. No standard fBM realization, filtration transfer, path continuity or fractional Ito/Gubinelli theorem is asserted.

Verification: full Lake build PASS (4183 jobs); complete transitive axiom audit PASS (2890 printed declarations, all 24 new public declarations), exactly propext, Classical.choice and Quot.sound. Earlier theorem bodies, original sources and dependency pins remain unchanged.
## Volatility campaign D1: genuine future-integral cancellation (2026-10-12)

Foundation/GaussianFutureRigidity.lean proves future_integral_past_zero and future_integral_eq_past_iff: for an actual full predictable u with cut S u=0, its Ito integral can be past-S measurable only if u=0. Proof uses the previously proved conditional integral/cutoff identity and injectivity of the actual Ito isometry, not assumed independence or a variance formula for an unspecified integral.

deterministic_factor_zero says that if J(u)=c sigma for a nonzero past-S Gaussian-L2 coefficient sigma, then c=0 and u=0. Positivity is unnecessary for this cancellation step. parameter_deterministic_representer lifts the result to a genuine Bochner-L2 family u(s) of predictable integrands: if each is supported after tau(s), sigma(s) is nonzero and past measurable, and J(u(s))=(kappa(s)-1) sigma(s) AE, then u=0 and kappa=1 AE. The hypotheses describe deterministic representer equality and independently verified time support/measurability; the zero conclusion is proved by conditioning and isometry. This does not assume or conclude that an arbitrary volatility has such a jointly square-integrable sensitivity representation. Connecting this to the actual derivative kernel and to determinism on the correct source sigma-algebra remains separate.

Verification: complete Lake build PASS (4184 jobs); all 2894 transitive axiom checks PASS, including all four new theorems, with only propext, Classical.choice and Quot.sound. Original sources and existing proofs unchanged.
### Volterra campaign E2: bounded deterministic kernel transfer (2026-10-12)

`Foundation/GaussianKernelTransfer.lean` defines `realization K = W ∘ K` for an actual bounded linear map `K : E →L[ℝ] TimeHilbert`. For a real Hilbert space E, with completeness only where its adjoint is needed, `realization_inner`, `realization_norm`, `realization_zero_iff`, `realization_product_integrable`, and `realization_centered` prove the source-isometry identities, genuine product integrability, and centering. No injectivity or surjectivity is assumed.

`covarianceOperator K = K.adjoint.comp K`; `realization_covariance` and `realization_normal` identify the actual covariance and `(W ∘ K)* (W ∘ K) = K* K`. `covariance_energy` and `covariance_zero_iff` preserve the precise nullspace. `realization_derivative` gives graph membership in the already constructed unbounded closed cylindrical derivative, with value `fieldEmbedding (productTensor (K x) gaussianOne)`.

This is deterministic Hilbert transfer. It does not identify K with a covariance square root, establish a specific fractional Brownian kernel, or turn a bounded adjoint into the full Malliavin derivative. Those distinctions are necessary for the manuscript's Theorem F.

Verification: complete Lake build passed (4185 jobs); all 2906 audit declarations passed with only `propext`, `Classical.choice`, `Quot.sound`. Explicit elaborated types are in `.lake/campaign-volterra/04-types.log`; build/audit logs use the same prefix. All twelve new public declarations are audited.

### Volterra campaign B/D: positive random polynomial volatility (2026-10-12)

`Foundation/GaussianPositiveVolatility.lean` constructs the actual predictable field sigma = 1 on (0,a], 1+B_a² on (a,b], zero outside (0,b], for 0≤a≤b. It is unbounded; no bounded-volatility theorem is substituted. `volatilityField_sobolev` proves membership in the independently defined predictable Sobolev domain, and `volatilityField_lower` proves sigma≥1 AE on (0,b]. `volatility_integral` identifies the actual Ito integral as B_a+(1+B_a²)(B_b−B_a).

`coefficient_derivative` is the actual polynomial derivative 2B_a times the source time direction. `volatility_derivative_graph` proves the existing closed cylindrical derivative of the actual integral equals `fieldEmbedding sigma` plus `incrementSensitivity`. `sensitivity_coeFn` identifies that extra term with 2B_a(B_b−B_a) times the time direction 1_(0,a]. `sensitivity_norm_sq` proves its exact squared norm 4a²(b−a). Thus for 0<a<b, `sensitivity_ne_zero`, `volatility_not_original_derivative`, and `volatilityField_not_deterministic` prove nonvanishing correction, failure of D J sigma = sigma, and genuine nondeterminism of the time-probability L² class.

The coefficient and increment products are actual finite-moment Gaussian polynomial random variables. Domain membership and values follow from the pre-existing polynomial differentiation and independent Sobolev results; no sensitivity value is postulated. This tests the full derivative, not the bounded predictable adjoint J*. A bounded nonconstant Sobolev coefficient and a general intrinsic volatility-observable calculus remain separate obligations.

Verification: all 24 new public declarations compiled and their explicit types were checked; full Lake build passed (4186 jobs), and 2930 transitive axiom checks used only `propext`, `Classical.choice`, `Quot.sound`. Logs: `.lake/campaign-volterra/05-*`.

### Volterra campaign B/C/D: actual weighted random representer (2026-10-12)

`Foundation/GaussianVolatilityRepresenter.lean` uses the preceding actual volatility, not an assumed gradient formula. Its `gradientField_graph` proves that the actual closed derivative of J sigma is the time-field embedding of `gradientField`. On the horizon (0,b], `coefficient` is measurable and at least one everywhere, and `coefficient_eq_field` identifies it with the actual volatility L² class.

`quotient_memLp` proves genuine L² membership of `gradientField / coefficient` in the actual measure coefficient² dt dP. `representer` is this quotient class, and `representer_formula` proves, for the finite-horizon class,

    kappa(r,omega) = 1 + 1_(0,a](r) 2 B_a(omega) (B_b(omega)-B_a(omega)).

The derivative graph identity requires a≤b. The nondegenerate randomness conclusions require 0<a<b. `correction_not_constant` rules out every AE scalar constant for 2B_a(B_b−B_a), using its actual predictable integral's zero mean and the independently proved nonzero sensitivity norm. `representer_not_deterministic` then rules out every deterministic time function k(r), even without requiring its measurability as a separate hypothesis: weighted/base measure equivalence, AE Fubini, and the positive measure of (0,a] reduce it to `correction_not_constant`.

`representer_sq_integrable` and `gradientField_sq_integrable` prove finiteness before the energy identity is used. `coefficient_mul_representer` recovers the already constructed source gradient. `representer_energy` identifies weighted representer energy with finite-horizon source gradient energy. No reciprocal moments, prescribed derivative data, or intrinsic-observable derivative are assumed. This is a concrete positive unbounded polynomial example, not a claim about every bounded or every predictable volatility.

All 21 public declarations, including the horizon-measure abbreviation, have explicit type checks and axiom audit entries. Full Lake build: 4187 jobs. Full transitive audit: 2951 declarations, only `propext`, `Classical.choice`, `Quot.sound`. Logs: `.lake/campaign-volterra/06-*`. Original manuscript and source SHA256 hashes remain unchanged. No dependency pin changed.

## Fractional Gaussian campaign A1: concrete spectral kernel (2026-10-12)

Initial verified HEAD d09656ee119054c9300a9d74b6ac9533653e800a, with the preceding Volterra campaign fully committed and reported. The original Gubinelli/factorization proofs and previous final report were inspected. The chosen covariance route is real harmonizable spectral geometry, not an assumed positive-definite kernel or a causal Volterra realization.

`Foundation/FractionalSpectralKernel.lean` defines `wave u = (cos u - 1, sin u)` in the actual Euclidean plane and `kernel H t x = 1_(0,infinity)(x) x^(-H-1/2) wave(t*x)`. For exactly 0<H<1 and any real t, `kernel_memLp` proves genuine Lebesgue L² membership. The local and tail bounds `raw_small_bound` and `raw_large_bound` dominate the squared norm by 2t² x^(1-2H) and 4x^(-2H-1), respectively. `raw_sq_integrableOn` and `kernel_sq_integrable` justify integration across zero and infinity. The estimates apply uniformly to both H<1/2 and H>1/2, without a separate Cauchy-principal-value convention.

`SpectralSpace` is actual L²(R;R²), complete by Mathlib; `spectralSpace_secondCountable` proves the separability prerequisite for the existing isonormal construction. `vector` is the actual L² class, `vector_zero` handles t=0, `vector_one_ne_zero` proves nondegeneracy using positivity of sine on (0,pi), and `vector_norm_sq_integral` identifies the actual norm integral. Fractional covariance and normalized process realization are not yet asserted at this milestone.

Verification: complete Lake build passed (4188 jobs); 2974 transitive axiom checks passed, including all 23 new public declarations, with only propext, Classical.choice and Quot.sound. Exact public types checked. Logs `.lake/campaign-fractional/01-*`. Existing declarations, original manuscript, pinned dependencies, and unrelated untracked documents preserved.

## Fractional Gaussian campaign A2: exact covariance, not just marginal variance

`Foundation/FractionalSpectralGeometry.lean` proves the actual spectral increment identity `kernel_sub_norm_sq`, scaling `kernel_scale_norm_sq`, and the resulting L² identities. `normalized` divides the actual vector by the independently proved nonzero norm at time one. `normalized_norm_sq` gives |t|^(2H); `normalized_sub_norm_sq` gives |t-s|^(2H); `normalized_inner` therefore gives exactly (|s|^(2H)+|t|^(2H)-|t-s|^(2H))/2, for every real s,t and exactly 0<H<1.

`covariance_positive` proves positive semidefiniteness for arbitrary finite real coefficient/time families, directly from the squared norm of their Hilbert-vector sum. `normalized_sub_norm` proves the exact H-Hölder distance |t-s|^H in the deterministic Hilbert space, and `normalized_continuous` proves its continuity. The proof uses genuine kernel integrability from A1 before the dilation change of variables. No covariance, positivity, completion, or scaling assumption is introduced.

This is real spectral geometry. It is not a causal Volterra kernel or pathwise sample regularity. The result applies without exclusions at H=1/2. The subsequent process realization and Cameron–Martin interpretation remain distinct constructions.

Verification: full Lake build 4189 jobs, 2992 transitive axiom checks (all 18 new public declarations), only propext, Classical.choice, Quot.sound. Exact public types checked. Logs `.lake/campaign-fractional/02-*`.

## Fractional Gaussian campaign A3: completed integrands and actual Gaussian realization

`Foundation/FractionalGaussianProcess.lean` constructs `integrandSpace` as the closed Hilbert span of the independently normalized spectral vectors, proves completeness, and defines `kernelVector`. `kernelVector_inner` is exactly the fractional Brownian covariance for nonnegative times and 0<H<1. `cameronMartinFunction_injective` proves that these vectors define an injective function realization; `cameronMartin_increment_bound` proves the H-Hölder estimate with the actual Hilbert norm.

`process_isGaussianProcess`, `process_covariance`, `process_centered`, and `process_law` construct a genuine jointly Gaussian process on the existing countable Gaussian product, with marginal variance t^(2H). `process_memLp`, `increment_sq_integrable`, and `increment_secondMoment` establish genuine moment integrability and the exact increment variance |t-s|^(2H). `value_zero` handles time zero; `value_increment_norm` gives the exact L² distance. `value_derivative_graph` identifies every coordinate's actual closed Gaussian derivative with its constant first-chaos direction.

This is a spectral Gaussian realization, not yet a continuous sample-path modification or a causal Brownian Volterra representation. Its complete deterministic Hilbert space is explicit. A full intrinsic integrand-valued divergence/derivative identification and an intrinsic fractional Clark–Ocone formula are not claimed.

Verification: full Lake build passed, 4190 jobs. The transitive audit passed for 3014 declarations, including all 22 new public declarations, with only propext, Classical.choice, Quot.sound. Explicit public types checked in `.lake/campaign-fractional/03-types.log`. Existing source bodies, pins, and unrelated untracked documents preserved.

## Fractional Gaussian campaign A4: actual prediction obstruction

`Foundation/FractionalPredictionObstruction.lean` defines `forecast t` as the actual orthogonal conditional projection of the constructed terminal coordinate X_1 onto the sigma-algebra generated by {X_r : r<=t}. `forecast_condExp` identifies it with Mathlib conditional expectation, without any independence assumption about fractional increments. `forecast_pairing` derives its pairing with X_t by projection orthogonality. For 0<t<=1, `forecast_norm_sq_lower` proves ||forecast t||² >= t^(2H)/4.

`zero_past_polynomial_constant` and polynomial density prove `forecast_zero`; this does not assume the raw generated sigma-algebra is pointwise trivial for chosen L² representatives. `no_higher_prediction_increment_bound` proves that for every alpha>2H, every real C, and every delta>0, some 0<t<delta with t<=1 satisfies C*t^alpha < ||forecast t-forecast 0||². `pastDirections_zero` proves the initial observation directions vanish.

This directly obstructs the original manuscript's claimed higher-order forecast remainder at s=0 when its leading representer lies in the initial past Hilbert space, hence is zero. Its claimed exponent min(4H,2H+1) exceeds 2H for all 0<H<1. The terminal variable is a genuine first-chaos coordinate with the actual closed derivative already proved in A3. The new theorem concerns mean-square increments, not a pathwise rough-path claim. A separate Taylor estimate for f(X_t) is a different, potentially valid statement and cannot silently replace the conditional-forecast claim.

Verification: all 12 public declarations compiled; exact types checked; full Lake build passed (4191 jobs), transitive audit 3026 declarations with only propext, Classical.choice, Quot.sound. Logs `.lake/campaign-fractional/04-*`. Manuscripts remain unchanged.

## Fractional Gaussian campaign A5: valid Taylor control for actual smooth observables

`Foundation/FractionalControlledEstimate.lean` proves a distinct valid statement, without claiming to repair the conditional forecast theorem by relabeling it. For 0<H<1, f continuously twice differentiable on R and every x satisfying ||deriv(deriv f)(x)||<=M, `remainder_bound` applies actual one-dimensional Taylor theory to R(x,y)=f(y)-f(x)-deriv f(x)*(y-x). `remainder_memLp` proves genuine Gaussian L² membership of R(X_s,X_t). `remainderL2_norm_sq` proves

    ||R(X_s,X_t)||_L²² <= (3 M²/4) |t-s|^(4H)

for all nonnegative s,t, including equal times. No boundedness of f or f' and no independence of increments is assumed. `square_norm_sq` derives the fourth moment from the previously proved actual second-chaos pairing, so the estimate is not based on an assumed fractional Gaussian moment identity. `increment_coeFn` and `remainderL2_coeFn` identify actual representatives.

This is a mean-square controlled estimate for a smooth composition f(X), not a conditional-prediction identity, a pathwise Gubinelli derivative theorem, or a rough integral construction. Continuous sample modifications and pathwise Hölder estimates remain separate.

Verification: all 13 public declarations and explicit hypotheses checked. Full build passed (4192 jobs), transitive audit 3039 declarations, only propext, Classical.choice, Quot.sound. Logs `.lake/campaign-fractional/05-*`.

## Fractional Gaussian campaign A6: full observable derivative and actual adjoint

`Foundation/FractionalGaussianOperators.lean` defines `scalarSpace` as the actual L² subspace measurable with respect to the constructed entire fractional Gaussian family. `derivative` is the restriction of the previously verified closed source derivative to the full inverse-image domain in this space. `derivative_domain` and `derivative_graph` give exact domain and value equivalences, not supplied derivative data. `derivative_isClosed`, `derivative_dense_domain` and `polynomial_graph_core` prove closedness, ambient density, and simultaneous polynomial approximation in the actual graph; no graph density is assumed.

`divergence` is the actual Mathlib adjoint. `divergence_domain` characterizes its entire domain by the weak pairing representer in fractional-observable L². Every field in the full source divergence domain belongs to this adjoint domain (`source_divergence_mem`); `divergence_source_value` is exactly conditional projection of its source divergence. `divergence_dense_domain` and `divergence_isClosed` follow with proved hypotheses. `divergence_adjoint_eq_derivative` proves equality of partial operators, including domains and values, using the independently verified closed-operator bidual theorem.

Important scope: the vector-field codomain remains ambient Gaussian L²(ell²). No assertion is made that this redundant source-field domain is already the intrinsic L² of the fractional Cameron–Martin space. No equality of its divergence domain with the source divergence domain, predictable projection, causal Volterra transfer or intrinsic Clark–Ocone formula is asserted. The full observable derivative is unbounded and is not replaced by a bounded deterministic first-chaos adjoint.

Verification: full Lake build passed (4193 jobs); explicit types checked in `.lake/campaign-fractional/06-types.log`. Full transitive audit completed with only propext, Classical.choice, Quot.sound; exact count is recorded in the final campaign report. All 58 archived source hashes and the newly added IBM PDF hash were checked unchanged, as were dependency pins. No existing proof body changed.

## Gaussian curvature campaign C1: actual OU polynomial recursion

Started only after the fractional campaign's final verified report commit 4c11a891ce31fe7661be577d3bfe71a4ac8dba26. No file named `iterated_gamma_curvature_tower.tex` was found recursively under C:/Operator. The available `fbm/hurst_curvature.tex` contains the Hadamard tower, innovation factorization and number-operator claims; its relevant proofs and the fBM Bakry–Émery manuscript definitions were inspected. These sources discuss the Fourier fractional Laplacian as well as covariance matrices; they must not be identified with Gaussian OU operators merely because kernels coincide.

`Foundation/GaussianOUCore.lean` defines the actual polynomial OU generator Lp=p''-x p'. Gamma and Gamma2 are defined by their generator recursions. `generator_actual_derivatives` identifies L with actual Mathlib derivatives. `gamma_formula` proves Gamma(p,q)=p'q'; `gammaTwo_formula` proves Gamma2(p,q)=p'q'+p''q''. `gaussian_curvature_one` consequently proves pointwise Gamma2(p,p)>=Gamma(p,p), not an assumed curvature field.

`generator_integrable`, `gamma_integrable`, and `gammaTwo_integrable` establish actual Gaussian integrability. `gaussian_generator_pairing`, `gaussian_generator_symmetric`, and `gaussian_generator_energy` reuse proved polynomial Gaussian IBP to establish symmetry and energy. This is a legitimate common polynomial core, not a theorem about the full closed OU generator, all Sobolev functions, higher iterates, or fractional-time evolution. Those operator-domain extension obligations remain explicit.

Verification: all 15 public declarations and explicit types checked. Full build passed (4194 jobs); transitive audit 3072 declarations, only propext, Classical.choice, Quot.sound. Logs `.lake/campaign-curvature/01-*`.

## Gaussian curvature campaign C2: covariance positivity and actual matrix eigenpairs

`Foundation/FractionalCovarianceMatrices.lean` proves finite fractional covariance matrices positive semidefinite for 0<H<1 from the independently constructed spectral Hilbert vectors, and proves positivity of every natural Hadamard power by Mathlib's Schur product theorem. This includes power zero and empty finite index sets. `brownian_covariance` identifies H=1/2 with min(s,t) for nonnegative times. `hurst_two_negative_energy` proves the H=2 two-point quadratic form on coefficients (2,-1) equals -12, excluding its interpretation as a probability covariance.

`Foundation/BrownianCovariancePowers.lean` proves the exact factorization A_k=L diag(D_k) L^T at times 1,...,n, k>0, where D_k(j)=(j+1)^k-j^k. `differenceVector_ne_zero`, `covariance_difference_action` and `generalized_eigenpair` establish actual nonzero generalized eigenvectors e_j-e_(j-1) (with the initial endpoint handled separately) and eigenvalues D_k(j)/D_l(j), for k,l>0. `adjacent_ratio_two` and `adjacent_ratio_ne_innovation` check the concrete ratio 7/3, which differs from 7. Completeness of this eigenbasis and a full spectral theorem are not asserted by this module.

Source qualification: the available `C:/Operator/fbm/hurst_curvature.tex` compares its j-th Hadamard form to the FIRST form; since D_1=1, raw D_j are appropriate for that stated comparison. The ratio correction concerns an adjacent-level comparison, not an error in that first-level comparison. Equality of covariance/Gram matrices does not establish equality of fractional Laplacians, Gaussian OU generators, or their domains.

Verification: all 24 new public declarations compiled and explicit types checked. Full build passed (4196 jobs); full transitive audit 3096 declarations with only propext, Classical.choice, Quot.sound. Logs `.lake/campaign-curvature/02-*`. No prior theorem body or archive changed.

## Gaussian curvature campaign C3: actual Wick realization of the Hadamard tower

`Foundation/FractionalWickCovariance.lean` uses actual polynomial cylindrical random variables in the constructed fractional Gaussian family. For arbitrary 0<H<1, nonnegative s,t and natural n,m, `cylinder_inner` proves the pairing equals n! R_H(s,t)^n if n=m and zero otherwise. `cylinder_centered` proves positive orders centered. `cylinder_derivative_graph` proves actual closed derivative graph membership with the genuine Wick lowering formula; no derivative data are supplied independently. `finite_sum_norm_sq` proves the exact factorial-scaled quadratic form for finite linear combinations.

This verifies the source manuscript's Wick Gram interpretation, including correlated times and degenerate directions. It does not identify a fractional Laplacian or a covariance-relative curvature matrix with the Gaussian OU number operator. The degree and spatial-innovation indices are different.

Verification: 6 new declarations, exact types checked, full Lake build 4197 jobs, full transitive audit 3102 declarations and only propext, Classical.choice, Quot.sound. Logs `.lake/campaign-curvature/03-*`.

## Fractional stochastic evolution E1: exact one-mode forcing threshold

The recursive C:/Operator/spde inventory contains two TeX manuscripts and no executable numerical sources, data, PDFs or Lean files. Both manuscripts' relevant definitions, proofs, limitations and retention experiments were inspected; see C:/Operator/ResearchAudits/SPDE_SOURCE_AUDIT.md and its hash manifest. Full manuscript claims remain UNVERIFIED.

`Foundation/FractionalForcingKernel.lean` extends the actual power-Volterra construction with necessity, not just sufficiency: `power_kernel_memLp_iff` proves for t>0 that 1_(0,t](s)(t-s)^beta is in Lebesgue L² iff beta>-1/2. `response_memLp_iff` proves for alpha>0 and t>0 that the normalized zero-generator forcing kernel (t-s)^(alpha-1)/Gamma(alpha) is in L² iff alpha>1/2. The proof uses the actual improper-integral criterion and reflection, with Gamma positivity, not a totalized integral.

`responseVector`, its a.e. representative theorem, and `stochasticResponse` give a genuine normalized deterministic time vector and isonormal Gaussian variable. `responseVector_norm_sq` and `stochasticResponse_norm_sq` prove the exact energy t^(2alpha-1)/(Gamma(alpha)^2*(2alpha-1)), including t=0. `stochasticResponse_derivative` proves actual closed Gaussian derivative graph membership. `stochasticResponse_zero` and `stochasticResponse_order_one` handle zero time and recover the existing Brownian coordinate at alpha=1.

This is a zero-generator one-mode forcing realization, not yet a Caputo solution theorem, a nonzero-rate Mittag-Leffler response, a continuous-path modification or an infinite-dimensional SPDE. It exposes the scalar temporal obstruction that spatial regularity alone cannot remove. The source's whole-space cylindrical-noise Hilbert-Schmidt computation is independently invalid; nonzero Fourier multipliers on L²(R) are not HS just because their symbols are in L². Its blanket temporal Holder exponent, arbitrary-Q scaling, and alpha=2 decay bounds also require repair. These source defects are documented without changing the manuscripts.

Verification: all 11 public declarations and explicit types checked. Full build 4198 jobs; full transitive audit 3113 declarations, only propext, Classical.choice, Quot.sound. Logs `.lake/campaign-evolution/01-*`.

## Recovered stochastic kernel convolution — 2026-10-13

Actual bounded predictable transforms, finite-rank Gram energy, adjoint/domain/nullspace and exact perturbation/convergence transfer independently verified. Full Lake build: 4199 jobs. Complete transitive audit: 3130 declarations; only propext, Classical.choice, Quot.sound. Exact statements, assumptions, source inventory and remaining obligations: RESEARCH_RECOVERY_REPORT.md. No Hilbert-valued SPDE solution is asserted.


## Fractional forcing quantified regularity obstruction — 2026-10-13

FractionalForcingObstruction.no_higher_initial_power_bound and no_initial_brownian_variance_bound prove failure of every excessive initial mean-square power bound in the actual zero-mode response. Full build 4200 jobs; full axiom audit 3132, exactly propext/Classical.choice/Quot.sound. See RESEARCH_RECOVERY_REPORT.md for quantifiers and limitations.


## IBM actual independent source coordinate laws — 2026-10-13

IBMSourceLaws constructs independent product Gaussian source factors, actual two-sided scenery with exact covariance/mean/marginal laws, Brownian finite laws on both halves, whole-half independence, and independent Brownian clock finite laws. No path modification or random-time composition is claimed. Full build 4201 jobs, transitive axiom audit 3153, only propext/Classical.choice/Quot.sound. All 21 public types checked. Complete source locations and scope: RESEARCH_RECOVERY_REPORT.md; analytic next backlog: RESEARCH_READINESS_AND_BACKLOG.md.


## IBM conditional path composition and modification bridge — 2026-10-13

Continuous IBM composition, joint measurability and independent path-valued source maps are verified under explicitly supplied measurable continuous paths. The bridge proves measurable path-valued random variables and preservation of one-time laws from continuous coordinate modifications. Existence of such modifications from the source Gaussian coordinates remains open. Full build 4205 jobs, 3171 transitive axiom checks, only propext/Classical.choice/Quot.sound. Exact statements and limitations: IBM_CAMPAIGN_STATE.md.


## IBM conditional Gaussian mixture and source fourth moments — 2026-10-13

The source scenery law and both source fourth-moment increment identities are actual verified facts. Conditional Gaussian event and first/second-moment formulas for the composition, plus the clock mixture event law, are verified under explicit continuous-modification hypotheses. Full build 4208 jobs, 3181 transitive axiom checks, only propext/Classical.choice/Quot.sound. Exact statements and open existence obligation: IBM_CAMPAIGN_STATE.md.

## IBM conditional two-time covariance — 2026-10-13

The exact two-sided Brownian covariance kernel for the composed process is proved at each fixed clock sample under the continuous-scenery-modification hypothesis. Full build 4209 jobs, complete 3182-declaration transitive audit, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM conditional finite-dimensional Gaussian laws — 2026-10-13

The composed process is a jointly Gaussian process on the scenery factor for every fixed clock sample under the continuous-modification hypothesis. Every finite conditional observation vector has a Gaussian law. Full build 4210 jobs, complete 3184-declaration transitive audit, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM conditional fourth-increment identity — 2026-10-13

Exact conditional fourth moment `3 * ||C_t|-|C_s||²` is proved under the continuous-scenery-modification hypothesis. Full build 4211 jobs, complete 3185-declaration audit, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM singular campaign: concrete L²-to-H⁻¹ distributional derivative — 2026-10-13

The derivative of any complex Lebesgue-L² function is bundled in Mathlib's actual H⁻¹(ℝ) Bessel-potential space, with the correct underlying distribution and an algebraic linear map. Boundedness, IBM-kernel convergence and local-time estimates remain separate. Full build 4228 jobs; 3191 transitive axiom checks, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM bounded H⁻¹ derivative — 2026-10-13

The concrete distributional derivative now extends as a bounded continuous linear map from complex Lebesgue L²(ℝ) to Mathlib H⁻¹(ℝ), by a verified closed-graph argument. This does not establish any IBM-specific kernel limit. Full build 4229 jobs; 3197 transitive axiom checks, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM random-field H⁻¹ transfer — 2026-10-13

Bounded differentiation now acts from L²(clock;L²(space)) to L²(clock;H⁻¹(space)), with almost-everywhere section identification and convergence transfer. No IBM-specific kernel or local-time limit is asserted. Full build 4230 jobs; 3201 transitive axiom checks, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM origin Dirac boundary mass in H⁻¹ — 2026-10-13

Mathlib's actual tempered Dirac distribution at zero is proved to belong to H⁻¹(ℝ) and bundled there. This is only the deterministic boundary target, not a local-time convergence theorem. Full build 4231 jobs; 3204 transitive axiom checks, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM random H⁻¹ Dirac boundary channel — 2026-10-13

A bounded map takes square-integrable clock coefficients to H⁻¹-valued random Dirac masses, with section identity and convergence transfer. Brownian local-time coefficients remain unconstructed. Full build 4232 jobs; 3209 transitive axiom checks, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM interior/boundary H⁻¹ assembly — 2026-10-13

A bounded operator assembles convergent interior L² spatial kernels and square-integrable clock boundary coefficients into L²(clock;H⁻¹(space)), with a two-channel norm bound. No actual IBM correction kernel is asserted. Full build 4233 jobs; 3216 transitive axiom checks, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM conditional mollified spatial chain rule — 2026-10-13

The exact second-derivative formula for f(x+U_r) is verified under explicit actual spatial derivative fields U,V,W and test-function derivatives. No mollifier or Malliavin field is yet constructed. Full build 4234 jobs; 3220 transitive axiom checks, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM spatial convolution and actual derivatives — 2026-10-13

For a supplied continuous path and compactly supported C² kernel, actual Lebesgue convolution and its first two derivative-kernel representations are verified, as is the second spatial chain rule. Stochastic measurability and Brownian source construction remain open. Full build 4235 jobs; 3228 transitive axiom checks, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM measurable mollified random-time process — 2026-10-13

For supplied continuous measurable source families and a compactly supported C² kernel, the actual convolution fields are jointly measurable, and their random-time composition is a measurable continuous-path-valued process on the joint product factor. Brownian continuous-modification existence is still open. Full build 4237 jobs; 3242 transitive axiom checks, only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM concrete normalized mollifier — 2026-10-13

A specific smooth nonnegative unit-mass bump sequence with shrinking support now instantiates the convolution kernel, and its pathwise convolution converges pointwise to every supplied continuous scenery path, including at a fixed random clock argument. The continuous source modifications, stronger stochastic convergence, derivative limits and singular correction remain open. Full build 4239 jobs; 3250 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM sectionwise dual distribution identity — 2026-10-13

The bounded interior-plus-boundary H⁻¹ assembly now has an almost-everywhere section formula and an exact tempered-distribution identity `∂u+aδ₀` for arbitrary admissible input fields. IBM-specific local-time inputs and convergence remain open. Full build 4240 jobs; 3252 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM H⁻¹–H¹ weighted-L² dual pairing — 2026-10-13

A concrete bounded pairing sends every H⁻¹ element to a continuous H¹ functional and separates H⁻¹ points. Compatibility with distribution action and onto-isometric duality remain separate. Full build 4241 jobs; 3260 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM abstract observable restriction — 2026-10-13

The maximal restriction of any closed partial linear source operator to an observable submodule is a closed partial linear operator, with exact domain and graph identities. This requires no observable-domain density; IBM's continuous source modifications and observable core density are still open. Full build 4242 jobs; 3264 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM projected divergence transfer — 2026-10-13

For a closed observable subspace with a dense restricted domain, every source-adjoint integrand lies in the restricted adjoint domain and its value is the orthogonal projection of the source divergence. This is a one-sided domain inclusion; IBM observable density is still open. Full build 4243 jobs; 3268 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM observable-core density criterion — 2026-10-13

Source-domain density plus invariance of that domain under observable orthogonal projection implies density of the restricted derivative domain. IBM projection invariance is not established. Full build 4244 jobs; 3269 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM positive-time scenery observable instantiation — 2026-10-13

The abstract closed restriction specializes to the existing dense Gaussian observable derivative for the positive-time coordinates of the verified two-sided IBM scenery source. This is a source-factor result, not compression onto the full IBM observable sigma-algebra. Full build 4245 jobs; 3274 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM observable graph norm and subcore closure — 2026-10-13

The abstract observable restriction has exactly the source graph norm. Every compatible smaller partial operator is closable and its closure lies within the maximal restriction; equality needs an independent graph-core result. Full build 4246 jobs; 3277 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM observable-density annihilator criterion — 2026-10-13

The maximal restricted derivative domain is dense exactly when no nonzero observable vector annihilates it under the Hilbert inner product. This is an exact criterion, not an IBM density proof. Full build 4247 jobs; 3278 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM abstract density-transfer obstruction — 2026-10-13

A proper source domain has a one-dimensional observable subspace with zero, hence nondense, restricted domain—even if the source domain is dense. This refutes automatic density transfer, not IBM-specific density. Full build 4248 jobs; 3282 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## Conditional IBM observable L² space — 2026-10-13

For supplied measurable continuous scenery and clock paths on the verified joint source, the sigma-algebra generated by all random-time composition coordinates gives a closed L² subspace and a contractive conditional-expectation projection. Continuous Brownian modifications and derivative-domain stability are still open; this is conditional, not an unconditional IBM compression. Full build 4249 jobs; 3288 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## Closure of projected source divergence — 2026-10-13

The projected source divergence is a closable partial operator whose graph and closure lie inside the full observable adjoint whenever both requisite derivative domains are dense. Equality is not established; the observable graph-core problem remains open. Full build 4250 jobs; 3292 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## Conditional IBM observable projection identities — 2026-10-13

Conditional expectation onto the supplied-path IBM observable L² space fixes observable inputs and preserves inner products against observable test functions. Source derivative-domain stability remains open. Full build 4251 jobs; 3294 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM sharp H⁻¹–H¹ duality — 2026-10-13

The weighted-L² H⁻¹ pairing has exactly the H⁻¹ operator norm and uniquely represents every continuous H¹ functional. Agreement of this Hilbert-model pairing with the manuscript's Schwartz-distribution action is still open. Full build 4252 jobs; 3296 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM signed spatial overlap — 2026-10-13

The covariance of two source Brownian-scenery increments is the signed spatial overlap of their oriented nonnegative intervals. Under explicit continuous-modification hypotheses, the same exact formula holds conditionally for two IBM increments at any fixed clock sample. This is covariance structure, not a quartic-variation limit. Full build 4254 jobs; 3301 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM reflected-clock fourth-moment correction — 2026-10-13

The reflected-clock squared increment equals the unreflected squared increment minus a nonnegative penalty supported exactly on zero-crossing endpoints. The conditional fourth moment inherits the exact penalty and a sharp same-sign equality. Brownian-clock expectation convergence remains open. Full build 4256 jobs; 3311 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM finite-family quartic expectation — 2026-10-13

For any finite family of time intervals and each fixed clock sample, the sum of IBM fourth powers is integrable in the scenery variable and has exact expectation `3` times the sum of squared reflected-clock displacements. Its zero-crossing penalty and upper bound are explicit. No partition limit or full joint expectation has been proved. Full build 4257 jobs; 3316 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## Mixed fourth-power Gaussian moment — 2026-10-13

Actual correlated first-chaos representatives satisfy `E[A⁴B⁴]=9u²v²+72uvc²+24c⁴`, derived through the verified fourth-Hermite decomposition and Wick orthogonality. The IBM reflected-clock substitution and partition variance estimates remain open. Full build 4258 jobs; 3321 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM paired fourth-power increments — 2026-10-13

The verified source scenery and conditional supplied-path IBM increments satisfy the exact mixed eighth-moment Wick polynomial, with covariance equal to signed reflected-clock spatial overlap. The conditional centered fourth-power product is `72uvc²+24c⁴`. Clock averaging and partition variance limits remain open. Full build 4260 jobs; 3325 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM finite quartic-sum conditional variance — 2026-10-13

Each fixed-clock fourth-power increment lies in scenery L², and the centered second moment of any finite quartic sum is exactly the double sum of `72u_pu_qc²+24c⁴` spatial-overlap contributions. This is the analytic input for partition limits, not a convergence theorem. Full build 4261 jobs; 3329 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM clock-averaged conditional quartic upper bound — 2026-10-13

The verified Brownian-clock increment has second moment equal to elapsed time; reflection can only lower its squared-increment expectation. Consequently the iterated scenery-then-clock expectation of a finite conditional IBM quartic sum is at most three times total ordered interval length. This is an upper bound, not a derived `3T` limit or a Fubini theorem for the joint process. Full build 4262 jobs; 3334 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM finite-partition fourth-order Taylor formula — 2026-10-13

A genuine fourth-degree Taylor expansion with a `C⁵` fifth-derivative remainder bound telescopes exactly along any finite supplied-path IBM partition. It does not establish convergence of the weighted quartic term or the lower-rank stochastic terms. Full build 4263 jobs; 3340 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## Finite IBM quartic variation is observable — 2026-10-13

Every finite quartic-variation sum is measurable with respect to the sigma-algebra generated by the supplied IBM composition coordinates, and it is definitionally the same sum used in the conditional moment formulas. No limiting variation has been proved. Full build 4264 jobs; 3344 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.

## IBM finite quartic expectation under the joint law — 2026-10-13

For measurable continuous Brownian-source modifications supplied as explicit hypotheses, the finite quartic variation is jointly measurable and integrable on the product source space. Fubini identifies its actual joint expectation with the clock average of the exact conditional formula, bounded by three times total ordered interval length. Source modifications and the refining-partition `3T` limit remain unproved. Full build 4265 jobs; 3349 transitive axiom checks with only propext/Classical.choice/Quot.sound. See IBM_CAMPAIGN_STATE.md.
