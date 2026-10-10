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
