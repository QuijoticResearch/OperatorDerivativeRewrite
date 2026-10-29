# Fractional theta deformations: editorial status

Reviewed draft, October 29, 2026. Frozen mathematical baseline `bab688bb6140cd6316c80680095a914ea0d346db`.

This paper reconstructs the central proofs: actual theta kernel positivity/evenness/decay; entire transform and subquadratic growth; the third- and fourth-derivative endpoint cancellation; the separate cubic boundary term; finite real and infinite nonreal zero sets; order convergence; and compact escape under real/simple limiting zeros. Exact declarations and source hashes accompany the draft.

Human big-O estimates in the local cancellation proof are expository reconstructions of the verified derivative mechanism, not additional claims of newly named Lean big-O theorems. The existence of infinitely many complex zeros is proved through the zero-free logarithm and subquadratic finite-zero rigidity, not inferred from nonpolynomiality. The fourth remainder has a finite endpoint value, which need not vanish. Its sine boundary factor kills that value. The actual fifth derivative is distinct from the old truncated exponential jet.

The quadratic escape statement for every selected zero remains conditional on real and simple limiting zeros. A deliberately distant selected sequence is unconditional and has different quantifiers. The separate late-quartic all-real/simple theorem is mentioned only as a cited application and its saddle proof is explicitly outside this paper. No claim at t=0, general real orders above two, effective transition time, sharp escape rate, or RH implication is made.

Literature: an accessible primary author-hosted search result for David A. Cardon, *Fourier transforms having only real zeros*, Proc. AMS 133 (2005), 1349–1356, gives the exact transform class and bibliographic metadata; the direct PDF fetch timed out. It is cited for context, not used as a theorem premise. Pólya's 1923 Messenger paper was identified through bibliographic discovery but not retrieved in full; no detailed attribution to an uninspected theorem is made. The Dimitrov–Rusev survey points to classical non-even-power Fourier-transform phenomena. Novelty remains unresolved and requires a direct primary comparison.

The ten-page length is deliberate: the self-contained obstruction and escape proofs fit without the much larger quartic saddle analysis. The suggested 12–30 pages is treated as a preference, not a reason to add unrelated results. All pages are rendered and inspected; current build and review receipts govern PDF freshness. This is a reviewed draft, not publication-ready or externally submitted.
