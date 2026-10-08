# ATK cross-repository proof reuse
Repository: ShantiDraconis/m-core-beal
Status: SOURCE; NOT KERNEL VERIFIED.

## Dependency references
- M-Core/final-proof/pnp_prior_formalization_reuse.json — historical conditional reuse.
- M-Core/evidence/endpoint_states.json — declarations and reference states.
- axiomatic-millenium/AxiomaticMillenium.lean — seven-lane import root.
- axiomatic-millenium/AxiomaticMillenium/SevenLaneClosureKernel.lean — structural counts, not terminal closure.
- m-core-p-vs-np/lean/MCore/Real/P01FinalCertificate.lean — P01ConstructionGap is Nonempty P01MachineConstruction.
- M-Core/imports/pnp/b406b806/lean/MCore/Real/FinalExternalTwoGap.lean — requires P01ConstructionGap and G21Pointwise.

## Required verification
- [ ] Pin source commits and verify exact elaborated Lean types.
- [ ] Reuse verified lemmas only with all original hypotheses.
- [ ] Compile and audit #print axioms before promoting certificates.
- [ ] Preserve main and frozen branches; never change OPEN_MATH status by assertion.
