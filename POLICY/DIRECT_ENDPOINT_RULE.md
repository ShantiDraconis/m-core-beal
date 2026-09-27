# UNIVERSAL DIRECT-ENDPOINT RULE — LOCKED POLICY v1.0.0

Status: NORMATIVE / FAIL-CLOSED
Policy ID: ATK-DIRECT-ENDPOINT-v1

## Canonical rule

Every attempted OPEN_MATH / OPEN_BRIDGE closure MUST have the dependency form:

    SOURCE -> PRODUCED_WITNESS -> VERIFIED_WITNESS -> ENDPOINT

The following forms are forbidden:

    SOURCE -> HYPOTHESIS_EQ_SOURCE -> ... -> ENDPOINT
    SOURCE -> HYPOTHESIS_EQ_ENDPOINT -> ENDPOINT
    SOURCE -> ... -> ENDPOINT -> ... -> SOURCE
    ENDPOINT -> any prerequisite of ENDPOINT

## Mandatory conditions

1. No-return: after leaving SOURCE, no dependency path may return to SOURCE.
2. No-endpoint-assumption: ENDPOINT, or a proposition used merely as an equivalent renaming of ENDPOINT, may not be assumed in the derivation of ENDPOINT.
3. Witness production: every bridge must construct a witness from prior data.
4. Independent verification: the witness must have a verifier whose premises do not contain ENDPOINT.
5. Acyclicity: the dependency graph for the claimed closure must be a DAG, or be equipped with a well-founded relation proving no cyclic justification is used.
6. Strict progress: adding a parameter is admissible only if a declared well-founded measure strictly decreases.
7. No parameter inflation: a new variable that only renames the unresolved obligation is not progress and MUST remain OPEN_MATH/OPEN_BRIDGE.
8. Fail-closed: wiring, compilation, numerical evidence, symbolic equivalence, conjectural axioms, `sorry`, `admit`, or placeholders cannot promote OPEN_MATH to CLOSED.
9. Endpoint isolation: the only positive terminal step has the form VERIFIED_WITNESS -> ENDPOINT.
10. Certification: CLOSED / FROZEN / CERTIFIED is permitted only when the repository contains the concrete witness-producing proof, verifier, dependency certificate, and kernel/build evidence required by that repository.

## Universal closure schema

For problem i:

    source_i -> witness_i
    verify_i(witness_i)

Across problems:

    verified_1 ∧ ... ∧ verified_n
        -> aggregate_signature
        -> universal_endpoint_law
        -> endpoint

No `endpoint` term may appear among the assumptions used to construct any `witness_i`.

## Status semantics

- Missing witness: OPEN_MATH.
- Witness exists but verifier missing: OPEN_BRIDGE.
- Dependency cycle found: RED / REJECT.
- Equivalent endpoint hypothesis found: RED / REJECT.
- Parameter added without strict decrease: RED / PARAMETER_INFLATION.
- All obligations kernel/build verified: eligible for GREEN -> FROZEN -> CERTIFIED.

This policy is normative for the repository. Any change to this file changes the policy version and invalidates prior policy-lock checks until explicitly re-certified.
