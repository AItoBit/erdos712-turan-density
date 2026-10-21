# Turan density existence and the graph case

This project packages a user-supplied Lean development concerning
[Erdos problem 712](https://www.erdosproblems.com/712).

It establishes the classical averaging argument for convergence of
`ex_r(n, K_k^r) / binomial(n,r)`, bounds its limit between zero and one, and
derives Turan's graph formula for `r = 2`:
`1 - 1/(k-1)` with the binomial normalization, or half that value with
denominator `n^2`.

These foundational extremal-combinatorics results may be useful to researchers
formalizing hypergraph Turan problems. No novelty is claimed. In particular,
this development does **not** determine the densities for `k > r > 2` and
does not solve Erdos 712 or the tetrahedron conjecture.

## Verification status

UNVERIFIED at preparation time. No local Lean compiler was available.
The original proof text was retained, with a module header and public exposure.
A successful build, axiom audit, Comparator run and Palomar full mechanical
preflight are required before this may be described as verified.

The `Challenge.lean` theorem bodies intentionally contain `sorry`.
The corresponding proofs are in `Solution.lean`; Comparator must establish
that they have the same types and use only permitted axioms.

## Reproduce

```sh
lake exe cache get
lake build Challenge Solution
lake env lean Audit.lean
```

The pinned full preflight workflow is in `.github/workflows/palomar-preflight.yml`.
Do not submit to Palomar before its mechanical report says `status: pass`.

## Provenance and limitations

The user supplied the proof file. Codex prepared the statement split, metadata
and workflows. No independent human review is claimed. The definitions in
Challenge spell out the finite edge families and complete-subgraph exclusion.

The function `turanDensity` is defined by a limit; proving convergence is a
supporting theorem, not an explicit solution of the value question.
The graph statements assume `2 <= k`; limiting ratios ignore the finitely many
indices with zero denominator. Claims about degenerate `r,k` use Lean's
totalized conventions.

The source problem page could not be retrieved directly during preparation
(HTTP 403); its main statement was cross-checked against the current upstream
formal-conjectures file. The PR uses the upstream extremal-number definition,
whereas this standalone project retains the supplied finite-family definition.
No compiled equivalence between those definitions is claimed.

License: Apache-2.0.
