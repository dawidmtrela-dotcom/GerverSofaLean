# External Lean 4 proof for `MovingSofa.GerversSofa.ABφθSpec.existsUnique`

I have completed an external Lean 4 formal proof of the existing theorem
`MovingSofa.GerversSofa.ABφθSpec.existsUnique` in
`FormalConjectures/Wikipedia/MovingSofa.lean`.

The external development mirrors the upstream `ABφθSpec` (the same
physical-domain inequalities and the same four equations) and proves the exact
tuple-shaped existence-and-uniqueness statement.

Verification summary:

- Lean 4.33.0;
- final theorem builds successfully;
- 8713/8713 global-exclusion obligations have kernel-checked proof providers;
- audited local import closure: 907 Lean source files;
- no `sorry`, `admit`, `native_decide`, custom `axiom`, or `unsafe` in the
  final audited local source closure;
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`;
- reproducibility evidence and SHA-256 manifests are included.

Because the proof is substantially longer than the 25–50 line guideline for
in-tree proofs, I plan to host it in a public repository and submit a small PR
adding:

```lean
formal_proof using lean4 at "<PUBLIC_STABLE_PROOF_URL>"
```

to the existing theorem.

External proof:
`<PUBLIC_STABLE_PROOF_URL>`
