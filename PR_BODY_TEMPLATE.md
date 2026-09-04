Title:
Link a Lean 4 proof of MovingSofa.GerversSofa.ABφθSpec.existsUnique

Body:
This PR adds a `formal_proof using lean4` link for
`MovingSofa.GerversSofa.ABφθSpec.existsUnique`.

The external Lean development proves global existence and uniqueness over the
full physical domain, not only uniqueness in a local numerical box. The final
proof is kernel-checked and includes a reproducibility bundle, full local
dependency audit, and `#print axioms` output.

The final audited theorem depends only on the standard Lean/mathlib axioms
`propext`, `Classical.choice`, and `Quot.sound`. The audited local import closure
contains no `sorry`, `admit`, `native_decide`, custom `axiom`, or `unsafe`.

External proof:
<PUBLIC_STABLE_PROOF_URL>

Reproduction:
`lake build GerverSofa.KernelOnly.PartE.E24KC6KernelFinalAxiomAudit`

The proof is kept external because it is substantially longer than the proof
length recommended for inclusion directly in formal-conjectures.