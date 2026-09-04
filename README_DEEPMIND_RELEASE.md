# Gerver Sofa — DeepMind ABφθ uniqueness kernel release

Frozen external Lean 4 proof release for publication and linking from
Google DeepMind `formal-conjectures`.

## Certified theorem

`GerverSofa.PartE.deepMindABPhiTheta_existsUnique`

```lean
∃! ABphiTheta : ℝ × ℝ × ℝ × ℝ,
  DeepMindABPhiThetaSpec
    ABphiTheta.1 ABphiTheta.2.1
    ABphiTheta.2.2.1 ABphiTheta.2.2.2
```

`DeepMindABPhiThetaSpec` mirrors the current upstream
`MovingSofa.GerversSofa.ABφθSpec`: the same physical-domain inequalities and
the same four Gerver/Romik equations.

## Verified status

- 8713 / 8713 original global-exclusion obligations have proof providers;
- all four final reconstruction modules: PASS;
- final theorem: PASS;
- final axiom-audit module: PASS;
- audited local import closure of the final theorem: 907 Lean source files;
- forbidden source hits in that closure: 0;
- no `native_decide`, `sorry`, `admit`, custom `axiom`, or `unsafe`
  in the audited final local source closure;
- `#print axioms` reports only:
  `propext`, `Classical.choice`, `Quot.sound`.

The untrusted discovery computation is not imported by the final theorem.
Primitive certificate claims are rechecked by Lean kernel proof terms and
combined by proved soundness lemmas.

## Toolchain

- Lean 4.33.0
- mathlib v4.33.0
- leancert commit `571a228555ae38742448854be81d7b59d994a8e3`

## Reproduction

From the repository root:

```powershell
lake build GerverSofa.KernelOnly.PartE.E24KC6KernelFinalAxiomAudit
```

or run:

```powershell
powershell -ExecutionPolicy Bypass -File .\REPRODUCE.ps1
```

The exact successful run and its evidence are preserved under `evidence/`.

## Google DeepMind `formal-conjectures`

The current upstream target is:

`MovingSofa.GerversSofa.ABφθSpec.existsUnique`

For a long proof hosted externally, the upstream metadata change is:

```lean
@[formal_proof using lean4 at "<PUBLIC_STABLE_PROOF_URL>"]
```

See:
- `FORMAL_CONJECTURES_ISSUE_TEMPLATE.md`
- `FORMAL_CONJECTURES_PATCH_TEMPLATE.txt`
- `PR_BODY_TEMPLATE.md`
