# GerverSofaLean v1.1.0 — Part F DeepMind interoperability bridge

This release freezes the Lean 4 proof that the concrete `MovingSofa.gerversSofa` from `google-deepmind/formal-conjectures` admits a valid moving-sofa witness under the corrected translate-then-rotate convention merged upstream in google-deepmind/formal-conjectures#5827.

## Main result

```lean
MovingSofa.isMovingSofa_gerversSofa :
  ∃ m : Set.Icc (0 : ℝ) 1 → MovingSofa.E2,
    MovingSofa.IsMovingSofa MovingSofa.gerversSofa m
```

The final source is `GerverSofa/KernelOnly/PartF/F07UpstreamMotion.lean` in the attached frozen artifact.

## Audit summary

- Lean 4.33.0
- audited local import closure: 1055 Lean source files
- final axiom audit: 219 declarations
- no `sorryAx` in the audited declarations
- only `propext`, `Classical.choice`, and `Quot.sound`
- corrected literal upstream-definition mirror bridge: PASS
- concrete moving-sofa witness: PASS

## Artifact

`GerverSofaLean_PartF_v1.1.0.zip`

SHA-256:

```text
7c496150f709ac709ae01f4836e9a702a18f752450efa69f15cf44264c0c2f77
```

The artifact contains the full audited source closure, Part F sources, manifests, build logs, axiom logs, and review-ready upstream compatibility evidence.

## Scope

This release proves validity of the concrete Gerver sofa as a moving sofa. It does **not** claim the global optimality statements `sofaConstant_eq` or `sofaConstant_eq_volume_gerversSofa`.

Prepared with AI assistance; verification claims refer to actual Lean runs preserved in the artifact.
