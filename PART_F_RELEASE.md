# Part F — DeepMind `gerversSofa` moving-sofa bridge

This release records the external Lean 4 development proving that the concrete `MovingSofa.gerversSofa` used by `google-deepmind/formal-conjectures` admits a valid moving-sofa witness after the `rotateTranslate` convention was corrected upstream in google-deepmind/formal-conjectures#5827.

## Main theorem

The frozen development proves:

```lean
MovingSofa.isMovingSofa_gerversSofa :
  ∃ m : Set.Icc (0 : ℝ) 1 → MovingSofa.E2,
    MovingSofa.IsMovingSofa MovingSofa.gerversSofa m
```

The final upstream-adapter source is `GerverSofa/KernelOnly/PartF/F07UpstreamMotion.lean` inside the frozen artifact.

## What Part F establishes

The development proves, for the exact DeepMind integral path definitions mirrored in the artifact:

- the parameter dictionary linking the DeepMind/Gerver constants to the certified Romik parameters;
- the phase-by-phase relation `x_R(t) = R_t p_G(t)`;
- equality of the corresponding hallway families under the documented translate-then-rotate convention;
- equality of the literal corrected upstream `gerversSofa` with the certified coordinate-image sofa;
- transport of the previously certified moving-sofa motion to the concrete upstream set;
- the resulting `isMovingSofa_gerversSofa` theorem.

This does **not** claim or prove the global optimality statements `sofaConstant_eq` or `sofaConstant_eq_volume_gerversSofa`.

## Verification

Frozen Part F artifact: `GerverSofaLean_PartF_v1.1.0.zip`.

The audit recorded in that artifact reports:

- Lean 4.33.0;
- 1055 source files in the audited local import closure;
- 219 audited declarations;
- no `sorryAx` in the audited declarations;
- only `propext`, `Classical.choice`, and `Quot.sound` in the final axiom audit;
- the corrected literal upstream-definition mirror bridge: PASS;
- the concrete moving-sofa witness: PASS.

The artifact also contains source manifests, build logs, axiom logs, and the corrected-upstream compatibility material used during the review-ready run.

## Upstream context

The proof was initially blocked by google-deepmind/formal-conjectures#5270: the old implementation of `rotateTranslate` implemented the opposite composition order from its documented Gerver convention. Upstream PR #5827 fixed that issue on 13 September 2026 and added the regression theorem

```lean
rotateTranslate α p q = rotation α (q + p)
```

which is precisely the convention used by this bridge.

Prepared with AI assistance; all proof and audit claims above refer to actual Lean runs preserved in the frozen artifact.
