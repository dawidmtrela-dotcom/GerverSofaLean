# Gerver sofa Lean formalisation

> **Current batch:** BATCH11, built on the user-confirmed FIX10 baseline (`lake build`: 8731 jobs; strict axiom audit clean). BATCH11 derives `x₂(π/2)=0` from the direct 22 equations and certified box instead of carrying it as a `KernelGerverCertificate` field. Read `BATCH11_README.md` first. BATCH11 itself still awaits the next pinned-toolchain build.

This repository is the cumulative Lean 4 project for the manuscript
**“Certified Geometry and Admissible Motion of Gerver's Sofa”**.  It starts
from the source set that the user actually built successfully under Lean
4.33.0 / mathlib v4.33.0 and adds a single consolidated kernel-hardening and
full-article target layer.

## Trustworthy status

Two facts must be kept separate.

1. **The base source set is build-confirmed.**  Before the new `KernelOnly/`
   layer was added, the user obtained:

   ```text
   Build completed successfully (8721 jobs).
   ```

2. **The present one-shot source set has not yet been compiled in the packaging
   runtime.**  That runtime has no `lean`, `lake`, or `elan` executable.  The
   new files therefore form a build candidate to be checked by the user's
   pinned Lean installation.

A successful `lake build` of this archive will establish that all definitions
and proof terms currently written are accepted by Lean.  It will **not by
itself** establish the whole manuscript unless a concrete term inhabiting
`GerverSofa.FullCertificationTarget` is also present.  This release deliberately
contains no fake inhabitant, user axiom, `sorry`, `admit`, `opaque`, `unsafe`,
or `native_decide` escape.

## What the one-shot layer adds

- kernel reduction (`decide +kernel`) for the two frozen exact-rational replay
  theorems;
- semantic soundness of rational interval multiplication;
- exact coordinate equivalences between named 4D/22D records and `Fin n → ℝ`;
- a Banach contraction theorem producing an actual unique zero rather than
  accepting the zero as certificate input;
- generic grid-to-continuum transfer lemmas;
- explicit semantic interfaces for trigonometric enclosures and interval AD;
- explicit exact rational contraction bounds for both frozen systems;
- endpoint symmetry reduction;
- a strengthened `KernelGerverCertificate`;
- set-theoretic Gerver/Romik reconstruction infrastructure;
- formal statement carriers for the eighteen-piece boundary, injectivity,
  Lebesgue-area threshold, and Baek first variation;
- a single fail-closed proposition:

  ```lean
  GerverSofa.FullCertificationTarget
  ```

  defined as `Nonempty FullArticleCertificate`.

The difficult analytic and geometric bridges are not silently assumed.  They
are visible as fields of proof-carrying structures and are listed precisely in
`STATUS.md` and `docs/PROOF_OBLIGATIONS.md`.

## First build on the user's Windows installation

The project is pinned by `lean-toolchain` and `lakefile.toml` to Lean 4.33.0
and mathlib v4.33.0.  From this directory run:

```powershell
lake build
```

The mathlib cache is already present in the user's existing working directory.
On a clean extraction, first run:

```powershell
lake exe cache get
lake build
```

After a successful build, run:

```powershell
lake env lean GerverSofa/FinalAxiomAudit.lean
```

For all local checks in one command:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/verify_windows.ps1
```

## Independent non-Lean checks already executed

```text
python scripts/audit.py              PASS
python scripts/contraction_audit.py  PASS
```

The first check reruns the submitted Python verifier byte-for-byte, compares
all 552 frozen box/preconditioner rationals with the source, verifies imports
and lexical structure, and rejects forbidden trust escapes in uncommented Lean
source.  These static checks are evidence, not a substitute for `lake build`.

## Key files

- `GerverSofa/ExactReplay.lean` — exact rational replay and contraction data.
- `GerverSofa/RationalInterval.lean` — interval semantics, including
  multiplication.
- `GerverSofa/KernelOnly/Contraction.lean` — Banach fixed-point endgame.
- `GerverSofa/KernelOnly/SoundnessInterfaces.lean` — exact real-semantics
  obligations for transcendentals and AD.
- `GerverSofa/KernelOnly/CertificateLayers.lean` — strengthened main
  certificate.
- `GerverSofa/KernelOnly/ArticleClaims.lean` — formal statement layer for all
  headline manuscript claims.
- `GerverSofa/KernelOnly/FinalTarget.lean` — single final target.
- `GerverSofa/FinalAxiomAudit.lean` — strict dependency audit.
- `docs/ONE_SHOT_FULL_CERTIFICATION.md` — architecture and boundary.
- `docs/FINAL_BUILD_PROTOCOL.md` — exact test protocol.
