import GerverSofa.KernelOnly.FullADSoundness

/-!
# Concrete numerical soundness package

This file assembles the proved transcendental layer and both concrete interval
AD evaluations into the exact numerical soundness record consumed by the
kernel certificate.  No analytic premise remains as a field of this value.
-/

noncomputable section

namespace GerverSofa

/-- Complete semantic soundness of the transcendental evaluator and the
frozen 4D/22D interval-AD calls. -/
def gerverNumericalSoundness : GerverNumericalSoundness where
  transcendentals := exactTranscendentalSoundness
  reduced_ad := Reduced.reducedADSoundness
  full_ad := Romik.fullADSoundness

/-- Proposition-level handle used by the final axiom audit. -/
theorem gerverNumericalSoundness_exists : Nonempty GerverNumericalSoundness :=
  ⟨gerverNumericalSoundness⟩

end GerverSofa
