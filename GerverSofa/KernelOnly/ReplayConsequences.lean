import GerverSofa.ExactReplay
import GerverSofa.CertificateManifest

/-!
# Named consequences of the frozen kernel-only certificate

These handles intentionally reason about the proof-carrying rational data, not
about re-running the expensive Krawczyk/grid search inside kernel reduction.
The latter remains available under `ExactReplay.executable*` for independent
diagnostic comparison.
-/

namespace GerverSofa.ExactReplay

set_option maxRecDepth 100000 in
theorem reduced_image_strict :
    RatInterval.allStrictInsideB reducedKrawczykImage reducedInputBox = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem full_image_strict :
    RatInterval.allStrictInsideB fullKrawczykImage fullInputBox = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem reduced_contraction_bound_lt :
    reducedContractionBound < (1 : ℚ) / 1000000000000 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem full_contraction_bound_lt :
    fullContractionBound < (1 : ℚ) / 10000000000 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem reduced_radius_ratio_lt :
    reducedRadiusRatio < (422 : ℚ) / 1000 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem full_radius_ratio_lt :
    fullRadiusRatio < (95 : ℚ) / 10000 := by
  decide +kernel

end GerverSofa.ExactReplay

namespace GerverSofa.CertificateManifest

set_option maxRecDepth 100000 in
theorem machin_inside_declared :
    RatInterval.strictInsideB machinPi declaredPi = true := by
  simpa [piCheck] using piCheck_eq_true

set_option maxRecDepth 100000 in
theorem area_interval_positive_threshold :
    scalar_area.lo > (24206448441453775 : ℚ) / 10000000000000000 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem grid_continuum_margins :
    grid_gu_continuum > (1710 : ℚ) / 10000 ∧
    grid_gv_continuum > (1710 : ℚ) / 10000 := by
  constructor <;> decide +kernel

end GerverSofa.CertificateManifest
