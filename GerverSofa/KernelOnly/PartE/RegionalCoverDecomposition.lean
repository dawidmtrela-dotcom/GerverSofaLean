import GerverSofa.KernelOnly.PartE.FiniteCoverReplay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Part E05: regional decomposition of the finite rejection cover

E04 established sound replay for a finite list of rational angle cells.  E05
adds the geometric composition layer needed to generate the global data in
independent batches.  The physical angle triangle outside the exact projection
of `Reduced.box` is decomposed into four explicit regions: below or above the
local `phi` interval, and below or above the local `theta` interval.

Regional certificates can be replayed separately and appended without losing
soundness.  Four such certificates compose to the exact
`FiniteRejectionCoverTarget` required by E04.  The already checked origin cell
is also packaged as the first genuine regional certificate.
-/

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core
open LeanCert.Engine

/-- A replayed finite cover of an arbitrary two-angle region. -/
def RegionalRejectionCoverTarget (region : ℝ → ℝ → Prop)
    (cells : List AngleCell) (cfg : EvalConfig := {}) : Prop :=
  allCellsRejected cells cfg = true ∧
    ∀ phi theta : ℝ, region phi theta → coveredBy cells phi theta

/-- Every point in a replayed regional certificate is excluded from being a
common zero of the two smooth residuals. -/
theorem no_common_zero_of_regionalRejectionCover
    (region : ℝ → ℝ → Prop) (cells : List AngleCell)
    (cfg : EvalConfig) (hregional : RegionalRejectionCoverTarget region cells cfg)
    {phi theta : ℝ} (hregion : region phi theta) :
    ¬ (scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0) := by
  exact no_common_zero_of_coveredBy_rejectedCells
    cells phi theta cfg hregional.1 (hregional.2 phi theta hregion)

/-- One rejected cell is already a regional certificate for its own
rectangle. -/
theorem regionalRejectionCoverTarget_singleton
    (cell : AngleCell) (cfg : EvalConfig)
    (hreject : cell.rejected cfg = true) :
    RegionalRejectionCoverTarget
      (fun phi theta => cell.Contains phi theta) (cell :: []) cfg := by
  unfold RegionalRejectionCoverTarget
  constructor
  · simp [allCellsRejected, hreject]
  · intro phi theta hmem
    exact ⟨cell, by simp, hmem⟩

/-- Independently replayed regional certificates compose by list append. -/
theorem regionalRejectionCoverTarget_append
    (leftRegion rightRegion : ℝ → ℝ → Prop)
    (leftCells rightCells : List AngleCell) (cfg : EvalConfig)
    (hleft : RegionalRejectionCoverTarget leftRegion leftCells cfg)
    (hright : RegionalRejectionCoverTarget rightRegion rightCells cfg) :
    RegionalRejectionCoverTarget
      (fun phi theta => leftRegion phi theta ∨ rightRegion phi theta)
      (leftCells ++ rightCells) cfg := by
  rcases hleft with ⟨hallLeft, hcoverLeft⟩
  rcases hright with ⟨hallRight, hcoverRight⟩
  have hallLeft' : leftCells.all (fun cell => cell.rejected cfg) = true := by
    simpa only [allCellsRejected] using hallLeft
  have hallRight' : rightCells.all (fun cell => cell.rejected cfg) = true := by
    simpa only [allCellsRejected] using hallRight
  constructor
  · change (leftCells ++ rightCells).all
      (fun cell => cell.rejected cfg) = true
    apply List.all_eq_true.mpr
    intro cell hcell
    rcases List.mem_append.mp hcell with hcell | hcell
    · exact (List.all_eq_true.mp hallLeft') cell hcell
    · exact (List.all_eq_true.mp hallRight') cell hcell
  · intro phi theta hregion
    rcases hregion with hregion | hregion
    · rcases hcoverLeft phi theta hregion with ⟨cell, hcell, hmem⟩
      refine ⟨cell, ?_, hmem⟩
      simpa only [List.mem_append, hcell, true_or]
    · rcases hcoverRight phi theta hregion with ⟨cell, hcell, hmem⟩
      refine ⟨cell, ?_, hmem⟩
      simpa only [List.mem_append, hcell, or_true]

/-! ## Four exact physical regions outside the local angle cell -/

def PhysicalPhiBelowRegion (phi theta : ℝ) : Prop :=
  PhysicalAngleDomain phi theta ∧
    ¬ ((reducedPhiInterval.lo : ℝ) ≤ phi)

def PhysicalPhiAboveRegion (phi theta : ℝ) : Prop :=
  PhysicalAngleDomain phi theta ∧
    ¬ (phi ≤ (reducedPhiInterval.hi : ℝ))

def PhysicalThetaBelowRegion (phi theta : ℝ) : Prop :=
  PhysicalAngleDomain phi theta ∧
    ¬ ((reducedThetaInterval.lo : ℝ) ≤ theta)

def PhysicalThetaAboveRegion (phi theta : ℝ) : Prop :=
  PhysicalAngleDomain phi theta ∧
    ¬ (theta ≤ (reducedThetaInterval.hi : ℝ))

/-- Failure of membership in the closed local angle rectangle is exactly one
of four endpoint failures. -/
theorem outside_reducedAngleCell_four_way {phi theta : ℝ}
    (houtside : ¬ reducedAngleCell.Contains phi theta) :
    (¬ ((reducedPhiInterval.lo : ℝ) ≤ phi)) ∨
      (¬ (phi ≤ (reducedPhiInterval.hi : ℝ))) ∨
      (¬ ((reducedThetaInterval.lo : ℝ) ≤ theta)) ∨
      (¬ (theta ≤ (reducedThetaInterval.hi : ℝ))) := by
  change ¬ (phi ∈ reducedPhiInterval ∧ theta ∈ reducedThetaInterval) at houtside
  simp only [IntervalRat.mem_def] at houtside
  by_cases hPhiLo : (reducedPhiInterval.lo : ℝ) ≤ phi
  · by_cases hPhiHi : phi ≤ (reducedPhiInterval.hi : ℝ)
    · by_cases hThetaLo : (reducedThetaInterval.lo : ℝ) ≤ theta
      · exact Or.inr (Or.inr (Or.inr (by
          intro hThetaHi
          exact houtside ⟨⟨hPhiLo, hPhiHi⟩, ⟨hThetaLo, hThetaHi⟩⟩)))
      · exact Or.inr (Or.inr (Or.inl hThetaLo))
    · exact Or.inr (Or.inl hPhiHi)
  · exact Or.inl hPhiLo

/-- Every physical point outside the local angle cell belongs to at least one
of the four bounded regional cover obligations. -/
theorem physical_outside_reduced_in_four_regions {phi theta : ℝ}
    (hdom : PhysicalAngleDomain phi theta)
    (houtside : ¬ reducedAngleCell.Contains phi theta) :
    PhysicalPhiBelowRegion phi theta ∨
      PhysicalPhiAboveRegion phi theta ∨
      PhysicalThetaBelowRegion phi theta ∨
      PhysicalThetaAboveRegion phi theta := by
  rcases outside_reducedAngleCell_four_way houtside with h | h | h | h
  · exact Or.inl ⟨hdom, h⟩
  · exact Or.inr (Or.inl ⟨hdom, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hdom, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hdom, h⟩))

/-- Four independently generated regional certificates yield E04's exact
global finite rejection cover. -/
theorem finiteRejectionCoverTarget_of_four_regions
    (phiBelowCells phiAboveCells thetaBelowCells thetaAboveCells :
      List AngleCell)
    (cfg : EvalConfig)
    (hPhiBelow : RegionalRejectionCoverTarget
      PhysicalPhiBelowRegion phiBelowCells cfg)
    (hPhiAbove : RegionalRejectionCoverTarget
      PhysicalPhiAboveRegion phiAboveCells cfg)
    (hThetaBelow : RegionalRejectionCoverTarget
      PhysicalThetaBelowRegion thetaBelowCells cfg)
    (hThetaAbove : RegionalRejectionCoverTarget
      PhysicalThetaAboveRegion thetaAboveCells cfg) :
    FiniteRejectionCoverTarget
      (phiBelowCells ++
        (phiAboveCells ++ (thetaBelowCells ++ thetaAboveCells))) cfg := by
  have hTheta := regionalRejectionCoverTarget_append
    PhysicalThetaBelowRegion PhysicalThetaAboveRegion
    thetaBelowCells thetaAboveCells cfg hThetaBelow hThetaAbove
  have hUpper := regionalRejectionCoverTarget_append
    PhysicalPhiAboveRegion
    (fun phi theta =>
      PhysicalThetaBelowRegion phi theta ∨ PhysicalThetaAboveRegion phi theta)
    phiAboveCells (thetaBelowCells ++ thetaAboveCells) cfg hPhiAbove hTheta
  have hAll := regionalRejectionCoverTarget_append
    PhysicalPhiBelowRegion
    (fun phi theta =>
      PhysicalPhiAboveRegion phi theta ∨
        (PhysicalThetaBelowRegion phi theta ∨
          PhysicalThetaAboveRegion phi theta))
    phiBelowCells
    (phiAboveCells ++ (thetaBelowCells ++ thetaAboveCells))
    cfg hPhiBelow hUpper
  refine ⟨hAll.1, ?_⟩
  intro phi theta hdom houtside
  exact hAll.2 phi theta
    (physical_outside_reduced_in_four_regions hdom houtside)

/-! ## First genuine regional data item -/

/-- The physical portion of E04's already replayed origin rectangle. -/
def OriginPilotPhysicalRegion (phi theta : ℝ) : Prop :=
  PhysicalAngleDomain phi theta ∧ originCell.Contains phi theta

/-- The origin pilot is a complete regional certificate, not merely a Boolean
probe. -/
theorem originPilotPhysical_regionalCover :
    RegionalRejectionCoverTarget
      OriginPilotPhysicalRegion originPilotCells := by
  constructor
  · exact originPilotCells_all_rejected
  · intro phi theta hregion
    exact ⟨originCell, by simp [originPilotCells], hregion.2⟩

/-- The first regional certificate lies wholly in the lower-theta exclusion
side of the local angle box. -/
theorem originPilotPhysicalRegion_subset_thetaBelow {phi theta : ℝ}
    (hregion : OriginPilotPhysicalRegion phi theta) :
    PhysicalThetaBelowRegion phi theta := by
  refine ⟨hregion.1, ?_⟩
  have htheta : theta ∈ originThetaInterval := by
    simpa [originCell] using hregion.2.2
  rw [IntervalRat.mem_def] at htheta
  have hgap : (originThetaInterval.hi : ℝ) <
      (reducedThetaInterval.lo : ℝ) := by
    norm_num [originThetaInterval, reducedThetaInterval]
  exact not_le.mpr (lt_of_le_of_lt htheta.2 hgap)

end PartE
end GerverSofa
