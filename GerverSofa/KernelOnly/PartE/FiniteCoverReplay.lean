import GerverSofa.KernelOnly.PartE.ScaledResidualInterval
import Mathlib.Tactic.NormNum

/-!
# Part E04: finite-cover replay foundation

E03 supplied a sound, executable rejection theorem for one rational rectangle
in the `(phi, theta)` plane.  This module lifts that kernel to finite lists of
rectangles and states the exact two remaining data obligations:

1. a finite rejected cover of the physical angle triangle outside the angle
   projection of `Reduced.box`;
2. local reconstruction into `Reduced.box` inside that angle projection.

Their conjunction yields `TwoAngleEnclosureTarget` and therefore the exact
DeepMind-shaped uniqueness theorem.  No cover or local enclosure is assumed as
an axiom: both remain ordinary theorem arguments.

The module also replays one nontrivial pilot rectangle near the origin.  This
checks the complete path from rational cell data through LeanCert interval
evaluation to the no-common-zero theorem before the large cover is generated.
-/

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core
open LeanCert.Engine
open PartALeanCert

/-- Kernel-reducible interval evaluation for one smooth residual.  This uses
the already certified project-specialized interval for `pi`, avoiding the
generic named-constant normalization bottleneck in closed `decide` replays. -/
def scaledResidualKernelInterval (i : Fin 2)
    (phiI thetaI : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  kernelPointEvalCore (scaledResidualExpr i)
    (angleIntervalEnv phiI thetaI) cfg.taylorDepth

/-- Soundness of the kernel-reducible residual evaluator. -/
theorem scaledResidual_mem_kernelInterval (i : Fin 2)
    (phi theta : ℝ) (phiI thetaI : IntervalRat)
    (hphi : phi ∈ phiI) (htheta : theta ∈ thetaI)
    (cfg : EvalConfig := {}) :
    (if i = 0 then scaledResidualOne phi theta
      else scaledResidualTwo phi theta) ∈
      scaledResidualKernelInterval i phiI thetaI cfg := by
  let u : Fin 2 → ℝ := ![phi, theta]
  have henv : envMem (finEnv u) (angleIntervalEnv phiI thetaI) := by
    intro n
    rcases n with (_ | _ | n)
    · simpa [u, finEnv, angleIntervalEnv] using hphi
    · simpa [u, finEnv, angleIntervalEnv] using htheta
    · change finEnv u (Nat.succ (Nat.succ n)) ∈ (default : IntervalRat)
      rw [IntervalRat.mem_default]
      simp [finEnv]
  have hcore := eval_mem_kernelPointEvalCore
    (scaledResidualExpr_supported i) (finEnv u)
    (angleIntervalEnv phiI thetaI) henv cfg.taylorDepth
  change evalFin (scaledResidualExpr i) u ∈
    scaledResidualKernelInterval i phiI thetaI cfg at hcore
  fin_cases i
  · simpa [u, scaledResidualExpr_eval_zero] using hcore
  · simpa [u, scaledResidualExpr_eval_one] using hcore

/-- A rational rectangle in the two-angle plane. -/
structure AngleCell where
  phiI : IntervalRat
  thetaI : IntervalRat

namespace AngleCell

/-- Real point membership in a rational angle cell. -/
def Contains (cell : AngleCell) (phi theta : ℝ) : Prop :=
  phi ∈ cell.phiI ∧ theta ∈ cell.thetaI

/-- Executable E03 rejection test for a complete angle cell. -/
def rejected (cell : AngleCell) (cfg : EvalConfig := {}) : Bool :=
  intervalExcludesZero
      (scaledResidualKernelInterval (0 : Fin 2) cell.phiI cell.thetaI cfg) ||
    intervalExcludesZero
      (scaledResidualKernelInterval (1 : Fin 2) cell.phiI cell.thetaI cfg)

/-- A cell accepted by the executable checker contains no common zero of the
two smooth residuals. -/
theorem no_common_zero_of_rejected
    (cell : AngleCell) (phi theta : ℝ)
    (hmem : cell.Contains phi theta)
    (cfg : EvalConfig := {})
    (hreject : cell.rejected cfg = true) :
    ¬ (scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0) := by
  have hreject' :
      intervalExcludesZero
          (scaledResidualKernelInterval
            (0 : Fin 2) cell.phiI cell.thetaI cfg) = true ∨
        intervalExcludesZero
          (scaledResidualKernelInterval
            (1 : Fin 2) cell.phiI cell.thetaI cfg) = true := by
    simpa only [rejected, Bool.or_eq_true] using hreject
  rintro ⟨hzero1, hzero2⟩
  rcases hreject' with hreject' | hreject'
  · have hmem' := scaledResidual_mem_kernelInterval (0 : Fin 2)
      phi theta cell.phiI cell.thetaI hmem.1 hmem.2 cfg
    have hnot := intervalExcludesZero_sound _ hreject'
    apply hnot
    simpa [hzero1] using hmem'
  · have hmem' := scaledResidual_mem_kernelInterval (1 : Fin 2)
      phi theta cell.phiI cell.thetaI hmem.1 hmem.2 cfg
    have hnot := intervalExcludesZero_sound _ hreject'
    apply hnot
    simpa [hzero2] using hmem'

end AngleCell

/-- A point is covered when it belongs to one cell in the supplied finite
certificate list. -/
def coveredBy (cells : List AngleCell) (phi theta : ℝ) : Prop :=
  ∃ cell ∈ cells, cell.Contains phi theta

/-- One Boolean replay checks every cell in a finite certificate list. -/
def allCellsRejected (cells : List AngleCell)
    (cfg : EvalConfig := {}) : Bool :=
  cells.all (fun cell => cell.rejected cfg)

/-- Soundness of the finite-list replay layer. -/
theorem no_common_zero_of_coveredBy_rejectedCells
    (cells : List AngleCell) (phi theta : ℝ)
    (cfg : EvalConfig := {})
    (hall : allCellsRejected cells cfg = true)
    (hcover : coveredBy cells phi theta) :
    ¬ (scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0) := by
  rcases hcover with ⟨cell, hcell, hmem⟩
  have hall' : cells.all (fun c => c.rejected cfg) = true := by
    simpa only [allCellsRejected] using hall
  have hreject : cell.rejected cfg = true :=
    (List.all_eq_true.mp hall') cell hcell
  exact cell.no_common_zero_of_rejected phi theta hmem cfg hreject

/-! ## Pilot replay -/

/-- First coordinate interval of the pilot origin rectangle. -/
def originPhiInterval : IntervalRat :=
  ⟨0, 1 / 20, by norm_num⟩

/-- Second coordinate interval of the pilot origin rectangle. -/
def originThetaInterval : IntervalRat :=
  ⟨0, 1 / 20, by norm_num⟩

/-- A nontrivial `1/20 × 1/20` rectangle at the origin. -/
def originCell : AngleCell :=
  ⟨originPhiInterval, originThetaInterval⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 120000000 in
/-- Kernel reduction confirms that the second smooth residual stays strictly
away from zero on the complete pilot rectangle. -/
theorem originCell_rejected : originCell.rejected = true := by
  decide +kernel

/-- Singleton pilot certificate, written without comma-list parser syntax. -/
def originPilotCells : List AngleCell :=
  originCell :: []

/-- The finite-list checker replays the pilot certificate. -/
theorem originPilotCells_all_rejected :
    allCellsRejected originPilotCells = true := by
  simp [originPilotCells, allCellsRejected, originCell_rejected]

/-- Semantic consequence of the pilot certificate. -/
theorem originCell_no_common_zero (phi theta : ℝ)
    (hmem : originCell.Contains phi theta) :
    ¬ (scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0) := by
  exact AngleCell.no_common_zero_of_rejected
    originCell phi theta hmem (cfg := {}) originCell_rejected

/-! ## Exact local angle target and terminal composition -/

/-- Exact `phi` projection of the already certified reduced box. -/
def reducedPhiInterval : IntervalRat :=
  ⟨122429264969 / 3125000000000,
    3917736479009 / 100000000000000, by norm_num⟩

/-- Exact `theta` projection of the already certified reduced box. -/
def reducedThetaInterval : IntervalRat :=
  ⟨2129067216821 / 3125000000000,
    68130150938273 / 100000000000000, by norm_num⟩

/-- Exact angle projection of `Reduced.box`. -/
def reducedAngleCell : AngleCell :=
  ⟨reducedPhiInterval, reducedThetaInterval⟩

/-- Concrete finite-cover obligation for the next data package.  Every point
of the physical angle triangle outside the certified local angle cell must be
contained in a replayed rejection cell. -/
def FiniteRejectionCoverTarget (cells : List AngleCell)
    (cfg : EvalConfig := {}) : Prop :=
  allCellsRejected cells cfg = true ∧
    ∀ phi theta : ℝ,
      PhysicalAngleDomain phi theta →
      ¬ reducedAngleCell.Contains phi theta →
      coveredBy cells phi theta

/-- A finite rejection cover forces every smooth two-angle solution into the
exact angle projection of the certified reduced box. -/
theorem reducedAngleCell_contains_of_finiteRejectionCover
    (cells : List AngleCell) (cfg : EvalConfig)
    (hcover : FiniteRejectionCoverTarget cells cfg)
    {phi theta : ℝ} (hspec : ScaledTwoAngleSpec phi theta) :
    reducedAngleCell.Contains phi theta := by
  rcases hspec with ⟨hdom, _hden, _hA, _hB, hzero1, hzero2⟩
  by_contra houtside
  have hcovered : coveredBy cells phi theta :=
    hcover.2 phi theta hdom houtside
  have hnozero := no_common_zero_of_coveredBy_rejectedCells
    cells phi theta cfg hcover.1 hcovered
  exact hnozero ⟨hzero1, hzero2⟩

/-- Local obligation left after the finite exclusion data: a smooth solution
whose angles lie in the exact local angle cell reconstructs into the complete
four-coordinate reduced box. -/
def LocalReconstructionEnclosureTarget : Prop :=
  ∀ phi theta : ℝ,
    ScaledTwoAngleSpec phi theta →
    reducedAngleCell.Contains phi theta →
    reconstructedParams phi theta ∈ Reduced.box

/-- Finite global exclusion plus local reconstruction proves the smooth
two-angle enclosure target. -/
theorem scaledResidualEnclosureTarget_of_finiteCover_and_local
    (cells : List AngleCell) (cfg : EvalConfig)
    (hcover : FiniteRejectionCoverTarget cells cfg)
    (hlocal : LocalReconstructionEnclosureTarget) :
    ScaledResidualEnclosureTarget := by
  intro phi theta hspec
  exact hlocal phi theta hspec
    (reducedAngleCell_contains_of_finiteRejectionCover
      cells cfg hcover hspec)

/-- Exact composition into E02's remaining theorem. -/
theorem twoAngleEnclosureTarget_of_finiteCover_and_local
    (cells : List AngleCell) (cfg : EvalConfig)
    (hcover : FiniteRejectionCoverTarget cells cfg)
    (hlocal : LocalReconstructionEnclosureTarget) :
    TwoAngleEnclosureTarget :=
  (scaledResidualEnclosureTarget_iff_twoAngleEnclosureTarget).1
    (scaledResidualEnclosureTarget_of_finiteCover_and_local
      cells cfg hcover hlocal)

/-- Terminal DeepMind-shaped uniqueness theorem from the two explicit E04 data
obligations. -/
theorem deepMindABPhiTheta_existsUnique_of_finiteCover_and_local
    (cells : List AngleCell) (cfg : EvalConfig)
    (hcover : FiniteRejectionCoverTarget cells cfg)
    (hlocal : LocalReconstructionEnclosureTarget) :
    ∃! ABphiTheta : ℝ × ℝ × ℝ × ℝ,
      DeepMindABPhiThetaSpec
        ABphiTheta.1 ABphiTheta.2.1 ABphiTheta.2.2.1 ABphiTheta.2.2.2 :=
  deepMindABPhiTheta_existsUnique_of_twoAngleEnclosure
    (twoAngleEnclosureTarget_of_finiteCover_and_local
      cells cfg hcover hlocal)

end PartE
end GerverSofa
