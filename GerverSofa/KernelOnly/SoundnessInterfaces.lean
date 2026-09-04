import GerverSofa.ExactReplay
import GerverSofa.CertificateManifest
import GerverSofa.KernelOnly.Coordinates
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Semantic interfaces for the executable interval certificate

These definitions state, without hiding any mathematical assumption, the
bridges that turn the frozen rational replay into facts about `Real.sin`,
`Real.cos`, the two real systems, and their Jacobians.  Concrete proof terms
for these interfaces are the remaining analytic part of the end-to-end
certificate; no axiom is declared here.
-/

noncomputable section

namespace GerverSofa

open RatInterval

/-- A rational interval list encloses a finite real vector coordinatewise. -/
def EnclosesVec {n : Nat} (box : List RatInterval) (x : Vec n) : Prop :=
  box.length = n ∧
    ∀ i : Fin n, Contains (box.getD i.1 (point 0)) (x i)

/-- A list of interval rows encloses a real matrix coordinatewise. -/
def EnclosesMatrix {n : Nat}
    (box : List (List RatInterval)) (J : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  box.length = n ∧
    ∀ i j : Fin n,
      Contains ((box.getD i.1 []).getD j.1 (point 0)) (J i j)

/-- Read the interval derivative rows returned by the first-order AD object. -/
def derivativeRows (out : List ExactReplay.D) : List (List RatInterval) :=
  out.map ExactReplay.D.der

/-- Read the value intervals returned by the first-order AD object. -/
def valueIntervals (out : List ExactReplay.D) : List RatInterval :=
  out.map ExactReplay.D.val

/-- A one-dimensional real derivative certificate in the classical
difference-quotient form.  This is the exact real specialization of the
right-hand side of Mathlib's `hasDerivAt_iff_tendsto_slope_zero`: it states
that `(f (x+t)-f x)/t` tends to `f'` as `t → 0`, `t ≠ 0`.

Unlike storing raw `HasDerivAt`/`DifferentiableAt`, this proposition contains
no hidden `AddCommGroup`/`Module` instance path for the codomain `ℝ`; this
removes the instance diamond exposed by Lean 4.33 while retaining the full
mathematical meaning of an actual derivative. -/
def RealDerivativeAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  Filter.Tendsto
    (fun t : ℝ => t⁻¹ * (f (x + t) - f x))
    (nhdsWithin 0 (({0} : Set ℝ)ᶜ))
    (nhds f')

/-- Semantic meaning of a pointwise Jacobian, phrased through all coordinate
partial derivatives.  Each entry is an actual derivative in the classical
difference-quotient sense encoded by `RealDerivativeAt`. -/
def IsJacobianAt {n : Nat}
    (F : Vec n → Vec n) (x : Vec n)
    (J : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n,
    RealDerivativeAt (fun t : ℝ => F (Function.update x j t) i) (J i j) (x j)

/-- The output of an interval-AD evaluation encloses both the value and one
actual Jacobian of the real system. -/
def ADOutputSoundAt {n : Nat}
    (F : Vec n → Vec n) (x : Vec n)
    (out : List ExactReplay.D) : Prop :=
  ∃ J : Matrix (Fin n) (Fin n) ℝ,
    IsJacobianAt F x J ∧
    EnclosesVec (valueIntervals out) (F x) ∧
    EnclosesMatrix (derivativeRows out) J

/-- Exact analytic correctness required from the executable trigonometric
layer.  The domain is the physical range used by the Gerver certificate. -/
structure TranscendentalSoundness : Prop where
  pi_mem : Contains ExactReplay.declaredPiInterval Real.pi
  sine_mem : ∀ (z : RatInterval) (x : ℝ),
    Contains z x → 0 ≤ x → x ≤ Real.pi / 2 →
      Contains (ExactReplay.sineInterval z) (Real.sin x)
  cosine_mem : ∀ (z : RatInterval) (x : ℝ),
    Contains z x → 0 ≤ x → x ≤ Real.pi / 2 →
      Contains (ExactReplay.cosineInterval z) (Real.cos x)

/-- Semantic correctness of one frozen interval-AD evaluation. -/
structure ADSystemSoundness {n : Nat}
    (F : Vec n → Vec n) (X : Set (Vec n))
    (input : List RatInterval)
    (eval : List RatInterval → List ExactReplay.D) : Prop where
  input_exact : ∀ x, x ∈ X ↔ EnclosesVec input x
  output_sound : ∀ x ∈ X, ADOutputSoundAt F x (eval input)

/-- The exact semantic bridge for both systems used by the manuscript. -/
structure GerverNumericalSoundness : Prop where
  transcendentals : TranscendentalSoundness
  reduced_ad : ADSystemSoundness
    Reduced.vectorSystem Reduced.vectorBox
    ExactReplay.reducedInputBox ExactReplay.reducedIntervalSystem
  full_ad : ADSystemSoundness
    Romik.vectorSystem Romik.vectorBox
    ExactReplay.fullInputBox ExactReplay.fullIntervalSystem

/-- Kernel-only rational replay is already a theorem checked by
`decide +kernel`. -/
theorem kernelReplayPass : ExactReplay.ReplayPass :=
  ExactReplay.replayChecks_eq_true

/-- The published rational manifest is likewise checked by kernel reduction. -/
theorem kernelManifestPass : CertificateManifest.ManifestPass :=
  CertificateManifest.allChecks_eq_true

end GerverSofa
