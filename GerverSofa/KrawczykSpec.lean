import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Specification boundary for interval/Krawczyk certification

The records below make the logical target explicit.  A completed numerical
formalisation must construct these records from exact interval operations,
Taylor bounds for `sin`/`cos`, a certified interval Jacobian and the general
Krawczyk theorem.  No global axiom is introduced here.
-/

namespace GerverSofa

/-- A unique solution of a predicate inside an explicit set. -/
structure CertifiedUniqueSolution {α : Type*} (P : α → Prop) (X : Set α) where
  solution : α
  solution_mem : solution ∈ X
  satisfies : P solution
  unique : ∀ y, y ∈ X → P y → y = solution

theorem CertifiedUniqueSolution.toExistsUnique
    {α : Type*} {P : α → Prop} {X : Set α}
    (c : CertifiedUniqueSolution P X) :
    ∃! x, x ∈ X ∧ P x := by
  refine ⟨c.solution, ⟨c.solution_mem, c.satisfies⟩, ?_⟩
  intro y hy
  exact c.unique y hy.1 hy.2

abbrev Vec (n : Nat) := Fin n → ℝ

/-- A unique zero of a vector-valued function in a set. -/
def CertifiedUniqueZero {n : Nat} (F : Vec n → Vec n) (X : Set (Vec n)) :=
  CertifiedUniqueSolution (fun x => F x = 0) X

/-- Abstract mathematical content of a strict Krawczyk certificate. -/
structure StrictKrawczykCertificate {n : Nat}
    (F : Vec n → Vec n) (X : Set (Vec n)) where
  preconditioner : Matrix (Fin n) (Fin n) ℝ
  preconditioner_invertible : IsUnit preconditioner.det
  image : Set (Vec n)
  image_strictly_inside : image ⊆ interior X
  soundness_statement : Prop
  interval_extension_sound : soundness_statement
  yields_unique_zero : CertifiedUniqueZero F X

end GerverSofa
