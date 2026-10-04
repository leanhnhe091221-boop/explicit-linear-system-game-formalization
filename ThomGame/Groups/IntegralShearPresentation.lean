module

public import ThomGame.Groups.PrimeFiveRankThreeCover

/-!
# The six-generator integral shear presentation

This is precisely (SL1)--(SL3) of the paper: separated roots commute,
adjacent roots have the prescribed commutator, and the standard Weyl
word has fourth power one. Identification of this presented group with
SL₃(ℤ), and its property (T), are separate unproved inputs.
-/

@[expose] public section
namespace ThomGame.IntegralShear

open Compressor

inductive Relation
  | separated (p : {p : Root × Root // Compressor.separated p.1 p.2})
  | adjacent (r : Root)
  | torsion
  deriving DecidableEq, Fintype

def relator : Relation → FreeGroup Root
  | .separated p => PrimeFiveRankThreeCover.comm (FreeGroup.of p.val.1) (FreeGroup.of p.val.2)
  | .adjacent r =>
      PrimeFiveRankThreeCover.comm (FreeGroup.of r) (FreeGroup.of (right r)) * (FreeGroup.of (across r))⁻¹
  | .torsion => (FreeGroup.of root12 * (FreeGroup.of (reverse root12))⁻¹ * FreeGroup.of root12) ^ 4

def relators : Set (FreeGroup Root) := Set.range relator

def ShearGroup := PresentedGroup relators
  deriving Group

def of (r : Root) : ShearGroup := PresentedGroup.of r

theorem relation_card : Fintype.card Relation = 25 := by decide +kernel

theorem relators_finite : relators.Finite := Set.finite_range _

instance : Group.IsFinitelyPresented ShearGroup := by
  let : Finite relators := relators_finite.to_subtype
  exact inferInstanceAs (Group.IsFinitelyPresented (PresentedGroup relators))

structure Model (G : Type*) [Group G] where
  x : Root → G
  separated : ∀ r s, Compressor.separated r s → PrimeFiveRankThreeCover.comm (x r) (x s) = 1
  adjacent : ∀ r, PrimeFiveRankThreeCover.comm (x r) (x (right r)) = x (across r)
  torsion : (x root12 * (x (reverse root12))⁻¹ * x root12) ^ 4 = 1

namespace Model

variable {G : Type*} [Group G] (M : Model G)

theorem eval_relator (r : Relation) : FreeGroup.lift M.x (relator r) = 1 := by
  cases r with
  | separated p => simpa [relator, PrimeFiveRankThreeCover.comm] using M.separated p.val.1 p.val.2 p.property
  | adjacent r => simpa [relator, PrimeFiveRankThreeCover.comm, ← mul_inv_eq_one] using M.adjacent r
  | torsion => simpa [relator] using M.torsion

def toHom : ShearGroup →* G := PresentedGroup.toGroup (f := M.x) (fun _ hr => by
  obtain ⟨r, rfl⟩ := hr
  exact M.eval_relator r)

@[simp] theorem toHom_of (r : Root) : M.toHom (of r) = M.x r := PresentedGroup.toGroup.of _

end Model
end ThomGame.IntegralShear
