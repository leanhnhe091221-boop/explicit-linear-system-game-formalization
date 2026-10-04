module

public import ThomGame.Finite.SparseSystem
public import ThomGame.Finite.PresentedWords
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.DeriveFintype

/-!
# The solution group of a binary sparse system

There is a central involution J and one involution per column. Variables in
the same row commute, and their product equals J to the right-hand-side bit.
No nontriviality of J is assumed or asserted here.
-/

@[expose] public section
namespace ThomGame.SolutionGroup

variable {R C : Type*}

inductive RelationTag (R C : Type*)
  | centralSquare
  | variableSquare (c : C)
  | centralCommutes (c : C)
  | rowCommutes (r : R) (i j : Fin 3)
  | rowEquation (r : R)
  deriving DecidableEq, Fintype

abbrev Generator (C : Type*) := Option C

def centralWord : Word (Generator C) := Word.generator none

def variableWord (c : C) : Word (Generator C) := Word.generator (some c)

def rowWord (S : SparseSystem R C) (r : R) : Word (Generator C) :=
  variableWord (S.column r 0) ++ variableWord (S.column r 1) ++ variableWord (S.column r 2)

def rhsWord (S : SparseSystem R C) (r : R) : Word (Generator C) :=
  if S.rhs r = 1 then centralWord else []

def relatorWord (S : SparseSystem R C) : RelationTag R C → Word (Generator C)
  | .centralSquare => centralWord ++ centralWord
  | .variableSquare c => variableWord c ++ variableWord c
  | .centralCommutes c => Word.commutator centralWord (variableWord c)
  | .rowCommutes r i j => Word.commutator (variableWord (S.column r i)) (variableWord (S.column r j))
  | .rowEquation r => Word.equation (rowWord S r) (rhsWord S r)

def relators (S : SparseSystem R C) : Set (FreeGroup (Generator C)) :=
  Set.range (fun tag => FreeGroup.mk (relatorWord S tag))

abbrev GroupOf (S : SparseSystem R C) := PresentedGroup (relators S)

def J (S : SparseSystem R C) : GroupOf S := PresentedGroup.of none

def x (S : SparseSystem R C) (c : C) : GroupOf S := PresentedGroup.of (some c)

theorem eval_relation (S : SparseSystem R C) (tag : RelationTag R C) :
    Word.eval (PresentedGroup.of (rels := relators S)) (relatorWord S tag) = 1 := by
  rw [Word.eval_presented]
  exact PresentedGroup.one_of_mem ⟨tag, rfl⟩

theorem J_sq (S : SparseSystem R C) : J S * J S = 1 := by
  simpa [relatorWord, centralWord, J] using eval_relation S .centralSquare

theorem x_sq (S : SparseSystem R C) (c : C) : x S c * x S c = 1 := by
  simpa [relatorWord, variableWord, x] using eval_relation S (.variableSquare c)

private theorem commutator_eq_one_iff {α G : Type*} [Group G] (f : α → G) (u v : Word α) :
    Word.eval f (Word.commutator u v) = 1 ↔ Commute (Word.eval f u) (Word.eval f v) := by
  rw [Word.eval_commutator, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  rfl

theorem J_commutes_x (S : SparseSystem R C) (c : C) : Commute (J S) (x S c) := by
  have h := eval_relation S (.centralCommutes c)
  rw [relatorWord, commutator_eq_one_iff] at h
  simpa [centralWord, variableWord, J, x] using h

theorem row_commutes (S : SparseSystem R C) (r : R) (i j : Fin 3) :
    Commute (x S (S.column r i)) (x S (S.column r j)) := by
  have h := eval_relation S (.rowCommutes r i j)
  rw [relatorWord, commutator_eq_one_iff] at h
  simpa [variableWord, x] using h

theorem row_product (S : SparseSystem R C) (r : R) :
    x S (S.column r 0) * x S (S.column r 1) * x S (S.column r 2) =
      if S.rhs r = 1 then J S else 1 := by
  have h := eval_relation S (.rowEquation r)
  rw [relatorWord, Word.eval_equation_eq_one_iff] at h
  by_cases hb : S.rhs r = 1 <;>
    simpa [rowWord, rhsWord, centralWord, variableWord, J, x, hb, mul_assoc] using h

/-- Centrality holds for every group element, not only the named generators. -/
theorem J_commutes (S : SparseSystem R C) (g : GroupOf S) : Commute (J S) g := by
  have hgen : ∀ a : Generator C, PresentedGroup.of (rels := relators S) a ∈
      Subgroup.centralizer ({J S} : Set (GroupOf S)) := by
    intro a
    rw [Subgroup.mem_centralizer_singleton_iff]
    cases a with
    | none => rfl
    | some c => exact (J_commutes_x S c).eq.symm
  have h := PresentedGroup.generated_by (relators S)
    (Subgroup.centralizer ({J S} : Set (GroupOf S))) hgen g
  exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm

theorem relators_finite [Fintype R] [Fintype C] (S : SparseSystem R C) :
    (relators S).Finite := Set.finite_range _

/-- Actual elements of a target group satisfying the solution-group relations. -/
structure Model (S : SparseSystem R C) (G : Type*) [Group G] where
  j : G
  x : C → G
  j_square : j * j = 1
  x_square : ∀ c, x c * x c = 1
  j_commutes : ∀ c, Commute j (x c)
  row_commutes : ∀ r i k, Commute (x (S.column r i)) (x (S.column r k))
  row_product : ∀ r, x (S.column r 0) * x (S.column r 1) * x (S.column r 2) =
    if S.rhs r = 1 then j else 1

namespace Model

variable {S : SparseSystem R C} {G : Type*} [Group G] (M : Model S G)

def assignment : Generator C → G
  | none => M.j
  | some c => M.x c

theorem eval_relator (tag : RelationTag R C) :
    Word.eval M.assignment (relatorWord S tag) = 1 := by
  cases tag with
  | centralSquare =>
    simpa [relatorWord, centralWord, assignment] using M.j_square
  | variableSquare c =>
    simpa [relatorWord, variableWord, assignment] using M.x_square c
  | centralCommutes c =>
    rw [relatorWord, commutator_eq_one_iff]
    simpa [centralWord, variableWord, assignment] using M.j_commutes c
  | rowCommutes r i k =>
    rw [relatorWord, commutator_eq_one_iff]
    simpa [variableWord, assignment] using M.row_commutes r i k
  | rowEquation r =>
    rw [relatorWord, Word.eval_equation_eq_one_iff]
    by_cases hb : S.rhs r = 1 <;>
      simpa [rowWord, rhsWord, centralWord, variableWord, assignment, hb, mul_assoc]
        using M.row_product r

/-- The homomorphism induced by a genuine assignment satisfying the relations. -/
def toHom : GroupOf S →* G :=
  PresentedGroup.toGroup (f := M.assignment) (rels := relators S) (by
    rintro _ ⟨tag, rfl⟩
    exact M.eval_relator tag)

theorem toHom_J : M.toHom (J S) = M.j := by
  simp [toHom, J, assignment]

theorem toHom_x (c : C) : M.toHom (SolutionGroup.x S c) = M.x c := by
  simp [toHom, SolutionGroup.x, assignment]

end Model

theorem hom_ext {S : SparseSystem R C} {G : Type*} [Group G]
    {φ ψ : GroupOf S →* G} (hJ : φ (J S) = ψ (J S))
    (hx : ∀ c, φ (x S c) = ψ (x S c)) : φ = ψ := by
  apply PresentedGroup.ext
  intro a
  cases a with
  | none => exact hJ
  | some c => exact hx c

theorem Model.toHom_unique {S : SparseSystem R C} {G : Type*} [Group G]
    (M : Model S G) (φ : GroupOf S →* G)
    (hJ : φ (J S) = M.j) (hx : ∀ c, φ (SolutionGroup.x S c) = M.x c) : φ = M.toHom := by
  apply hom_ext
  · exact hJ.trans M.toHom_J.symm
  · intro c
    exact (hx c).trans (M.toHom_x c).symm

/-- The canonical generators themselves provide the universal model. -/
def canonicalModel (S : SparseSystem R C) : Model S (GroupOf S) where
  j := J S
  x := x S
  j_square := J_sq S
  x_square := x_sq S
  j_commutes := J_commutes_x S
  row_commutes := row_commutes S
  row_product := row_product S


end ThomGame.SolutionGroup
