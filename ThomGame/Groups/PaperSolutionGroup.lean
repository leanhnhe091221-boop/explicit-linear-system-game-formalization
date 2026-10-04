module

public import ThomGame.Groups.SolutionGroup

/-!
The paper's literal relator convention: [x,J] and only the three row pairs i < j.
The row-word order is supplied by S; the final construction uses S.ordered.
-/

@[expose] public section
namespace ThomGame.SolutionGroup.Paper

variable {R C : Type*}

abbrev RowPair := {p : Fin 3 × Fin 3 // p.1 < p.2}

inductive RelationTag (R C : Type*)
  | centralSquare
  | variableSquare (c : C)
  | centralCommutes (c : C)
  | rowCommutes (r : R) (p : RowPair)
  | rowEquation (r : R)
  deriving DecidableEq, Fintype

def relatorWord (S : SparseSystem R C) : RelationTag R C → Word (Generator C)
  | .centralSquare => centralWord ++ centralWord
  | .variableSquare c => variableWord c ++ variableWord c
  | .centralCommutes c => Word.commutator (variableWord c) centralWord
  | .rowCommutes r p => Word.commutator
      (variableWord (S.column r p.val.1)) (variableWord (S.column r p.val.2))
  | .rowEquation r => Word.equation (rowWord S r) (rhsWord S r)

def relators (S : SparseSystem R C) : Set (FreeGroup (Generator C)) :=
  Set.range (fun tag => FreeGroup.mk (relatorWord S tag))

abbrev GroupOf (S : SparseSystem R C) := PresentedGroup (relators S)

def J (S : SparseSystem R C) : GroupOf S := PresentedGroup.of none

def x (S : SparseSystem R C) (c : C) : GroupOf S := PresentedGroup.of (some c)

theorem relators_finite [Fintype R] [Fintype C] (S : SparseSystem R C) :
    (relators S).Finite := Set.finite_range _

theorem eval_relation (S : SparseSystem R C) (tag : RelationTag R C) :
    Word.eval (PresentedGroup.of (rels := relators S)) (relatorWord S tag) = 1 := by
  rw [Word.eval_presented]
  exact PresentedGroup.one_of_mem ⟨tag, rfl⟩

theorem eval_commutator_eq_one_iff {α G : Type*} [Group G] (f : α → G) (u v : Word α) :
    Word.eval f (Word.commutator u v) = 1 ↔ Commute (Word.eval f u) (Word.eval f v) := by
  rw [Word.eval_commutator, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  rfl

theorem J_sq (S : SparseSystem R C) : J S * J S = 1 := by
  simpa [relatorWord, centralWord, J] using eval_relation S .centralSquare

theorem x_sq (S : SparseSystem R C) (c : C) : x S c * x S c = 1 := by
  simpa [relatorWord, variableWord, x] using eval_relation S (.variableSquare c)

theorem J_commutes_x (S : SparseSystem R C) (c : C) : Commute (J S) (x S c) := by
  have h := eval_relation S (.centralCommutes c)
  rw [relatorWord, eval_commutator_eq_one_iff] at h
  simpa [centralWord, variableWord, J, x] using h.symm

theorem row_commutes_lt (S : SparseSystem R C) (r : R) (i j : Fin 3) (hij : i < j) :
    Commute (x S (S.column r i)) (x S (S.column r j)) := by
  have h := eval_relation S (.rowCommutes r ⟨(i, j), hij⟩)
  rw [relatorWord, eval_commutator_eq_one_iff] at h
  simpa [variableWord, x] using h

theorem row_commutes (S : SparseSystem R C) (r : R) (i j : Fin 3) :
    Commute (x S (S.column r i)) (x S (S.column r j)) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact row_commutes_lt S r i j h
  · exact Commute.refl _
  · exact (row_commutes_lt S r j i h).symm

theorem row_product (S : SparseSystem R C) (r : R) :
    x S (S.column r 0) * x S (S.column r 1) * x S (S.column r 2) =
      if S.rhs r = 1 then J S else 1 := by
  have h := eval_relation S (.rowEquation r)
  rw [relatorWord, Word.eval_equation_eq_one_iff] at h
  by_cases hb : S.rhs r = 1 <;>
    simpa [rowWord, rhsWord, centralWord, variableWord, J, x, hb, mul_assoc] using h

def canonicalModel (S : SparseSystem R C) : SolutionGroup.Model S (GroupOf S) where
  j := J S
  x := x S
  j_square := J_sq S
  x_square := x_sq S
  j_commutes := J_commutes_x S
  row_commutes := row_commutes S
  row_product := row_product S

theorem model_eval_relation {G : Type*} [Group G] {S : SparseSystem R C}
    (M : SolutionGroup.Model S G) (tag : RelationTag R C) :
    Word.eval M.assignment (relatorWord S tag) = 1 := by
  cases tag with
  | centralSquare => exact M.eval_relator .centralSquare
  | variableSquare c => exact M.eval_relator (.variableSquare c)
  | centralCommutes c =>
    rw [relatorWord, eval_commutator_eq_one_iff]
    simpa [variableWord, centralWord, Model.assignment] using (M.j_commutes c).symm
  | rowCommutes r p => exact M.eval_relator (.rowCommutes r p.val.1 p.val.2)
  | rowEquation r => exact M.eval_relator (.rowEquation r)

def modelToHom {G : Type*} [Group G] {S : SparseSystem R C}
    (M : SolutionGroup.Model S G) : GroupOf S →* G :=
  PresentedGroup.toGroup (f := M.assignment) (rels := relators S) (by
    rintro _ ⟨tag, rfl⟩
    exact model_eval_relation M tag)

theorem modelToHom_J {G : Type*} [Group G] {S : SparseSystem R C}
    (M : SolutionGroup.Model S G) : modelToHom M (J S) = M.j := by
  simp [modelToHom, J, Model.assignment]

theorem modelToHom_x {G : Type*} [Group G] {S : SparseSystem R C}
    (M : SolutionGroup.Model S G) (c : C) : modelToHom M (x S c) = M.x c := by
  simp [modelToHom, x, Model.assignment]

def toSolution (S : SparseSystem R C) : GroupOf S →* SolutionGroup.GroupOf S :=
  modelToHom (SolutionGroup.canonicalModel S)

def ofSolution (S : SparseSystem R C) : SolutionGroup.GroupOf S →* GroupOf S :=
  (canonicalModel S).toHom

theorem toSolution_J (S : SparseSystem R C) : toSolution S (J S) = SolutionGroup.J S :=
  modelToHom_J _

theorem toSolution_x (S : SparseSystem R C) (c : C) :
    toSolution S (x S c) = SolutionGroup.x S c := modelToHom_x _ c

theorem ofSolution_J (S : SparseSystem R C) : ofSolution S (SolutionGroup.J S) = J S :=
  Model.toHom_J _

theorem ofSolution_x (S : SparseSystem R C) (c : C) :
    ofSolution S (SolutionGroup.x S c) = x S c := Model.toHom_x _ c

theorem toSolution_comp_ofSolution (S : SparseSystem R C) :
    (toSolution S).comp (ofSolution S) = MonoidHom.id (SolutionGroup.GroupOf S) := by
  apply SolutionGroup.hom_ext
  · simp [MonoidHom.comp_apply, ofSolution_J, toSolution_J]
  · intro c
    simp [MonoidHom.comp_apply, ofSolution_x, toSolution_x]

theorem ofSolution_comp_toSolution (S : SparseSystem R C) :
    (ofSolution S).comp (toSolution S) = MonoidHom.id (GroupOf S) := by
  apply PresentedGroup.ext
  intro a
  cases a with
  | none => exact (congrArg (ofSolution S) (toSolution_J S)).trans (ofSolution_J S)
  | some c => exact (congrArg (ofSolution S) (toSolution_x S c)).trans (ofSolution_x S c)

def solutionEquiv (S : SparseSystem R C) : GroupOf S ≃* SolutionGroup.GroupOf S where
  toFun := toSolution S
  invFun := ofSolution S
  left_inv := DFunLike.congr_fun (ofSolution_comp_toSolution S)
  right_inv := DFunLike.congr_fun (toSolution_comp_ofSolution S)
  map_mul' := (toSolution S).map_mul

theorem solutionEquiv_J (S : SparseSystem R C) : solutionEquiv S (J S) = SolutionGroup.J S :=
  toSolution_J S

theorem solutionEquiv_x (S : SparseSystem R C) (c : C) :
    solutionEquiv S (x S c) = SolutionGroup.x S c := toSolution_x S c

end ThomGame.SolutionGroup.Paper
