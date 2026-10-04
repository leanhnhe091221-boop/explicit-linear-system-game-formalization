module

public import ThomGame.Groups.SolutionInvolution
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

/-!
# Three-variable solution groups need only the triangular relations

For three involutions a,b,c, a central involution q and abc=q, every pair
among a,b,c commutes. Consequently our actual three-column solution groups
have an equivalent involution presentation with exactly one triangular word
per row and no additional commutator words. This is the presentation used
to give every internal vertex of a solution-group picture degree three.
-/

@[expose] public section
namespace ThomGame.SolutionGroup

variable {G : Type*} [Group G]

theorem commute_of_triple (a b c q : G) (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hq : q * q = 1) (hqc : Commute q c)
    (h : a * b * c = q) : Commute a b := by
  have hab : a * b = q * c := by
    calc
      a * b = (a * b * c) * c := by rw [mul_assoc, hc, mul_one]
      _ = q * c := by rw [h]
  apply (four_product_eq_one_iff a b ha hb).mp
  calc
    a * b * a * b = (a * b) * (a * b) := by rw [mul_assoc]
    _ = (q * c) * (q * c) := by rw [hab]
    _ = (q * q) * (c * c) := hqc.symm.mul_mul_mul_comm q c
    _ = 1 := by rw [hq, hc, one_mul]

theorem rotate_triple (a b c q : G) (hqa : Commute q a)
    (h : a * b * c = q) : b * c * a = q := by
  calc
    b * c * a = a⁻¹ * (a * b * c) * a := by group
    _ = a⁻¹ * q * a := by rw [h]
    _ = q := by rw [mul_assoc, hqa.eq, inv_mul_cancel_left]

theorem triple_commutes (v : Fin 3 → G) (q : G)
    (hv : ∀ i, v i * v i = 1) (hq : q * q = 1)
    (hqv : ∀ i, Commute q (v i)) (h : v 0 * v 1 * v 2 = q) :
    ∀ i j, Commute (v i) (v j) := by
  have h01 := commute_of_triple (v 0) (v 1) (v 2) q (hv 0) (hv 1) (hv 2) hq (hqv 2) h
  have hrot := rotate_triple (v 0) (v 1) (v 2) q (hqv 0) h
  have h12 := commute_of_triple (v 1) (v 2) (v 0) q (hv 1) (hv 2) (hv 0) hq (hqv 0) hrot
  have hrot' := rotate_triple (v 1) (v 2) (v 0) q (hqv 1) hrot
  have h20 := commute_of_triple (v 2) (v 0) (v 1) q (hv 2) (hv 0) (hv 1) hq (hqv 1) hrot'
  intro i j
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact h01
    | exact h01.symm
    | exact h12
    | exact h12.symm
    | exact h20
    | exact h20.symm
    | exact Commute.refl _

variable {R C : Type*}

/-- All orderings of a row give the same relation, as required for arbitrary
cyclic orders at picture vertices. -/
theorem Model.row_word_product {S : SparseSystem R C} (M : Model S G)
    (r : R) (w : List C)
    (hw : w.Perm [S.column r 0, S.column r 1, S.column r 2]) :
    (w.map M.x).prod = if S.rhs r = 1 then M.j else 1 := by
  have hc : ([S.column r 0, S.column r 1, S.column r 2].map M.x).Pairwise Commute := by
    simp [M.row_commutes]
  have he := (hw.symm.map M.x).prod_eq' hc
  calc
    (w.map M.x).prod = ([S.column r 0, S.column r 1, S.column r 2].map M.x).prod := he.symm
    _ = if S.rhs r = 1 then M.j else 1 := by
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        mul_assoc] using M.row_product r

def triangularPresentation (S : SparseSystem R C) : InvolutionPresentation R C where
  word r := [S.column r 0, S.column r 1, S.column r 2]
  parity := S.rhs

def triangularModel (S : SparseSystem R C) :
    InvolutionPresentation.Model (triangularPresentation S) (GroupOf S) where
  j := J S
  x := x S
  j_square := J_sq S
  x_square := x_sq S
  j_commutes := J_commutes_x S
  word_product r := by
    change [x S (S.column r 0), x S (S.column r 1), x S (S.column r 2)].prod =
      if S.rhs r = 1 then J S else 1
    simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using row_product S r

def ofTriangle (S : SparseSystem R C) :
    InvolutionPresentation.GroupOf (triangularPresentation S) →* GroupOf S :=
  (triangularModel S).toHom

theorem ofTriangle_J (S : SparseSystem R C) :
    ofTriangle S (InvolutionPresentation.J (triangularPresentation S)) = J S :=
  (triangularModel S).toHom_J

theorem ofTriangle_x (S : SparseSystem R C) (c : C) :
    ofTriangle S (InvolutionPresentation.x (triangularPresentation S) c) = x S c :=
  (triangularModel S).toHom_x c

theorem triangular_row_product (S : SparseSystem R C) (r : R) :
    InvolutionPresentation.x (triangularPresentation S) (S.column r 0) *
      InvolutionPresentation.x (triangularPresentation S) (S.column r 1) *
      InvolutionPresentation.x (triangularPresentation S) (S.column r 2) =
        if S.rhs r = 1 then InvolutionPresentation.J (triangularPresentation S) else 1 := by
  have h := InvolutionPresentation.word_product (triangularPresentation S) r
  change [InvolutionPresentation.x (triangularPresentation S) (S.column r 0),
    InvolutionPresentation.x (triangularPresentation S) (S.column r 1),
    InvolutionPresentation.x (triangularPresentation S) (S.column r 2)].prod =
      (if S.rhs r = 1 then InvolutionPresentation.J (triangularPresentation S) else 1) at h
  simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h

def modelInTriangle (S : SparseSystem R C) :
    Model S (InvolutionPresentation.GroupOf (triangularPresentation S)) where
  j := InvolutionPresentation.J (triangularPresentation S)
  x := InvolutionPresentation.x (triangularPresentation S)
  j_square := InvolutionPresentation.J_sq _
  x_square := InvolutionPresentation.x_sq _
  j_commutes := InvolutionPresentation.J_commutes_x _
  row_commutes r := by
    apply triple_commutes (fun i => InvolutionPresentation.x (triangularPresentation S) (S.column r i))
      (if S.rhs r = 1 then InvolutionPresentation.J (triangularPresentation S) else 1)
    · intro i; exact InvolutionPresentation.x_sq _ _
    · split_ifs
      · exact InvolutionPresentation.J_sq _
      · exact one_mul 1
    · intro i
      split_ifs
      · exact InvolutionPresentation.J_commutes_x _ _
      · exact Commute.one_left _
    · exact triangular_row_product S r
  row_product := triangular_row_product S

def toTriangle (S : SparseSystem R C) :
    GroupOf S →* InvolutionPresentation.GroupOf (triangularPresentation S) :=
  (modelInTriangle S).toHom

theorem toTriangle_J (S : SparseSystem R C) :
    toTriangle S (J S) = InvolutionPresentation.J (triangularPresentation S) :=
  (modelInTriangle S).toHom_J

theorem toTriangle_x (S : SparseSystem R C) (c : C) :
    toTriangle S (x S c) = InvolutionPresentation.x (triangularPresentation S) c :=
  (modelInTriangle S).toHom_x c

theorem ofTriangle_comp_toTriangle (S : SparseSystem R C) :
    (ofTriangle S).comp (toTriangle S) = MonoidHom.id (GroupOf S) := by
  apply hom_ext
  · change ofTriangle S (toTriangle S (J S)) = J S
    rw [toTriangle_J, ofTriangle_J]
  · intro c
    change ofTriangle S (toTriangle S (x S c)) = x S c
    rw [toTriangle_x, ofTriangle_x]

theorem toTriangle_comp_ofTriangle (S : SparseSystem R C) :
    (toTriangle S).comp (ofTriangle S) =
      MonoidHom.id (InvolutionPresentation.GroupOf (triangularPresentation S)) := by
  apply InvolutionPresentation.hom_ext
  · change toTriangle S (ofTriangle S (InvolutionPresentation.J _)) = _
    rw [ofTriangle_J, toTriangle_J]
    rfl
  · intro c
    change toTriangle S (ofTriangle S (InvolutionPresentation.x _ c)) = _
    rw [ofTriangle_x, toTriangle_x]
    rfl

def triangularEquiv (S : SparseSystem R C) :
    GroupOf S ≃* InvolutionPresentation.GroupOf (triangularPresentation S) where
  toFun := toTriangle S
  invFun := ofTriangle S
  left_inv := DFunLike.congr_fun (ofTriangle_comp_toTriangle S)
  right_inv := DFunLike.congr_fun (toTriangle_comp_ofTriangle S)
  map_mul' := (toTriangle S).map_mul

theorem triangularEquiv_J (S : SparseSystem R C) :
    triangularEquiv S (J S) = InvolutionPresentation.J (triangularPresentation S) :=
  toTriangle_J S

theorem triangularEquiv_x (S : SparseSystem R C) (c : C) :
    triangularEquiv S (x S c) = InvolutionPresentation.x (triangularPresentation S) c :=
  toTriangle_x S c

end ThomGame.SolutionGroup
