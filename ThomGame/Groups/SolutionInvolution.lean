module

public import ThomGame.Groups.SolutionGroup
public import ThomGame.Groups.InvolutionPresentation

/-!
# Solution groups as involution presentations

The unsigned relation [a,b,a,b] is exactly commutation for involutions.
This identifies the actual solution-group presentation, including all row
commutators and the distinguished J, with an involution presentation.
-/

@[expose] public section
namespace ThomGame.SolutionGroup

variable {R C : Type*}

theorem four_product_eq_one_iff {G : Type*} [Group G] (a b : G)
    (ha : a * a = 1) (hb : b * b = 1) : a * b * a * b = 1 ↔ Commute a b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  constructor
  · intro h
    have hh : (a * b) * (a * b) = 1 := by simpa only [mul_assoc] using h
    have he := eq_inv_of_mul_eq_one_left hh
    change a * b = b * a
    simpa only [mul_inv_rev, hai, hbi] using he
  · intro h
    calc
      a * b * a * b = (a * a) * (b * b) := by
        rw [mul_assoc, h.symm.mul_mul_mul_comm, ← mul_assoc]
      _ = 1 := by rw [ha, hb, one_mul]

inductive InvolutionRelation (R : Type*)
  | commutes (r : R) (i j : Fin 3)
  | equation (r : R)
  deriving DecidableEq, Fintype

def involutionPresentation (S : SparseSystem R C) :
    InvolutionPresentation (InvolutionRelation R) C where
  word
    | .commutes r i j => [S.column r i, S.column r j, S.column r i, S.column r j]
    | .equation r => [S.column r 0, S.column r 1, S.column r 2]
  parity
    | .commutes _ _ _ => 0
    | .equation r => S.rhs r

def involutionModel (S : SparseSystem R C) :
    InvolutionPresentation.Model (involutionPresentation S) (GroupOf S) where
  j := J S
  x := x S
  j_square := J_sq S
  x_square := x_sq S
  j_commutes := J_commutes_x S
  word_product t := by
    cases t with
    | commutes r i j =>
      change [x S (S.column r i), x S (S.column r j),
        x S (S.column r i), x S (S.column r j)].prod = 1
      have h := (four_product_eq_one_iff _ _ (x_sq S _) (x_sq S _)).mpr
        (row_commutes S r i j)
      simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h
    | equation r =>
      change [x S (S.column r 0), x S (S.column r 1), x S (S.column r 2)].prod =
        if S.rhs r = 1 then J S else 1
      simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using row_product S r

def ofInvolution (S : SparseSystem R C) :
    InvolutionPresentation.GroupOf (involutionPresentation S) →* GroupOf S :=
  (involutionModel S).toHom

theorem ofInvolution_J (S : SparseSystem R C) :
    ofInvolution S (InvolutionPresentation.J (involutionPresentation S)) = J S :=
  (involutionModel S).toHom_J

theorem ofInvolution_x (S : SparseSystem R C) (c : C) :
    ofInvolution S (InvolutionPresentation.x (involutionPresentation S) c) = x S c :=
  (involutionModel S).toHom_x c

def modelInInvolution (S : SparseSystem R C) :
    Model S (InvolutionPresentation.GroupOf (involutionPresentation S)) where
  j := InvolutionPresentation.J (involutionPresentation S)
  x := InvolutionPresentation.x (involutionPresentation S)
  j_square := InvolutionPresentation.J_sq _
  x_square := InvolutionPresentation.x_sq _
  j_commutes := InvolutionPresentation.J_commutes_x _
  row_commutes r i j := by
    apply (four_product_eq_one_iff _ _ (InvolutionPresentation.x_sq _ _)
      (InvolutionPresentation.x_sq _ _)).mp
    have h := InvolutionPresentation.word_product (involutionPresentation S) (.commutes r i j)
    change [InvolutionPresentation.x (involutionPresentation S) (S.column r i),
      InvolutionPresentation.x (involutionPresentation S) (S.column r j),
      InvolutionPresentation.x (involutionPresentation S) (S.column r i),
      InvolutionPresentation.x (involutionPresentation S) (S.column r j)].prod = 1 at h
    simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h
  row_product r := by
    have h := InvolutionPresentation.word_product (involutionPresentation S) (.equation r)
    change [InvolutionPresentation.x (involutionPresentation S) (S.column r 0),
      InvolutionPresentation.x (involutionPresentation S) (S.column r 1),
      InvolutionPresentation.x (involutionPresentation S) (S.column r 2)].prod =
        (if S.rhs r = 1 then InvolutionPresentation.J (involutionPresentation S) else 1) at h
    simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h

def toInvolution (S : SparseSystem R C) :
    GroupOf S →* InvolutionPresentation.GroupOf (involutionPresentation S) :=
  (modelInInvolution S).toHom

theorem toInvolution_J (S : SparseSystem R C) :
    toInvolution S (J S) = InvolutionPresentation.J (involutionPresentation S) :=
  (modelInInvolution S).toHom_J

theorem toInvolution_x (S : SparseSystem R C) (c : C) :
    toInvolution S (x S c) = InvolutionPresentation.x (involutionPresentation S) c :=
  (modelInInvolution S).toHom_x c

theorem ofInvolution_comp_toInvolution (S : SparseSystem R C) :
    (ofInvolution S).comp (toInvolution S) = MonoidHom.id (GroupOf S) := by
  apply hom_ext
  · change ofInvolution S (toInvolution S (J S)) = J S
    rw [toInvolution_J, ofInvolution_J]
  · intro c
    change ofInvolution S (toInvolution S (x S c)) = x S c
    rw [toInvolution_x, ofInvolution_x]

theorem toInvolution_comp_ofInvolution (S : SparseSystem R C) :
    (toInvolution S).comp (ofInvolution S) =
      MonoidHom.id (InvolutionPresentation.GroupOf (involutionPresentation S)) := by
  apply InvolutionPresentation.hom_ext
  · change toInvolution S (ofInvolution S (InvolutionPresentation.J _)) = _
    rw [ofInvolution_J, toInvolution_J]
    rfl
  · intro c
    change toInvolution S (ofInvolution S (InvolutionPresentation.x _ c)) = _
    rw [ofInvolution_x, toInvolution_x]
    rfl

def involutionEquiv (S : SparseSystem R C) :
    GroupOf S ≃* InvolutionPresentation.GroupOf (involutionPresentation S) where
  toFun := toInvolution S
  invFun := ofInvolution S
  left_inv := DFunLike.congr_fun (ofInvolution_comp_toInvolution S)
  right_inv := DFunLike.congr_fun (toInvolution_comp_ofInvolution S)
  map_mul' := (toInvolution S).map_mul

theorem involutionEquiv_J (S : SparseSystem R C) :
    involutionEquiv S (J S) = InvolutionPresentation.J (involutionPresentation S) :=
  toInvolution_J S

theorem involutionEquiv_x (S : SparseSystem R C) (c : C) :
    involutionEquiv S (x S c) = InvolutionPresentation.x (involutionPresentation S) c :=
  toInvolution_x S c

end ThomGame.SolutionGroup
