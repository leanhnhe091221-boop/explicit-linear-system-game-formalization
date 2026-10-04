module

public import ThomGame.Groups.SolutionInvolution
public import ThomGame.Groups.InvolutionEven
public import ThomGame.Groups.CentralQuotient
public import ThomGame.Groups.CentralTwist
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Erasing the right-hand side of a solution group

The homogeneous presentation is isomorphic to (G / {1,J}) × C₂.
The fresh C₂ factor must not be confused with the J killed by the quotient.
-/

@[expose] public section
namespace ThomGame.SolutionGroup

variable {R C : Type*} (P : SparseSystem R C)

def centralDatum : CentralQuotient.Datum (GroupOf P) where
  j := J P
  square := J_sq P
  central := J_commutes P

abbrev ModJ := (centralDatum P).GroupOf

def quotientJ : GroupOf P →* (ModJ P) := (centralDatum P).projection

theorem quotientJ_eq_one_iff (g : GroupOf P) : (quotientJ P) g = 1 ↔ g = 1 ∨ g = J P :=
  (centralDatum P).projection_eq_one_iff g

theorem quotientJ_J : (quotientJ P) (J P) = 1 := (centralDatum P).projection_j

def homogeneous : SparseSystem R C := { P with rhs := fun _ => 0 }

theorem homogeneous_involutionPresentation :
    involutionPresentation (homogeneous P) = (involutionPresentation P).homogeneous := by
  unfold involutionPresentation homogeneous InvolutionPresentation.homogeneous
  congr 1
  funext t
  cases t <;> rfl

def quotientX (s : C) : (ModJ P) := (quotientJ P) (x P s)

theorem quotientX_square (s : C) : (quotientX P) s * (quotientX P) s = 1 := by
  rw [quotientX, ← map_mul, x_sq, map_one]

theorem quotientX_commutes (r : R) (i j : Fin 3) :
    Commute ((quotientX P) (P.column r i)) ((quotientX P) (P.column r j)) :=
  (row_commutes P r i j).map (quotientJ P)

theorem quotientX_row (r : R) :
    (quotientX P) (P.column r 0) * (quotientX P) (P.column r 1) * (quotientX P) (P.column r 2) = 1 := by
  change (quotientJ P) (x P (P.column r 0)) * (quotientJ P) (x P (P.column r 1)) *
    (quotientJ P) (x P (P.column r 2)) = 1
  have h := congrArg (quotientJ P) (row_product P r)
  by_cases hp : P.rhs r = 1 <;> simpa [hp, quotientJ_J] using h

def forgetParityModel : Model P (GroupOf (homogeneous P)) where
  j := 1
  x := x (homogeneous P)
  j_square := one_mul 1
  x_square := x_sq (homogeneous P)
  j_commutes := fun _ => Commute.one_left _
  row_commutes := row_commutes (homogeneous P)
  row_product r := by
    simp only [ite_self]
    exact row_product (homogeneous P) r

def forgetParity : GroupOf P →* GroupOf (homogeneous P) := (forgetParityModel P).toHom

theorem forgetParity_J : (forgetParity P) (J P) = 1 := (forgetParityModel P).toHom_J
theorem forgetParity_x (s : C) : (forgetParity P) (x P s) = x (homogeneous P) s :=
  (forgetParityModel P).toHom_x s

def modJToHomogeneous : (ModJ P) →* GroupOf (homogeneous P) :=
  (centralDatum P).lift (forgetParity P) (forgetParity_J P)

theorem modJToHomogeneous_quotient (g : GroupOf P) :
    (modJToHomogeneous P) ((quotientJ P) g) = (forgetParity P) g := rfl

def homogeneousProductModel : Model (homogeneous P) ((ModJ P) × CentralTwist.C₂) where
  j := (1, CentralTwist.j)
  x s := ((quotientX P) s, 1)
  j_square := by apply Prod.ext <;> simp [CentralTwist.j_square]
  x_square s := by apply Prod.ext <;> simp [(quotientX_square P)]
  j_commutes s := by apply Prod.ext <;> simp
  row_commutes r i j := by
    change ((quotientX P) (P.column r i), (1 : CentralTwist.C₂)) *
      ((quotientX P) (P.column r j), 1) =
      ((quotientX P) (P.column r j), 1) * ((quotientX P) (P.column r i), 1)
    apply Prod.ext
    · exact ((quotientX_commutes P) r i j).eq
    · rfl
  row_product r := by
    change ((quotientX P) (P.column r 0), (1 : CentralTwist.C₂)) *
      ((quotientX P) (P.column r 1), 1) * ((quotientX P) (P.column r 2), 1) = 1
    apply Prod.ext
    · exact (quotientX_row P) r
    · rfl

def homogeneousToProduct : GroupOf (homogeneous P) →* (ModJ P) × CentralTwist.C₂ :=
  (homogeneousProductModel P).toHom

theorem homogeneousToProduct_J : (homogeneousToProduct P) (J (homogeneous P)) = (1, CentralTwist.j) :=
  (homogeneousProductModel P).toHom_J

theorem homogeneousToProduct_x (s : C) : (homogeneousToProduct P) (x (homogeneous P) s) = ((quotientX P) s, 1) :=
  (homogeneousProductModel P).toHom_x s

def productToHomogeneous : (ModJ P) × CentralTwist.C₂ →* GroupOf (homogeneous P) :=
  (modJToHomogeneous P).noncommCoprod
    (CentralTwist.involutionHom (J (homogeneous P)) (J_sq (homogeneous P))) (by
      intro g c
      rcases CentralTwist.c₂_cases c with rfl | rfl
      · simp
      · rw [CentralTwist.involutionHom_j]
        exact (J_commutes (homogeneous P) _).symm)

theorem productToHomogeneous_left (g : (ModJ P)) :
    (productToHomogeneous P) (g, 1) = (modJToHomogeneous P) g := by simp [productToHomogeneous]

theorem productToHomogeneous_j : (productToHomogeneous P) (1, CentralTwist.j) = J (homogeneous P) := by
  simp [productToHomogeneous, CentralTwist.involutionHom_j]

theorem productToHomogeneous_comp_homogeneousToProduct :
    (productToHomogeneous P).comp (homogeneousToProduct P) = MonoidHom.id (GroupOf (homogeneous P)) := by
  apply hom_ext
  · change (productToHomogeneous P) ((homogeneousToProduct P) (J (homogeneous P))) = J (homogeneous P)
    rw [homogeneousToProduct_J, productToHomogeneous_j]
  · intro s
    change (productToHomogeneous P) ((homogeneousToProduct P) (x (homogeneous P) s)) = x (homogeneous P) s
    rw [homogeneousToProduct_x, productToHomogeneous_left, quotientX, modJToHomogeneous_quotient,
      forgetParity_x]

theorem homogeneousToProduct_forgetParity :
    (homogeneousToProduct P).comp (forgetParity P) = (MonoidHom.inl _ _).comp (quotientJ P) := by
  apply hom_ext
  · change (homogeneousToProduct P) ((forgetParity P) (J P)) = ((quotientJ P) (J P), 1)
    rw [forgetParity_J, quotientJ_J, map_one]
    rfl
  · intro s
    change (homogeneousToProduct P) ((forgetParity P) (x P s)) = ((quotientX P) s, 1)
    rw [forgetParity_x, homogeneousToProduct_x]

theorem homogeneousToProduct_modJToHomogeneous (g : (ModJ P)) :
    (homogeneousToProduct P) ((modJToHomogeneous P) g) = (g, 1) := by
  obtain ⟨g, rfl⟩ := (centralDatum P).projection_surjective g
  exact DFunLike.congr_fun (homogeneousToProduct_forgetParity P) g

theorem homogeneousToProduct_comp_productToHomogeneous :
    (homogeneousToProduct P).comp (productToHomogeneous P) = MonoidHom.id ((ModJ P) × CentralTwist.C₂) := by
  apply MonoidHom.ext
  rintro ⟨g, c⟩
  change (homogeneousToProduct P) ((productToHomogeneous P) (g, c)) = (g, c)
  rcases CentralTwist.c₂_cases c with rfl | rfl
  · rw [productToHomogeneous_left, homogeneousToProduct_modJToHomogeneous]
  · have hp : (g, CentralTwist.j) = (g, 1) * (1, CentralTwist.j) := by simp
    rw [hp, map_mul, map_mul, productToHomogeneous_left, productToHomogeneous_j,
      homogeneousToProduct_modJToHomogeneous, homogeneousToProduct_J]

def homogeneousEquiv : GroupOf (homogeneous P) ≃* (ModJ P) × CentralTwist.C₂ where
  toFun := (homogeneousToProduct P)
  invFun := (productToHomogeneous P)
  left_inv := DFunLike.congr_fun (productToHomogeneous_comp_homogeneousToProduct P)
  right_inv := DFunLike.congr_fun (homogeneousToProduct_comp_productToHomogeneous P)
  map_mul' := (homogeneousToProduct P).map_mul

theorem forgetParity_eq_one_iff (g : GroupOf P) : (forgetParity P) g = 1 ↔ g = 1 ∨ g = J P := by
  rw [← (quotientJ_eq_one_iff P)]
  constructor
  · intro h
    have hh := DFunLike.congr_fun (homogeneousToProduct_forgetParity P) g
    simpa [h] using (congrArg Prod.fst hh).symm
  · intro h
    rw [← modJToHomogeneous_quotient, h, map_one]

theorem homogeneous_J_ne_one : J (homogeneous P) ≠ 1 := by
  intro h
  have hh := homogeneousToProduct_J P
  rw [h, map_one] at hh
  exact CentralTwist.j_ne_one (congrArg Prod.snd hh).symm

theorem forgetParity_not_surjective : ¬ Function.Surjective (forgetParity P) := by
  intro h
  obtain ⟨g, hg⟩ := h (J (homogeneous P))
  have hh := DFunLike.congr_fun (homogeneousToProduct_forgetParity P) g
  change homogeneousToProduct P (forgetParity P g) = (quotientJ P g, 1) at hh
  rw [hg, homogeneousToProduct_J] at hh
  exact CentralTwist.j_ne_one (congrArg Prod.snd hh)

end ThomGame.SolutionGroup
