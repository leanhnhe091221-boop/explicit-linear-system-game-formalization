module

public import ThomGame.Groups.InvolutionPresentation
public import ThomGame.Groups.CentralQuotient
public import ThomGame.Groups.CentralTwist
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Erasing parity in an involution presentation

The homogeneous presentation is isomorphic to (G / {1,J}) × C₂.
The fresh C₂ factor must not be confused with the J killed by the quotient.
-/

@[expose] public section
namespace ThomGame.InvolutionPresentation

variable {R S : Type*} (P : InvolutionPresentation R S)

def centralDatum : CentralQuotient.Datum (GroupOf P) where
  j := J P
  square := J_sq P
  central := J_commutes P

abbrev ModJ := P.centralDatum.GroupOf

def quotientJ : GroupOf P →* P.ModJ := P.centralDatum.projection

theorem quotientJ_eq_one_iff (g : GroupOf P) : P.quotientJ g = 1 ↔ g = 1 ∨ g = J P :=
  P.centralDatum.projection_eq_one_iff g

theorem quotientJ_J : P.quotientJ (J P) = 1 := P.centralDatum.projection_j

def homogeneous : InvolutionPresentation R S := ⟨P.word, fun _ => 0⟩

def quotientX (s : S) : P.ModJ := P.quotientJ (x P s)

theorem quotientX_square (s : S) : P.quotientX s * P.quotientX s = 1 := by
  rw [quotientX, ← map_mul, x_sq, map_one]

theorem quotientX_word (r : R) : ((P.word r).map P.quotientX).prod = 1 := by
  change ((P.word r).map (fun s => P.quotientJ (x P s))).prod = 1
  have h := congrArg P.quotientJ (word_product P r)
  by_cases hp : P.parity r = 1 <;>
    simpa [hp, map_list_prod, List.map_map, Function.comp_def, quotientX, quotientJ_J] using h

def forgetParityModel : Model P (GroupOf P.homogeneous) where
  j := 1
  x := x P.homogeneous
  j_square := one_mul 1
  x_square := x_sq P.homogeneous
  j_commutes := fun _ => Commute.one_left _
  word_product r := by
    simp only [ite_self]
    simpa [homogeneous] using word_product P.homogeneous r

def forgetParity : GroupOf P →* GroupOf P.homogeneous := P.forgetParityModel.toHom

theorem forgetParity_J : P.forgetParity (J P) = 1 := P.forgetParityModel.toHom_J
theorem forgetParity_x (s : S) : P.forgetParity (x P s) = x P.homogeneous s :=
  P.forgetParityModel.toHom_x s

def modJToHomogeneous : P.ModJ →* GroupOf P.homogeneous :=
  P.centralDatum.lift P.forgetParity P.forgetParity_J

theorem modJToHomogeneous_quotient (g : GroupOf P) :
    P.modJToHomogeneous (P.quotientJ g) = P.forgetParity g := rfl

def homogeneousProductModel : Model P.homogeneous (P.ModJ × CentralTwist.C₂) where
  j := (1, CentralTwist.j)
  x s := (P.quotientX s, 1)
  j_square := by apply Prod.ext <;> simp [CentralTwist.j_square]
  x_square s := by apply Prod.ext <;> simp [P.quotientX_square]
  j_commutes s := by apply Prod.ext <;> simp
  word_product r := by
    change ((P.word r).map (fun s => (P.quotientX s, 1))).prod = 1
    have h := congrArg (MonoidHom.inl P.ModJ CentralTwist.C₂) (P.quotientX_word r)
    simpa only [map_list_prod, List.map_map, Function.comp_def, MonoidHom.inl_apply, map_one] using h

def homogeneousToProduct : GroupOf P.homogeneous →* P.ModJ × CentralTwist.C₂ :=
  P.homogeneousProductModel.toHom

theorem homogeneousToProduct_J : P.homogeneousToProduct (J P.homogeneous) = (1, CentralTwist.j) :=
  P.homogeneousProductModel.toHom_J

theorem homogeneousToProduct_x (s : S) : P.homogeneousToProduct (x P.homogeneous s) = (P.quotientX s, 1) :=
  P.homogeneousProductModel.toHom_x s

def productToHomogeneous : P.ModJ × CentralTwist.C₂ →* GroupOf P.homogeneous :=
  P.modJToHomogeneous.noncommCoprod
    (CentralTwist.involutionHom (J P.homogeneous) (J_sq P.homogeneous)) (by
      intro g c
      rcases CentralTwist.c₂_cases c with rfl | rfl
      · simp
      · rw [CentralTwist.involutionHom_j]
        exact (J_commutes P.homogeneous _).symm)

theorem productToHomogeneous_left (g : P.ModJ) :
    P.productToHomogeneous (g, 1) = P.modJToHomogeneous g := by simp [productToHomogeneous]

theorem productToHomogeneous_j : P.productToHomogeneous (1, CentralTwist.j) = J P.homogeneous := by
  simp [productToHomogeneous, CentralTwist.involutionHom_j]

theorem productToHomogeneous_comp_homogeneousToProduct :
    P.productToHomogeneous.comp P.homogeneousToProduct = MonoidHom.id (GroupOf P.homogeneous) := by
  apply hom_ext
  · change P.productToHomogeneous (P.homogeneousToProduct (J P.homogeneous)) = J P.homogeneous
    rw [homogeneousToProduct_J, productToHomogeneous_j]
  · intro s
    change P.productToHomogeneous (P.homogeneousToProduct (x P.homogeneous s)) = x P.homogeneous s
    rw [homogeneousToProduct_x, productToHomogeneous_left, quotientX, modJToHomogeneous_quotient,
      forgetParity_x]

theorem homogeneousToProduct_forgetParity :
    P.homogeneousToProduct.comp P.forgetParity = (MonoidHom.inl _ _).comp P.quotientJ := by
  apply hom_ext
  · change P.homogeneousToProduct (P.forgetParity (J P)) = (P.quotientJ (J P), 1)
    rw [forgetParity_J, quotientJ_J, map_one]
    rfl
  · intro s
    change P.homogeneousToProduct (P.forgetParity (x P s)) = (P.quotientX s, 1)
    rw [forgetParity_x, homogeneousToProduct_x]

theorem homogeneousToProduct_modJToHomogeneous (g : P.ModJ) :
    P.homogeneousToProduct (P.modJToHomogeneous g) = (g, 1) := by
  obtain ⟨g, rfl⟩ := P.centralDatum.projection_surjective g
  exact DFunLike.congr_fun P.homogeneousToProduct_forgetParity g

theorem homogeneousToProduct_comp_productToHomogeneous :
    P.homogeneousToProduct.comp P.productToHomogeneous = MonoidHom.id (P.ModJ × CentralTwist.C₂) := by
  apply MonoidHom.ext
  rintro ⟨g, c⟩
  change P.homogeneousToProduct (P.productToHomogeneous (g, c)) = (g, c)
  rcases CentralTwist.c₂_cases c with rfl | rfl
  · rw [productToHomogeneous_left, homogeneousToProduct_modJToHomogeneous]
  · have hp : (g, CentralTwist.j) = (g, 1) * (1, CentralTwist.j) := by simp
    rw [hp, map_mul, map_mul, productToHomogeneous_left, productToHomogeneous_j,
      homogeneousToProduct_modJToHomogeneous, homogeneousToProduct_J]

def homogeneousEquiv : GroupOf P.homogeneous ≃* P.ModJ × CentralTwist.C₂ where
  toFun := P.homogeneousToProduct
  invFun := P.productToHomogeneous
  left_inv := DFunLike.congr_fun P.productToHomogeneous_comp_homogeneousToProduct
  right_inv := DFunLike.congr_fun P.homogeneousToProduct_comp_productToHomogeneous
  map_mul' := P.homogeneousToProduct.map_mul

theorem forgetParity_eq_one_iff (g : GroupOf P) : P.forgetParity g = 1 ↔ g = 1 ∨ g = J P := by
  rw [← P.quotientJ_eq_one_iff]
  constructor
  · intro h
    have hh := DFunLike.congr_fun P.homogeneousToProduct_forgetParity g
    simpa [h] using (congrArg Prod.fst hh).symm
  · intro h
    rw [← modJToHomogeneous_quotient, h, map_one]

theorem homogeneous_J_ne_one : J P.homogeneous ≠ 1 := by
  intro h
  have hh := P.homogeneousToProduct_J
  rw [h, map_one] at hh
  exact CentralTwist.j_ne_one (congrArg Prod.snd hh).symm

theorem forgetParity_not_surjective : ¬ Function.Surjective P.forgetParity := by
  intro h
  obtain ⟨g, hg⟩ := h (J P.homogeneous)
  have hh := DFunLike.congr_fun P.homogeneousToProduct_forgetParity g
  change P.homogeneousToProduct (P.forgetParity g) = (P.quotientJ g, 1) at hh
  rw [hg, homogeneousToProduct_J] at hh
  exact CentralTwist.j_ne_one (congrArg Prod.snd hh)

end ThomGame.InvolutionPresentation
