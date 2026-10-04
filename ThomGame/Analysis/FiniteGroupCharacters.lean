module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! Complex characters of finite groups, using the existing finite Fourier dual. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {C : Type*} [CommGroup C]

abbrev FiniteGroupCharacter (C : Type*) [CommGroup C] := AddChar (Additive C) ℂ

def finiteGroupCharacterHom (χ : FiniteGroupCharacter C) : C →* ℂ where
  toFun c := χ (Additive.ofMul c)
  map_one' := χ.map_zero_eq_one
  map_mul' c d := χ.map_add_eq_mul (Additive.ofMul c) (Additive.ofMul d)

theorem finiteGroupCharacterHom_apply (χ : FiniteGroupCharacter C) (c : C) :
    finiteGroupCharacterHom χ c = χ (Additive.ofMul c) := rfl

theorem finiteGroupCharacterHom_inv (χ : FiniteGroupCharacter C) (c : C) :
    finiteGroupCharacterHom χ c⁻¹ = (finiteGroupCharacterHom χ c)⁻¹ :=
  χ.map_neg_eq_inv (Additive.ofMul c)

variable [Fintype C]

theorem finiteGroupCharacterHom_norm (χ : FiniteGroupCharacter C) (c : C) :
    ‖finiteGroupCharacterHom χ c‖ = 1 := χ.norm_apply (Additive.ofMul c)

theorem finiteGroupCharacterHom_ne_zero (χ : FiniteGroupCharacter C) (c : C) :
    finiteGroupCharacterHom χ c ≠ 0 := by
  intro h
  have hn := finiteGroupCharacterHom_norm χ c
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem finiteGroupCharacterHom_conj (χ : FiniteGroupCharacter C) (c : C) :
    (starRingEnd ℂ) (finiteGroupCharacterHom χ c) = (finiteGroupCharacterHom χ c)⁻¹ :=
  (χ.inv_apply_eq_conj (Additive.ofMul c)).symm

omit [Fintype C] in
theorem finiteGroupCharacterHom_trivial (c : C) : finiteGroupCharacterHom (0 : FiniteGroupCharacter C) c = 1 := rfl

open scoped Classical in
theorem finiteGroupCharacterHom_sum (c : C) :
    ∑ χ : FiniteGroupCharacter C, finiteGroupCharacterHom χ c =
      if c = 1 then (Fintype.card C : ℂ) else 0 := by
  classical
  simpa only [finiteGroupCharacterHom_apply, ofMul_eq_zero, Fintype.card_additive] using
    AddChar.sum_apply_eq_ite (Additive.ofMul c)

omit [Fintype C] in
theorem finiteGroupCharacterHom_injective : Function.Injective (finiteGroupCharacterHom (C := C)) := by
  intro χ ψ h
  apply AddChar.ext
  intro c
  exact DFunLike.congr_fun h c.toMul

end ThomGame.Analysis
