module

public import ThomGame.Analysis.IntegerTorusCharacterEnergy
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-! Continuous torus functional calculus for two unitaries in a commutative C⋆-algebra. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerTorus

open WeakDual

def coordinateCharacter (b : Bool) : C(Torus, ℂ) :=
  if b then ⟨fun x => character x.2, character_continuous.comp continuous_snd⟩
  else ⟨fun x => character x.1, character_continuous.comp continuous_fst⟩

variable {A : Type*} [CommCStarAlgebra A]

def spectralCircle (u : unitary A) : C(characterSpace ℂ A, _root_.Circle) where
  toFun φ := ⟨φ (u : A), mem_sphere_zero_iff_norm.mpr
    (CStarRing.norm_of_mem_unitary (Unitary.map_mem φ u.property))⟩
  continuous_toFun := (gelfandTransform ℂ A (u : A)).continuous.subtype_mk _

def spectralCoordinate (u : unitary A) : C(characterSpace ℂ A, Circle) where
  toFun φ := (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm (spectralCircle u φ)
  continuous_toFun := (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm.continuous.comp
    (spectralCircle u).continuous

theorem character_spectralCoordinate (u : unitary A) (φ : characterSpace ℂ A) :
    character (spectralCoordinate u φ) = φ (u : A) := by
  have h := (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).apply_symm_apply
    (spectralCircle u φ)
  rw [AddCircle.homeomorphCircle_apply] at h
  exact congrArg (fun z : _root_.Circle => (z : ℂ)) h

def spectralPoint (u v : unitary A) : C(characterSpace ℂ A, Torus) where
  toFun φ := (spectralCoordinate u φ, spectralCoordinate v φ)
  continuous_toFun := (spectralCoordinate u).continuous.prodMk (spectralCoordinate v).continuous

def torusFunctionalCalculus (u v : unitary A) : C(Torus, ℂ) →⋆ₐ[ℂ] A :=
  (gelfandStarTransform A).symm.toStarAlgHom.comp ((spectralPoint u v).compStarAlgHom' ℂ ℂ)

theorem gelfand_torusFunctionalCalculus (u v : unitary A) (f : C(Torus, ℂ)) :
    gelfandStarTransform A (torusFunctionalCalculus u v f) = f.comp (spectralPoint u v) :=
  (gelfandStarTransform A).apply_symm_apply _

theorem torusFunctionalCalculus_first (u v : unitary A) :
    torusFunctionalCalculus u v (coordinateCharacter false) = (u : A) := by
  apply (gelfandStarTransform A).injective
  change gelfandStarTransform A (torusFunctionalCalculus u v (coordinateCharacter false)) =
    gelfandStarTransform A (u : A)
  rw [gelfand_torusFunctionalCalculus]
  ext φ
  exact character_spectralCoordinate u φ

theorem torusFunctionalCalculus_second (u v : unitary A) :
    torusFunctionalCalculus u v (coordinateCharacter true) = (v : A) := by
  apply (gelfandStarTransform A).injective
  change gelfandStarTransform A (torusFunctionalCalculus u v (coordinateCharacter true)) =
    gelfandStarTransform A (v : A)
  rw [gelfand_torusFunctionalCalculus]
  ext φ
  exact character_spectralCoordinate v φ

theorem torusFunctionalCalculus_norm_le (u v : unitary A) (f : C(Torus, ℂ)) :
    ‖torusFunctionalCalculus u v f‖ ≤ ‖f‖ :=
  NonUnitalStarAlgHom.norm_apply_le (torusFunctionalCalculus u v) f

end ThomGame.Analysis.IntegerTorus
