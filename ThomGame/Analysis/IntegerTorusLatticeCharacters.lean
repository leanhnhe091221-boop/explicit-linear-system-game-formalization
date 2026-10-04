module

public import ThomGame.Analysis.IntegerTorusCharacterEnergy
public import ThomGame.Analysis.IntegerTorusShearMeasureControl
public import ThomGame.Groups.IntegerPlaneShearAction

/-! Actual lattice characters and the transpose action of the two integer shears. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerTorus

theorem character_eq_one_iff (x : Circle) : character x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
    apply Subtype.ext
    simpa [character] using hx
  · rintro rfl
    exact character_zero

def latticeCharacter (v : IntegerPlane.Lattice) (x : Torus) : ℂ :=
  character (v.1 • x.1 + v.2 • x.2)

theorem latticeCharacter_continuous (v : IntegerPlane.Lattice) :
    Continuous (latticeCharacter v) :=
  character_continuous.comp (by fun_prop)

@[simp] theorem latticeCharacter_norm (v : IntegerPlane.Lattice) (x : Torus) :
    ‖latticeCharacter v x‖ = 1 := character_norm _

@[simp] theorem latticeCharacter_zero (x : Torus) : latticeCharacter 0 x = 1 := by
  simp [latticeCharacter]

theorem latticeCharacter_add (v w : IntegerPlane.Lattice) (x : Torus) :
    latticeCharacter (v + w) x = latticeCharacter v x * latticeCharacter w x := by
  dsimp [latticeCharacter]
  rw [add_zsmul, add_zsmul,
    show v.1 • x.1 + w.1 • x.1 + (v.2 • x.2 + w.2 • x.2) =
      (v.1 • x.1 + v.2 • x.2) + (w.1 • x.1 + w.2 • x.2) by abel,
    character_add]

def latticeCharacterHom (x : Torus) : IntegerPlane.Group →* ℂ where
  toFun v := latticeCharacter v.toAdd x
  map_one' := latticeCharacter_zero x
  map_mul' v w := latticeCharacter_add v.toAdd w.toAdd x

@[simp] theorem latticeCharacter_first (x : Torus) :
    latticeCharacter (1, 0) x = character x.1 := by simp [latticeCharacter]

@[simp] theorem latticeCharacter_second (x : Torus) :
    latticeCharacter (0, 1) x = character x.2 := by simp [latticeCharacter]

theorem coordinate_characters_eq_one_iff (x : Torus) :
    latticeCharacter (1, 0) x = 1 ∧ latticeCharacter (0, 1) x = 1 ↔ x = 0 := by
  simp only [latticeCharacter_first, latticeCharacter_second, character_eq_one_iff]
  exact Prod.mk_eq_zero.symm

theorem latticeCharacter_upperShear (v : IntegerPlane.Lattice) (x : Torus) :
    latticeCharacter (IntegerPlane.upperShear v) x = latticeCharacter v (lower 1 x) := by
  dsimp [latticeCharacter, IntegerPlane.upperShear, lower]
  rw [one_zsmul, add_zsmul, smul_add]
  congr 1
  abel

theorem latticeCharacter_lowerShear (v : IntegerPlane.Lattice) (x : Torus) :
    latticeCharacter (IntegerPlane.lowerShear v) x = latticeCharacter v (upper 1 x) := by
  dsimp [latticeCharacter, IntegerPlane.lowerShear, upper]
  rw [one_zsmul, add_zsmul, smul_add]
  congr 1
  abel

theorem latticeCharacter_shear (b : Bool) (v : IntegerPlane.Group) (x : Torus) :
    latticeCharacterHom x (IntegerPlane.shear b v) =
      latticeCharacterHom (integerShear b 1 x) v := by
  cases b
  · exact latticeCharacter_upperShear v.toAdd x
  · exact latticeCharacter_lowerShear v.toAdd x

theorem latticeCharacter_freeAction_generator (b : Bool) (v : IntegerPlane.Group) (x : Torus) :
    latticeCharacterHom x (IntegerPlane.freeAction (FreeGroup.of b) v) =
      latticeCharacterHom (integerShear b 1 x) v := by
  rw [IntegerPlane.freeAction_of]
  exact latticeCharacter_shear b v x

end ThomGame.Analysis.IntegerTorus
