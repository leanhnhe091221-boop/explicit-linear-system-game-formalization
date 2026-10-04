module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Tactic.Abel

/-! The standard upper and lower shears acting on the genuine integer lattice. -/

@[expose] public section
namespace ThomGame.IntegerPlane

abbrev Lattice := ℤ × ℤ
abbrev Group := Multiplicative Lattice

def upperShear : Lattice ≃+ Lattice where
  toFun v := (v.1 + v.2, v.2)
  invFun v := (v.1 - v.2, v.2)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
  map_add' v w := by ext <;> simp only [Prod.fst_add, Prod.snd_add]; abel

def lowerShear : Lattice ≃+ Lattice where
  toFun v := (v.1, v.1 + v.2)
  invFun v := (v.1, v.2 - v.1)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
  map_add' v w := by ext <;> simp only [Prod.fst_add, Prod.snd_add]; abel

def shear (b : Bool) : MulAut Group :=
  if b then lowerShear.toMultiplicative else upperShear.toMultiplicative

def freeAction : FreeGroup Bool →* MulAut Group := FreeGroup.lift shear

@[simp] theorem freeAction_of (b : Bool) : freeAction (FreeGroup.of b) = shear b := FreeGroup.lift_apply_of

theorem upperShear_apply (v : Group) : (shear false v).toAdd = (v.toAdd.1 + v.toAdd.2, v.toAdd.2) := rfl

theorem lowerShear_apply (v : Group) : (shear true v).toAdd = (v.toAdd.1, v.toAdd.1 + v.toAdd.2) := rfl

abbrev FreeShearProduct := Group ⋊[freeAction] FreeGroup Bool

end ThomGame.IntegerPlane
