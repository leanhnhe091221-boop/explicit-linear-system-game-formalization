module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

/-! The universal finite class-two pair group in explicit prime-five coordinates.
The coordinates are the exponents of the ordered a, b, and [a,b] factors. -/

@[expose] public section
namespace ThomGame

@[ext] structure FinitePrimeFivePair (r : ℕ) where
  left : Fin r → ZMod 5
  right : Fin r → ZMod 5
  central : Fin r → Fin r → ZMod 5
  deriving DecidableEq, Fintype

namespace FinitePrimeFivePair

variable {r : ℕ}

def multiply (g h : FinitePrimeFivePair r) : FinitePrimeFivePair r where
  left := g.left + h.left
  right := g.right + h.right
  central := fun i j => g.central i j + h.central i j - h.left i * g.right j

def identity : FinitePrimeFivePair r := ⟨0, 0, 0⟩

def inverse (g : FinitePrimeFivePair r) : FinitePrimeFivePair r where
  left := -g.left
  right := -g.right
  central := fun i j => -g.central i j - g.left i * g.right j

theorem multiply_assoc (g h k : FinitePrimeFivePair r) :
    multiply (multiply g h) k = multiply g (multiply h k) := by
  ext <;> dsimp [multiply] <;> ring

theorem identity_multiply (g : FinitePrimeFivePair r) : multiply identity g = g := by
  ext <;> simp [multiply, identity]

theorem multiply_identity (g : FinitePrimeFivePair r) : multiply g identity = g := by
  ext <;> simp [multiply, identity]

theorem inverse_multiply (g : FinitePrimeFivePair r) : multiply (inverse g) g = identity := by
  ext <;> simp [multiply, inverse, identity] <;> ring

instance : Group (FinitePrimeFivePair r) where
  mul := multiply
  one := identity
  inv := inverse
  mul_assoc := multiply_assoc
  one_mul := identity_multiply
  mul_one := multiply_identity
  inv_mul_cancel := inverse_multiply

@[simp] theorem mul_left (g h : FinitePrimeFivePair r) : (g * h).left = g.left + h.left := rfl
@[simp] theorem mul_right (g h : FinitePrimeFivePair r) : (g * h).right = g.right + h.right := rfl
@[simp] theorem mul_central (g h : FinitePrimeFivePair r) (i j : Fin r) :
    (g * h).central i j = g.central i j + h.central i j - h.left i * g.right j := rfl
@[simp] theorem one_left : (1 : FinitePrimeFivePair r).left = 0 := rfl
@[simp] theorem one_right : (1 : FinitePrimeFivePair r).right = 0 := rfl
@[simp] theorem one_central : (1 : FinitePrimeFivePair r).central = 0 := rfl
@[simp] theorem inv_left (g : FinitePrimeFivePair r) : g⁻¹.left = -g.left := rfl
@[simp] theorem inv_right (g : FinitePrimeFivePair r) : g⁻¹.right = -g.right := rfl
@[simp] theorem inv_central (g : FinitePrimeFivePair r) (i j : Fin r) :
    g⁻¹.central i j = -g.central i j - g.left i * g.right j := rfl

def coordinateEquiv : FinitePrimeFivePair r ≃
    (Fin r → ZMod 5) × (Fin r → ZMod 5) × (Fin r → Fin r → ZMod 5) where
  toFun g := (g.left, g.right, g.central)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv g := rfl
  right_inv p := rfl

theorem card (r : ℕ) : Fintype.card (FinitePrimeFivePair r) = 5 ^ (r ^ 2 + 2 * r) := by
  rw [Fintype.card_congr (coordinateEquiv (r := r))]
  simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

def leftVector (α : Fin r → ZMod 5) : FinitePrimeFivePair r := ⟨α, 0, 0⟩
def rightVector (β : Fin r → ZMod 5) : FinitePrimeFivePair r := ⟨0, β, 0⟩
def centerVector (γ : Fin r → Fin r → ZMod 5) : FinitePrimeFivePair r := ⟨0, 0, γ⟩

@[simp] theorem leftVector_zero : leftVector (0 : Fin r → ZMod 5) = 1 := rfl
@[simp] theorem rightVector_zero : rightVector (0 : Fin r → ZMod 5) = 1 := rfl
@[simp] theorem centerVector_zero : centerVector (0 : Fin r → Fin r → ZMod 5) = 1 := rfl

theorem leftVector_add (α β : Fin r → ZMod 5) : leftVector (α + β) = leftVector α * leftVector β := by
  ext <;> simp [leftVector]
theorem rightVector_add (α β : Fin r → ZMod 5) : rightVector (α + β) = rightVector α * rightVector β := by
  ext <;> simp [rightVector]
theorem centerVector_add (α β : Fin r → Fin r → ZMod 5) :
    centerVector (α + β) = centerVector α * centerVector β := by
  ext <;> simp [centerVector]

theorem canonical_factors (g : FinitePrimeFivePair r) :
    leftVector g.left * rightVector g.right * centerVector g.central = g := by
  ext <;> simp [leftVector, rightVector, centerVector]

theorem commutator_vectors (α β : Fin r → ZMod 5) :
    leftVector α * rightVector β * (leftVector α)⁻¹ * (rightVector β)⁻¹ =
      centerVector (fun i j => α i * β j) := by
  ext <;> simp [leftVector, rightVector, centerVector]

theorem centerVector_commutes (γ : Fin r → Fin r → ZMod 5) (g : FinitePrimeFivePair r) :
    Commute (centerVector γ) g := by
  change centerVector γ * g = g * centerVector γ
  ext <;> simp [centerVector, add_comm]

theorem pow_five (g : FinitePrimeFivePair r) : g ^ 5 = 1 := by
  ext i j <;> simp only [pow_succ, pow_zero, one_mul, mul_left, mul_right, mul_central,
    one_left, one_right, one_central, Pi.add_apply, Pi.zero_apply]
  all_goals ring_nf
  all_goals simp only [show (5 : ZMod 5) = 0 from rfl, show (10 : ZMod 5) = 0 from rfl,
    mul_zero, sub_zero]

theorem eq_one_of_eq_inv (g : FinitePrimeFivePair r) (h : g = g⁻¹) : g = 1 := by
  have hs : g * g = 1 := (congrArg (fun x => x * g) h).trans (inv_mul_cancel g)
  have hp := pow_five g
  simpa only [show g ^ 5 = (g * g) * (g * g) * g by simp [pow_succ, mul_assoc],
    hs, one_mul] using hp

end FinitePrimeFivePair
end ThomGame

