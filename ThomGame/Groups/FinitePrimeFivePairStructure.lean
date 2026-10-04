module

public import ThomGame.Groups.FinitePrimeFivePairWords
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic

/-! The two generating abelian root subgroups and the central commutator structure. -/

@[expose] public section
namespace ThomGame.FinitePrimeFivePair

open scoped commutatorElement
variable {r : ℕ}

def leftHom : Multiplicative (Fin r → ZMod 5) →* FinitePrimeFivePair r where
  toFun x := leftVector x.toAdd
  map_one' := leftVector_zero
  map_mul' x y := leftVector_add _ _

def rightHom : Multiplicative (Fin r → ZMod 5) →* FinitePrimeFivePair r where
  toFun x := rightVector x.toAdd
  map_one' := rightVector_zero
  map_mul' x y := rightVector_add _ _

def leftSubgroup (r : ℕ) : Subgroup (FinitePrimeFivePair r) := leftHom.range
def rightSubgroup (r : ℕ) : Subgroup (FinitePrimeFivePair r) := rightHom.range

theorem leftVector_mem (α : Fin r → ZMod 5) : leftVector α ∈ leftSubgroup r :=
  ⟨Multiplicative.ofAdd α, rfl⟩

theorem rightVector_mem (β : Fin r → ZMod 5) : rightVector β ∈ rightSubgroup r :=
  ⟨Multiplicative.ofAdd β, rfl⟩

theorem left_commutative : ∀ g ∈ leftSubgroup r, ∀ h ∈ leftSubgroup r, Commute g h := by
  rintro _ ⟨α,rfl⟩ _ ⟨β,rfl⟩
  change leftVector α.toAdd * leftVector β.toAdd = leftVector β.toAdd * leftVector α.toAdd
  rw [← leftVector_add, ← leftVector_add, add_comm]

theorem right_commutative : ∀ g ∈ rightSubgroup r, ∀ h ∈ rightSubgroup r, Commute g h := by
  rintro _ ⟨α,rfl⟩ _ ⟨β,rfl⟩
  change rightVector α.toAdd * rightVector β.toAdd = rightVector β.toAdd * rightVector α.toAdd
  rw [← rightVector_add, ← rightVector_add, add_comm]

theorem commutator_eq_center (g h : FinitePrimeFivePair r) :
    ⁅g,h⁆ = centerVector (fun i j => g.left i * h.right j - h.left i * g.right j) := by
  change g * h * g⁻¹ * h⁻¹ = _
  ext i j <;> simp [centerVector] <;> ring

theorem commutator_le_center : _root_.commutator (FinitePrimeFivePair r) ≤
    Subgroup.center (FinitePrimeFivePair r) := by
  apply Subgroup.commutator_le.mpr
  intro g _ h _
  rw [commutator_eq_center]
  exact Subgroup.mem_center_iff.mpr (fun x => (centerVector_commutes _ x).eq.symm)

theorem isPGroup : IsPGroup 5 (FinitePrimeFivePair r) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro g
  exact ⟨1, by simpa only [pow_one] using pow_five g⟩

theorem right_isPGroup : IsPGroup 5 (rightSubgroup r) := isPGroup.to_subgroup _

theorem word_eval_mem (K : Subgroup (FinitePrimeFivePair r))
    (hgen : ∀ g, generator g ∈ K) (w : Word (Alphabet r)) : Word.eval generator w ∈ K := by
  induction w with
  | nil => simpa using K.one_mem
  | cons p w ih =>
    rcases p with ⟨x, b⟩
    have he : Word.eval generator ((x,b)::w) =
        (if b then generator x else (generator x)⁻¹) * Word.eval generator w := by
      simp [Word.eval, FreeGroup.lift_mk]
    rw [he]
    apply K.mul_mem _ ih
    cases b
    · exact K.inv_mem (hgen x)
    · exact hgen x

theorem left_sup_right : leftSubgroup r ⊔ rightSubgroup r = ⊤ := by
  apply top_unique
  intro g _
  rw [← eval_canonicalWord g]
  apply word_eval_mem
  rintro ⟨b,i⟩
  cases b
  · exact (show leftSubgroup r ≤ leftSubgroup r ⊔ rightSubgroup r from le_sup_left)
      (leftVector_mem (Pi.single i 1))
  · exact (show rightSubgroup r ≤ leftSubgroup r ⊔ rightSubgroup r from le_sup_right)
      (rightVector_mem (Pi.single i 1))

end ThomGame.FinitePrimeFivePair
