module

public import ThomGame.Finite.WheelSystem
public import ThomGame.Finite.BlockNumbering

/-! Numbering wrappers use the proved total length without reducing concrete data. -/

@[expose] public section
namespace ThomGame.Wheel.Family

open scoped BigOperators

variable {n : Nat} {V : Type*} (F : Family (Option (Fin n)) V)

def slotNumbering (L k : Nat) (h : F.totalLength = L) :
    (r : Option (Fin n)) × (Fin (F.size r) × Fin k) ≃ Fin (L * k) :=
  BlockNumbering.slotEquiv F.size L k h

theorem slotNumbering_val (L k : Nat) (h : F.totalLength = L)
    (r : Option (Fin n)) (j : Fin (F.size r)) (a : Fin k) :
    (F.slotNumbering L k h ⟨r, j, a⟩).val =
      k * (BlockNumbering.prefixSum F.size r + j.val) + a.val :=
  BlockNumbering.slotEquiv_val F.size L k h r j a

end ThomGame.Wheel.Family
