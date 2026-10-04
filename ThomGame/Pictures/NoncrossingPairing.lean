module

public import ThomGame.Pictures.PairingSurgery
public import ThomGame.Pictures.CircularInvolutions
public import ThomGame.Pictures.CircularCombination

/-!
# Splitting a noncrossing matching at its first chord

The two intervals inside and after the chord from position zero are
invariant under the actual edge pairing. Restricting and renumbering
either interval preserves its pairing and noninterlacing property.
-/

@[expose] public section
namespace ThomGame.Pictures

open CircularPartition

variable {S : Type*}

namespace NoncrossingPairing

def intervalIndex (n offset size : Nat) (hb : offset + size ≤ n) :
    Fin size ≃ {i : Fin n // offset ≤ i.val ∧ i.val < offset + size} where
  toFun i := ⟨⟨offset + i.val, by omega⟩, by change offset ≤ offset + i.val ∧ offset + i.val < offset + size; omega⟩
  invFun i := ⟨i.val.val - offset, by have := i.property; omega⟩
  left_inv i := by apply Fin.ext; simp
  right_inv i := by apply Subtype.ext; apply Fin.ext; have := i.property; dsimp; omega

theorem intervalIndex_strictMono (n offset size : Nat) (hb : offset + size ≤ n) :
    StrictMono (fun i => (intervalIndex n offset size hb i).val) := by
  intro i j hij
  change offset + i.val < offset + j.val
  exact Nat.add_lt_add_left hij offset

variable {n : Nat} {label : Fin n → S} (p : Pairing label)

def interval (offset size : Nat) (hb : offset + size ≤ n)
    (hclosed : ∀ i : Fin n, offset ≤ i.val ∧ i.val < offset + size →
      offset ≤ (p.twin i).val ∧ (p.twin i).val < offset + size) :
    Pairing (fun i : Fin size => label (intervalIndex n offset size hb i).val) :=
  (p.restrict _ hclosed).transport (intervalIndex n offset size hb).symm _ (by
    intro i
    exact congrArg (fun j => label j.val) ((intervalIndex n offset size hb).apply_symm_apply i))

theorem interval_twin (offset size : Nat) (hb : offset + size ≤ n)
    (hclosed : ∀ i : Fin n, offset ≤ i.val ∧ i.val < offset + size →
      offset ≤ (p.twin i).val ∧ (p.twin i).val < offset + size) (i : Fin size) :
    (intervalIndex n offset size hb ((interval p offset size hb hclosed).twin i)).val =
      p.twin (intervalIndex n offset size hb i).val := by
  exact congrArg Subtype.val ((intervalIndex n offset size hb).apply_symm_apply _)

theorem interval_noninterlacing (h : NonInterlacing sbtw p.perm)
    (offset size : Nat) (hb : offset + size ≤ n)
    (hclosed : ∀ i : Fin n, offset ≤ i.val ∧ i.val < offset + size →
      offset ≤ (p.twin i).val ∧ (p.twin i).val < offset + size) :
    NonInterlacing sbtw (interval p offset size hb hclosed).perm := by
  let e : Fin size ↪ Fin n :=
    (intervalIndex n offset size hb).toEmbedding.trans (Function.Embedding.subtype _)
  have he : FiniteReturn.Advances p.perm (interval p offset size hb hclosed).perm e :=
    fun i => Or.inl (interval_twin p offset size hb hclosed i)
  intro a b c d habc hacd hac hbd
  exact (he.sameCycle_iff a b).mpr
    (h (e a) (e b) (e c) (e d)
      ((strictMono_sbtw _ (intervalIndex_strictMono n offset size hb) a b c).mpr habc)
      ((strictMono_sbtw _ (intervalIndex_strictMono n offset size hb) a c d).mpr hacd)
      ((he.sameCycle_iff a c).mp hac) ((he.sameCycle_iff b d).mp hbd))

end NoncrossingPairing

namespace Pairing

variable {n : Nat} {label : Fin (n + 1) → S} (p : Pairing label)

theorem first_twin_pos : 0 < (p.twin 0).val := by
  have he := p.ne_self 0
  by_contra hh
  exact he (Fin.ext (by simp only [Fin.val_zero]; omega))

theorem firstChord_inside_stable (hnc : NonInterlacing sbtw p.perm)
    (x : Fin (n + 1)) (hx : 0 < x.val ∧ x.val < (p.twin 0).val) :
    0 < (p.twin x).val ∧ (p.twin x).val < (p.twin 0).val := by
  have hy0 : p.twin x ≠ 0 := by
    intro he
    have hh : x = p.twin 0 := (p.involutive x).symm.trans (congrArg p.twin he)
    have hv := congrArg Fin.val hh
    omega
  have hyj : p.twin x ≠ p.twin 0 := by
    intro he
    have hh := p.perm.injective he
    have hv := congrArg Fin.val hh
    change x.val = 0 at hv
    omega
  have hypos : 0 < (p.twin x).val := by
    by_contra hh
    exact hy0 (Fin.ext (by simp only [Fin.val_zero]; omega))
  refine ⟨hypos, ?_⟩
  by_contra hylt
  have hjy : (p.twin 0).val < (p.twin x).val := by
    have hv : (p.twin x).val ≠ (p.twin 0).val := fun he => hyj (Fin.ext he)
    omega
  have hsame := hnc 0 x (p.twin 0) (p.twin x)
    (by simp only [Fin.sbtw_iff, Fin.lt_def, Fin.val_zero]; omega)
    (by simp only [Fin.sbtw_iff, Fin.lt_def, Fin.val_zero]; omega)
    Equiv.Perm.SameCycle.rfl.apply_right Equiv.Perm.SameCycle.rfl.apply_right
  rcases (involutive_sameCycle p.perm p.involutive 0 x).mp hsame with hh | hh
  · have hv := congrArg Fin.val hh; change x.val = 0 at hv; omega
  · have hv := congrArg Fin.val hh; change x.val = (p.twin 0).val at hv; omega

theorem firstChord_after_stable (hnc : NonInterlacing sbtw p.perm)
    (x : Fin (n + 1)) (hx : (p.twin 0).val < x.val) :
    (p.twin 0).val < (p.twin x).val := by
  have hy0 : p.twin x ≠ 0 := by
    intro he
    have hh := congrArg Fin.val ((p.involutive x).symm.trans (congrArg p.twin he))
    omega
  have hyj : p.twin x ≠ p.twin 0 := by
    intro he
    have hh := congrArg Fin.val (p.perm.injective he)
    change x.val = 0 at hh
    omega
  by_contra hafter
  have hinside : 0 < (p.twin x).val ∧ (p.twin x).val < (p.twin 0).val := by
    have h0 : (p.twin x).val ≠ 0 := fun he => hy0 (Fin.ext he)
    have hj : (p.twin x).val ≠ (p.twin 0).val := fun he => hyj (Fin.ext he)
    omega
  have hi := p.firstChord_inside_stable hnc (p.twin x) hinside
  rw [p.involutive] at hi
  omega

end Pairing
end ThomGame.Pictures
