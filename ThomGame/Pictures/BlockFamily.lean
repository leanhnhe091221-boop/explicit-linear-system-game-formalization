module

public import ThomGame.Pictures.CyclicBlockDiagrams
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# A finite partition into cyclic blocks carrying actual diagrams

Every port has exactly one block owner. Merging the two blocks at a
non-loop edge removes one owner, joins their diagrams, and preserves
the multiset of all relation occurrences in the entire family.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CycleSurgery
open scoped BigOperators Classical

namespace BlockIndex

variable {I : Type*} [DecidableEq I]

def merge (a b : I) (hab : a ≠ b) (x : I) : {i : I // i ≠ b} :=
  ⟨if x = b then a else x, by split_ifs with hx; exact hab; exact hx⟩

theorem merge_eq (a b : I) (hab : a ≠ b) (x : I) (i : {i : I // i ≠ b}) :
    merge a b hab x = i ↔ x = i.val ∨ (i.val = a ∧ x = b) := by
  by_cases hx : x = b
  · simp [merge, hx, Subtype.ext_iff, i.property.symm, eq_comm]
  · simp [merge, hx, Subtype.ext_iff]

theorem sum_merge [Fintype I] {M : Type*} [AddCommMonoid M]
    (a b : I) (hab : a ≠ b) (w : I → M) :
    (∑ i : {i : I // i ≠ b}, if i.val = a then w a + w b else w i.val) = ∑ i, w i := by
  rw [← Finset.sum_subtype (p := fun i => i ≠ b) (Finset.univ.erase b) (by simp)
    (fun i => if i = a then w a + w b else w i)]
  have hw (i : I) : (if i = a then w a + w b else w i) =
      w i + (if i = a then w b else 0) := by
    split_ifs with hi
    · rw [hi]
    · simp
  simp_rw [hw]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.univ.erase b) a (fun _ => w b)]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  rw [ite_eq_left hab]
  exact Finset.sum_erase_add (Finset.univ : Finset I) w (Finset.mem_univ b)

end BlockIndex

universe u
variable {R S : Type*} {D : Type u} [DecidableEq D]
    (P : InvolutionPresentation R S) (label : D → S) (r t : Perm D)

structure BlockFamily where
  Index : Type u
  [indexFintype : Fintype Index]
  block : Index → DiagramBlock P label r t
  owner : D → Index
  mem_ports : ∀ (x : D) (i : Index), x ∈ (block i).ports ↔ owner x = i

attribute [instance] BlockFamily.indexFintype

namespace BlockFamily

variable {P label r t} (F : BlockFamily P label r t)

noncomputable def relations : Multiset R := ∑ i : F.Index, ((F.block i).diagram.labels : Multiset R)

noncomputable def rooted (a : D) : RootedBlock P label r t a :=
  (F.block (F.owner a)).root a ((F.mem_ports a (F.owner a)).mpr rfl)

theorem rooted_mem (a x : D) :
    x ∈ a :: (F.rooted a).tail ↔ F.owner x = F.owner a :=
  ((F.block (F.owner a)).root_rotated a ((F.mem_ports a _).mpr rfl)).mem_iff.symm.trans
    (F.mem_ports x _)

theorem rooted_labels (a : D) :
    (F.rooted a).diagram.labels = (F.block (F.owner a)).diagram.labels :=
  (F.block (F.owner a)).root_labels a ((F.mem_ports a _).mpr rfl)

variable [Finite D]

theorem owners_ne (a : D) (hr : ¬ r.SameCycle a (t a)) : F.owner a ≠ F.owner (t a) := by
  intro he
  apply hr
  exact (F.block (F.owner a)).cyclic.sameCycle_of_mem ((F.mem_ports a _).mpr rfl)
    ((F.mem_ports (t a) _).mpr he.symm)

noncomputable def mergedBlock (ht : Function.Involutive t)
    (hl : ∀ x, label (t x) = label x) (a : D) (hr : ¬ r.SameCycle a (t a))
    (i : {i : F.Index // i ≠ F.owner (t a)}) :
    DiagramBlock P label (splice r a (t a)) (splice t a (t a)) := by
  classical
  exact if hi : i.val = F.owner a then
    (F.rooted a).merge (F.rooted (t a)) ht hr (hl a).symm
  else
    (F.block i.val).untouched ht a
      (fun hx => hi ((F.mem_ports a i.val).mp hx).symm)
      (fun hx => i.property ((F.mem_ports (t a) i.val).mp hx).symm)

theorem mergedBlock_mem (ht : Function.Involutive t) (hl : ∀ x, label (t x) = label x)
    (a : D) (hr : ¬ r.SameCycle a (t a)) (i : {i : F.Index // i ≠ F.owner (t a)}) (x : D) :
    x ∈ (F.mergedBlock ht hl a hr i).ports ↔
      F.owner x = i.val ∨ (i.val = F.owner a ∧ F.owner x = F.owner (t a)) := by
  classical
  by_cases hi : i.val = F.owner a
  · simp only [mergedBlock, dite_eq_left hi, RootedBlock.merge, List.mem_append]
    rw [F.rooted_mem, F.rooted_mem]
    simp only [hi, true_and]
  · simp only [mergedBlock, dite_eq_right hi, DiagramBlock.untouched, hi, false_and, or_false]
    exact F.mem_ports x i.val

theorem mergedBlock_labels (ht : Function.Involutive t) (hl : ∀ x, label (t x) = label x)
    (a : D) (hr : ¬ r.SameCycle a (t a)) (i : {i : F.Index // i ≠ F.owner (t a)}) :
    (F.mergedBlock ht hl a hr i).diagram.labels =
      if i.val = F.owner a then
        (F.block (F.owner a)).diagram.labels ++ (F.block (F.owner (t a))).diagram.labels
      else (F.block i.val).diagram.labels := by
  classical
  unfold mergedBlock
  split_ifs with hi
  · rw [dite_eq_left hi, RootedBlock.merge_labels, F.rooted_labels, F.rooted_labels]
  · rw [dite_eq_right hi]
    exact DiagramBlock.untouched_labels _ _ _ _ _

noncomputable def merge (ht : Function.Involutive t) (hl : ∀ x, label (t x) = label x)
    (a : D) (hr : ¬ r.SameCycle a (t a)) :
    BlockFamily P label (splice r a (t a)) (splice t a (t a)) := by
  classical
  exact {
    Index := {i : F.Index // i ≠ F.owner (t a)}
    block := F.mergedBlock ht hl a hr
    owner := fun x => BlockIndex.merge (F.owner a) (F.owner (t a)) (F.owners_ne a hr) (F.owner x)
    mem_ports := fun x i => (F.mergedBlock_mem ht hl a hr i x).trans
      (BlockIndex.merge_eq _ _ (F.owners_ne a hr) _ i).symm }

theorem merge_relations (ht : Function.Involutive t) (hl : ∀ x, label (t x) = label x)
    (a : D) (hr : ¬ r.SameCycle a (t a)) :
    (F.merge ht hl a hr).relations = F.relations := by
  classical
  unfold relations merge
  simp_rw [mergedBlock_labels]
  simp only [apply_ite, ← Multiset.coe_add]
  exact BlockIndex.sum_merge (F.owner a) (F.owner (t a)) (F.owners_ne a hr)
    (fun i => ((F.block i).diagram.labels : Multiset R))

end BlockFamily
end ThomGame.Pictures
