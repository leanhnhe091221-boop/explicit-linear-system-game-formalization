module

public import ThomGame.Pictures.EulerMatching
public import ThomGame.Pictures.CircularSubsets

/-!
# Removing fixed ports from a circular partial matching

The moving ports of a label-preserving involution form a genuine pairing.
Their increasing enumeration preserves noninterlacing. Thus an Euler-
saturating circular partial matching has a relation-free diagram on the
remaining ports, in their original order. This does not identify its
full graph with the matching or assemble multiple vertex blocks.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CircularPartition
open scoped Classical

namespace ResidualMatching

section General

variable {D S : Type*} (t : Perm D) (ht : Function.Involutive t)
    (label : D → S) (hl : ∀ x, label (t x) = label x)

def pairing : Pairing (fun x : {x : D // t x ≠ x} => label x.val) where
  twin x := ⟨t x.val, fun he => x.property (t.injective he)⟩
  involutive x := Subtype.ext (ht x.val)
  ne_self x he := x.property (congrArg Subtype.val he)
  label_twin x := hl x.val

end General

variable {S : Type*} {n : Nat}

noncomputable def index (t : Perm (Fin n)) :
    Fin (Nat.card {i : Fin n // t i ≠ i}) ≃ {i : Fin n // t i ≠ i} :=
  (subsetEnumeration (fun i => t i ≠ i)).toEquiv

theorem index_strictMono (t : Perm (Fin n)) : StrictMono (fun i => (index t i).val) :=
  subsetEnumeration_strictMono _

noncomputable def word (t : Perm (Fin n)) (label : Fin n → S) : List S :=
  List.ofFn (fun i => label (index t i).val)

variable (t : Perm (Fin n)) (ht : Function.Involutive t)
    (label : Fin n → S) (hl : ∀ x, label (t x) = label x)

noncomputable def orderedPairing : Pairing (fun i => label (index t i).val) :=
  (pairing t ht label hl).transport (index t).symm _ (by
    intro x
    exact congrArg (fun y => label y.val) ((index t).apply_symm_apply x))

theorem orderedPairing_twin (i : Fin (Nat.card {i : Fin n // t i ≠ i})) :
    (index t ((orderedPairing t ht label hl).twin i)).val = t (index t i).val :=
  congrArg Subtype.val ((index t).apply_symm_apply _)

theorem orderedPairing_noninterlacing (hnc : NonInterlacing sbtw t) :
    NonInterlacing sbtw (orderedPairing t ht label hl).perm := by
  let e : Fin (Nat.card {i : Fin n // t i ≠ i}) ↪ Fin n :=
    (index t).toEmbedding.trans (Function.Embedding.subtype _)
  have he : FiniteReturn.Advances t (orderedPairing t ht label hl).perm e :=
    fun i => Or.inl (orderedPairing_twin t ht label hl i)
  intro a b c d habc hacd hac hbd
  exact (he.sameCycle_iff a b).mpr
    (hnc (e a) (e b) (e c) (e d)
      ((strictMono_sbtw _ (index_strictMono t) a b c).mpr habc)
      ((strictMono_sbtw _ (index_strictMono t) a c d).mpr hacd)
      ((he.sameCycle_iff a c).mp hac) ((he.sameCycle_iff b d).mp hbd))

include ht hl in
theorem exists_diagram {R : Type*} (P : InvolutionPresentation R S)
    (hnc : NonInterlacing sbtw t) :
    ∃ d : Diagram P (word t label) [], d.labels = [] :=
  exists_matching_diagram P _ (orderedPairing t ht label hl)
    (orderedPairing_noninterlacing t ht label hl hnc)

include ht hl in
theorem exists_diagram_of_euler {R : Type*} (P : InvolutionPresentation R S)
    (hEuler : RotationEuler.count (finRotate n) t =
      2 * Nat.card (RibbonConnectivity.Component (finRotate n) t)) :
    ∃ d : Diagram P (word t label) [], d.labels = [] :=
  exists_diagram t ht label hl P (RotationEuler.circular_noninterlacing t ht hEuler)

end ResidualMatching
end ThomGame.Pictures
