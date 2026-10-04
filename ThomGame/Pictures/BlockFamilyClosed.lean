module

public import ThomGame.Pictures.BlockFamilyTrace
public import ThomGame.Pictures.FullCycleMatching

/-!
# Closing an Euler-saturating connected family of diagram blocks

All relation blocks are assembled along the constructed contraction
trace. The single terminal boundary is then closed with its actual
relation-free matching diagram. The resulting closed diagram preserves
the multiset of every original relation occurrence.
-/

@[expose] public section
namespace ThomGame.Pictures.BlockFamily

open Equiv CyclicBlock RibbonConnectivity
open scoped BigOperators

variable {R S D : Type*} [DecidableEq D] [Finite D]
    {P : InvolutionPresentation R S} {label : D → S} {r t : Perm D}
    (F : BlockFamily P label r t)

theorem owner_eq_of_sameCycle {x y : D} (h : r.SameCycle x y) : F.owner x = F.owner y := by
  have hx := (F.mem_ports x (F.owner x)).mpr rfl
  have hy := ((F.block (F.owner x)).cyclic.mem_iff_sameCycle hx y).mpr h
  exact ((F.mem_ports y (F.owner x)).mp hy).symm

omit [Finite D] in
theorem owner_surjective : Function.Surjective F.owner := by
  intro i
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (F.block i).cyclic.nonempty
  exact ⟨x, (F.mem_ports x i).mp hx⟩

theorem relations_eq_block (hcycle : ∀ x y, r.SameCycle x y) (i : F.Index) :
    F.relations = ((F.block i).diagram.labels : Multiset R) := by
  classical
  have hi (j : F.Index) : j = i := by
    obtain ⟨x, hx⟩ := F.owner_surjective j
    obtain ⟨y, hy⟩ := F.owner_surjective i
    rw [← hx, ← hy]
    exact F.owner_eq_of_sameCycle (hcycle x y)
  unfold relations
  exact Finset.sum_eq_single i (fun j _ hji => (hji (hi j)).elim) (by simp)

theorem exists_closed_diagram (ht : Function.Involutive t)
    (hl : ∀ x, label (t x) = label x)
    (hEuler : RotationEuler.count r t = 2 * Nat.card (Component r t))
    (hconn : ∀ x y, Connected r t x y) :
    ∃ d : Diagram P [] [], (d.labels : Multiset R) = F.relations := by
  classical
  cases isEmpty_or_nonempty D with
  | inl hD =>
    let : IsEmpty D := hD
    let : IsEmpty F.Index := ⟨fun i => by
      obtain ⟨x, _⟩ := List.exists_mem_of_ne_nil _ (F.block i).cyclic.nonempty
      exact isEmptyElim x⟩
    exact ⟨.identity [], by simp [relations, Diagram.labels]⟩
  | inr hD =>
    obtain ⟨a⟩ := hD
    obtain ⟨r', t', k, c, F', hterm, hrel⟩ := F.exists_terminal ht hl
    have hcycle (x y : D) : r'.SameCycle x y :=
      (c.terminal_original_connected hterm x y).mpr (hconn x y)
    let i := F'.owner a
    have ha : a ∈ (F'.block i).ports := (F'.mem_ports a i).mpr rfl
    have hall (x : D) : x ∈ (F'.block i).ports :=
      ((F'.block i).cyclic.mem_iff_sameCycle ha x).mpr (hcycle a x)
    obtain ⟨d, hd⟩ := (F'.block i).cyclic.exists_filtered_diagram hall P t'
      (c.involutive ht) label (c.preserves_label ht label hl) (c.saturated ht hEuler)
    have hadj : d.adjoint.labels = [] := by
      apply List.perm_nil.mp
      simpa only [hd] using d.labels_adjoint_perm
    refine ⟨d.adjoint.comp (F'.block i).diagram, ?_⟩
    change ((d.adjoint.labels ++ (F'.block i).diagram.labels : List R) : Multiset R) = F.relations
    rw [hadj, List.nil_append]
    exact (F'.relations_eq_block hcycle i).symm.trans hrel

end ThomGame.Pictures.BlockFamily
