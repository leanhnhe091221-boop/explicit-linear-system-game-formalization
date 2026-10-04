module

public import ThomGame.Pictures.CircuitGermBoundary
public import ThomGame.Pictures.TwoStepReturn

/-!
# Empty corners along a path in a simple circuit

If all unmarked ports at a circuit vertex are on the same frontier side,
the opposite corner is a single actual rotation step. Selecting the same
side of each circuit edge therefore gives ports on one face across that
vertex. These conclusions use the actual rotation and sector orbits.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv MarkedReturn
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

theorem sector_exists_of_marked {x : G.Dart} (hx : C.Marked x) : ∃ s, C.Sector s x := by
  obtain ⟨⟨i, s⟩, rfl⟩ := hx
  exact ⟨s, (C.sector_marked s (i, s)).mpr rfl⟩

theorem sector_twin_of_marked {x : G.Dart} (hx : C.Marked x) {s : Bool}
    (hs : C.Sector s x) : C.Sector (!s) (G.pairing.twin x) := by
  obtain ⟨⟨i, b⟩, rfl⟩ := hx
  have hb := (C.sector_marked s (i, b)).mp hs
  change s = b at hb
  subst b
  rw [C.twin_port, C.sector_marked]
  exact (CircuitPermutations.edge_snd C.length (i, s)).symm

theorem sector_other_marked {x y : G.Dart} (hx : C.Marked x) (hy : C.Marked y)
    (hv : x.vertex = y.vertex) (hne : x ≠ y) {s : Bool} (hs : C.Sector s x) :
    C.Sector (!s) y := by
  obtain ⟨⟨i, b⟩, rfl⟩ := hx
  obtain ⟨⟨j, c⟩, rfl⟩ := hy
  have hij : i = j := C.vertex_injective
    ((C.port_vertex (i, b)).symm.trans (hv.trans (C.port_vertex (j, c))))
  subst j
  have hb := (C.sector_marked s (i, b)).mp hs
  change s = b at hb
  subst b
  rw [C.sector_marked]
  have hsc : s ≠ c := fun he => hne (congrArg (fun t => C.port (i, t)) he)
  cases s <;> cases c <;> simp_all

theorem empty_corner_rotation (i : Fin C.length) (s : Bool)
    (hext : ∀ x : G.Dart, x.vertex = (C.dart i).vertex → ¬ C.Marked x → C.Frontier s x) :
    G.rotation (C.port (i, s)) = C.port (i, !s) := by
  have hp := (C.sector_marked s (i, s)).mpr rfl
  have hm : C.Marked (G.rotation (C.port (i, s))) := by
    by_contra hn
    have hs : C.Sector s ((C.edgeTwist * G.rotation) (C.port (i, s))) := hp.apply_right
    change C.Sector s (C.edgeTwist (G.rotation (C.port (i, s)))) at hs
    rw [C.edgeTwist_of_unmarked _ hn] at hs
    have ht := hext _ ((G.vertex_rotation _).trans (C.port_vertex (i, s))) hn
    have he := C.sector_unique hs ht.1
    cases s <;> cases he
  have hret := perm_val_of_step G.rotation C.Marked (C.portEquiv (i, s)) hm
  have hstd := congrArg Subtype.val (C.rotation_return_port (i, s))
  exact hret.symm.trans hstd

noncomputable def sidePort (s : Bool) (x : G.Dart) : G.Dart :=
  if C.Sector s x then x else G.pairing.twin x

theorem empty_corner_rotation_of_sector {x y : G.Dart} (hx : C.Marked x) (hy : C.Marked y)
    (hv : x.vertex = y.vertex) (hne : x ≠ y) {s : Bool} (hs : C.Sector s x)
    (hext : ∀ z : G.Dart, z.vertex = x.vertex → ¬ C.Marked z → C.Frontier s z) :
    G.rotation x = y := by
  obtain ⟨⟨i, b⟩, rfl⟩ := hx
  obtain ⟨⟨j, c⟩, rfl⟩ := hy
  have hij : i = j := C.vertex_injective ((C.port_vertex (i, b)).symm.trans
    (hv.trans (C.port_vertex (j, c))))
  subst j
  have hb := (C.sector_marked s (i, b)).mp hs
  change s = b at hb
  subst b
  have hc : c = !s := by
    have hn : s ≠ c := fun he => hne (congrArg (fun t => C.port (i, t)) he)
    cases s <;> cases c <;> simp_all
  subst c
  exact C.empty_corner_rotation i s (fun z hz hn =>
    hext z (hz.trans (C.port_vertex (i, s)).symm) hn)

theorem sidePort_of_sector {s : Bool} {x : G.Dart} (hs : C.Sector s x) : C.sidePort s x = x := by
  simp only [sidePort, ite_eq_left hs]

theorem sidePort_of_opposite {s : Bool} {x : G.Dart} (hs : C.Sector (!s) x) :
    C.sidePort s x = G.pairing.twin x := by
  have hn : ¬ C.Sector s x := by
    intro ht
    have he := C.sector_unique ht hs
    cases s <;> cases he
  simp only [sidePort, ite_eq_right hn]

theorem sidePort_twin (s : Bool) {x : G.Dart} (hx : C.Marked x) :
    C.sidePort s (G.pairing.twin x) = C.sidePort s x := by
  obtain ⟨b, hb⟩ := C.sector_exists_of_marked hx
  have ht := C.sector_twin_of_marked hx hb
  by_cases hbs : b = s
  · subst b
    rw [C.sidePort_of_sector hb, C.sidePort_of_opposite ht, G.pairing.involutive]
  · have he : b = !s := by cases b <;> cases s <;> simp_all
    subst b
    have ht' : C.Sector s (G.pairing.twin x) := by simpa only [Bool.not_not] using ht
    rw [C.sidePort_of_opposite hb, C.sidePort_of_sector ht']

theorem empty_corner_sameCycle (s : Bool) {x y : G.Dart}
    (hx : C.Marked x) (hy : C.Marked y) (hv : x.vertex = y.vertex)
    (hext : ∀ z : G.Dart, z.vertex = x.vertex → ¬ C.Marked z → C.Frontier s z) :
    G.circuitStep.SameCycle (C.sidePort (!s) x) (C.sidePort (!s) y) := by
  obtain ⟨⟨i, b⟩, rfl⟩ := hx
  obtain ⟨⟨j, c⟩, rfl⟩ := hy
  have hij : i = j := C.vertex_injective
    ((C.port_vertex (i, b)).symm.trans (hv.trans (C.port_vertex (j, c))))
  subst j
  have ht := C.empty_corner_rotation i s (fun z hz hn =>
    hext z (hz.trans (C.port_vertex (i, b)).symm) hn)
  have hf : G.circuitStep.SameCycle (G.pairing.twin (C.port (i, s))) (C.port (i, !s)) := by
    have he : G.circuitStep (G.pairing.twin (C.port (i, s))) = C.port (i, !s) := by
      rw [G.circuitStep_apply, G.pairing.involutive, ht]
    exact ⟨1, he⟩
  cases s <;> cases b <;> cases c
  all_goals simp only [sidePort, C.sector_marked, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true] at hf ⊢
  all_goals first | exact Perm.SameCycle.rfl | exact hf | exact hf.symm

end ThomGame.Pictures.PortGraph.SimpleCircuit
