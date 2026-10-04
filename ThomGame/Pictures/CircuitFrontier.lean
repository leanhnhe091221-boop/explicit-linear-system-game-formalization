module

public import ThomGame.Pictures.SimpleCircuitSectors
public import ThomGame.Pictures.OrbitSubsetEnumeration

/-!
# Ordered frontier ports of the two circuit sectors

Each frontier follows the twisted vertex orbit in its genuine cyclic
order, retaining precisely the unmarked ports. These are the ports to
become boundary leaves when the circuit vertices are removed from that
side. The two lists partition all unmarked ports at circuit vertices.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv MarkedReturn

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

def Frontier (s : Bool) (a : G.Dart) : Prop := C.Sector (!s) a ∧ ¬ C.Marked a

noncomputable def frontierLength (s : Bool) : Nat :=
  OrbitEnumeration.retainedLength (C.edgeTwist * G.rotation) (C.port (0, !s)) (fun a => ¬ C.Marked a)

noncomputable def frontierEnumeration (s : Bool) : Fin (C.frontierLength s) ≃ Subtype (C.Frontier s) :=
  OrbitEnumeration.retainedEnumeration (C.edgeTwist * G.rotation) (C.port (0, !s)) (fun a => ¬ C.Marked a)

theorem frontierEnumeration_return (s : Bool) (i : Fin (C.frontierLength s)) :
    perm (C.edgeTwist * G.rotation) (C.Frontier s) (C.frontierEnumeration s i) =
      C.frontierEnumeration s (finRotate (C.frontierLength s) i) :=
  OrbitEnumeration.retainedEnumeration_return _ _ _ i

noncomputable def frontierDarts (s : Bool) : List G.Dart :=
  OrbitEnumeration.retainedList (C.edgeTwist * G.rotation) (C.port (0, !s)) (fun a => ¬ C.Marked a)

theorem frontierDarts_length (s : Bool) : (C.frontierDarts s).length = C.frontierLength s :=
  OrbitEnumeration.retainedList_length _ _ _

theorem mem_frontierDarts (s : Bool) (a : G.Dart) : a ∈ C.frontierDarts s ↔ C.Frontier s a :=
  OrbitEnumeration.mem_retainedList _ _ _ a

theorem frontierDarts_nodup (s : Bool) : (C.frontierDarts s).Nodup :=
  OrbitEnumeration.retainedList_nodup _ _ _

theorem frontier_unique {a : G.Dart} {s t : Bool} (hs : C.Frontier s a) (ht : C.Frontier t a) : s = t := by
  have he := C.sector_unique hs.1 ht.1
  simpa only [Bool.not_not] using congrArg (fun b : Bool => !b) he

theorem exists_frontier_iff (a : G.Dart) :
    (∃ s, C.Frontier s a) ↔ C.OnCircuitVertex a.vertex ∧ ¬ C.Marked a := by
  constructor
  · rintro ⟨s, hs, ha⟩
    exact ⟨(C.onCircuitVertex_iff_sector a).mpr ⟨!s, hs⟩, ha⟩
  · rintro ⟨hv, ha⟩
    obtain ⟨s, hs⟩ := (C.onCircuitVertex_iff_sector a).mp hv
    refine ⟨!s, ?_, ha⟩
    simpa only [Bool.not_not] using hs

/-- The label word reads the actual frontier ports in their cyclic order. -/
noncomputable def frontierWord (s : Bool) : List S :=
  List.ofFn (fun i : Fin (C.frontierLength s) => Port.label G.jointLabel (C.frontierEnumeration s i).val)

theorem frontierWord_length (s : Bool) : (C.frontierWord s).length = C.frontierLength s := List.length_ofFn

theorem frontierWord_get (s : Bool) (i : Fin (C.frontierLength s)) :
    (C.frontierWord s)[i.val]'(by rw [C.frontierWord_length]; exact i.isLt) =
      Port.label G.jointLabel (C.frontierEnumeration s i).val := by
  simp [frontierWord]

noncomputable def boundaryEnumeration (s : Bool) :
    Fin (C.frontierWord s).length ≃ Subtype (C.Frontier s) :=
  (finCongr (C.frontierWord_length s)).trans (C.frontierEnumeration s)

theorem boundaryEnumeration_label (s : Bool) (i : Fin (C.frontierWord s).length) :
    Port.label G.jointLabel (C.boundaryEnumeration s i).val = (C.frontierWord s)[i.val] :=
  (C.frontierWord_get s (i.cast (C.frontierWord_length s))).symm

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (RibbonConnectivity.Component G.circuitStep G.pairing.perm))

include hEuler in
theorem frontier_iff (s : Bool) (a : G.Dart) :
    C.Frontier s a ↔ C.OnCircuitVertex a.vertex ∧ ¬ C.Marked a ∧ C.OnSide s a :=
  C.sector_frontier_iff hEuler s a

include hEuler in
theorem mem_frontierDarts_iff (s : Bool) (a : G.Dart) :
    a ∈ C.frontierDarts s ↔ C.OnCircuitVertex a.vertex ∧ ¬ C.Marked a ∧ C.OnSide s a := by
  rw [C.mem_frontierDarts, C.frontier_iff hEuler]

end ThomGame.Pictures.PortGraph.SimpleCircuit
