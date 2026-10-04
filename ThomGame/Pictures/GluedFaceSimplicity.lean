module

public import ThomGame.Pictures.GluedFaceProjection
public import ThomGame.Pictures.FacialOrbitSimplicity

/-! # A lifted facial orbit remains simple at old vertices and new seam joints -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
  (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm)) (s : Bool)

theorem gluedFaceProjection_injective_retained {x y : (C.gluedGraph hEuler s).Dart}
    (hx : C.GluedRetained hEuler s x) (hy : C.GluedRetained hEuler s y)
    (he : C.gluedFaceProjection hEuler s x = C.gluedFaceProjection hEuler s y) : x = y := by
  rw [C.gluedFaceProjection_retained hEuler s x hx, C.gluedFaceProjection_retained hEuler s y hy] at he
  have he' : (C.gluedComponentPorts hEuler s ⟨x, hx⟩).val =
      (C.gluedComponentPorts hEuler s ⟨y, hy⟩).val := by
    rw [C.gluedComponentPorts_val, C.gluedComponentPorts_val]
    exact he
  exact congrArg Subtype.val ((C.gluedComponentPorts hEuler s).injective (Subtype.ext he'))

theorem gluedFaceProjection_vertex_retained {x y : (C.gluedGraph hEuler s).Dart}
    (hx : C.GluedRetained hEuler s x) (hv : x.vertex = y.vertex) :
    C.GluedRetained hEuler s y ∧
      (C.gluedFaceProjection hEuler s x).vertex = (C.gluedFaceProjection hEuler s y).vertex := by
  have hr := ((C.gluedGraph hEuler s).rotation_sameCycle_iff x y).mpr hv
  have h := predicate_of_sameCycle (C.gluedGraph hEuler s).rotation
    (fun z => C.GluedRetained hEuler s z ∧
      G.rotation.SameCycle (C.gluedFaceProjection hEuler s x) (C.gluedFaceProjection hEuler s z))
    (fun z hz => And.intro ((C.gluedRetained_rotation hEuler s z).mpr hz.1)
      (by rw [C.gluedFaceProjection_rotation_retained hEuler s z hz.1]; exact hz.2.apply_right))
    hr ⟨hx, Equiv.Perm.SameCycle.rfl⟩
  exact ⟨h.1, (G.rotation_sameCycle_iff _ _).mp h.2⟩

variable (D : G.SimpleCircuit) (side : Bool) (hf : D.BoundsFaceOrbit side)

include hf in
theorem gluedFace_vertex_injective {x y : (C.gluedGraph hEuler s).Dart}
    (hx : G.circuitStep.SameCycle (C.gluedFaceProjection hEuler s x) (D.port (0, side)))
    (hy : G.circuitStep.SameCycle (C.gluedFaceProjection hEuler s y) (D.port (0, side)))
    (hv : x.vertex = y.vertex) : x = y := by
  by_cases hret : C.GluedRetained hEuler s x
  · obtain ⟨hyret, hxy⟩ := C.gluedFaceProjection_vertex_retained hEuler s hret hv
    exact C.gluedFaceProjection_injective_retained hEuler s hret hyret
      (D.face_vertex_injective side hf hx hy hxy)
  · rw [C.gluedRetained_iff] at hret
    cases x with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub h i => exact (hret trivial).elim
    | joint j b =>
      rcases j with (j | j) | i
      · exact (hret trivial).elim
      · exact (hret trivial).elim
      · cases y with
        | top k => exact k.elim0
        | bottom k => exact k.elim0
        | hub h k => cases hv
        | joint k c =>
          rcases k with (k | k) | k
          · cases hv
          · cases hv
          · have hik : i = k := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj hv))
            subst k
            by_cases hbc : b = c
            · subst c; rfl
            · have he : C.gluedFaceProjection hEuler s (.joint (.inr i) c) =
                  G.pairing.twin (C.gluedFaceProjection hEuler s (.joint (.inr i) b)) := by
                cases b <;> cases c
                · exact (hbc rfl).elim
                · exact (G.pairing.involutive (C.boundaryEnumeration (!s) i).val).symm
                · rfl
                · exact (hbc rfl).elim
              exact (D.face_excludes_twin side hf hx (he ▸ hy)).elim

include hf in
theorem gluedFace_rotation_ne_self (x : (C.gluedGraph hEuler s).Dart)
    (hx : G.circuitStep.SameCycle (C.gluedFaceProjection hEuler s x) (D.port (0, side))) :
    (C.gluedGraph hEuler s).rotation x ≠ x := by
  intro he
  by_cases hret : C.GluedRetained hEuler s x
  · have hr := C.gluedFaceProjection_rotation_retained hEuler s x hret
    rw [he] at hr
    exact D.face_rotation_ne_self side hf hx hr.symm
  · rw [C.gluedRetained_iff] at hret
    cases x with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub h i => exact hret trivial
    | joint j b =>
      rcases j with (j | j) | i
      · exact hret trivial
      · exact hret trivial
      · cases b <;> cases he

end ThomGame.Pictures.PortGraph.SimpleCircuit
