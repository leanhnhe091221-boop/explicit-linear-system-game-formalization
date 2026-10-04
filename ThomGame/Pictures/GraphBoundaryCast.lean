module

public import ThomGame.Pictures.BottomBoundaryGraph
public import ThomGame.Pictures.BoundarySwapGraph

/-! # Transport along equal boundary words, with explicit port equivalence -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v u' v' : List S}
  (G : PortGraph P u v) (hu : u = u') (hv : v = v')

theorem swapBoundary_sign : G.swapBoundary.sign = G.sign := rfl

theorem bottomTop_sign {w : List S} (B : PortGraph P [] w) : B.bottomTopGraph.sign = B.sign := rfl

def cast : PortGraph P u' v' := hu ▸ hv ▸ G

def castPorts : G.Dart ≃ (G.cast hu hv).Dart := by
  subst u' v'
  exact Equiv.refl _

theorem castPorts_top (j : Fin u.length) :
    G.castPorts hu hv (.top j) = .top (finCongr (congrArg List.length hu) j) := by
  subst u' v'
  rfl

theorem castPorts_bottom (j : Fin v.length) :
    G.castPorts hu hv (.bottom j) = .bottom (finCongr (congrArg List.length hv) j) := by
  subst u' v'
  rfl

theorem castPorts_label (a : G.Dart) :
    Port.label (G.cast hu hv).jointLabel (G.castPorts hu hv a) = Port.label G.jointLabel a := by
  subst u' v'
  rfl

theorem castPorts_pairing (a : G.Dart) :
    (G.cast hu hv).pairing.perm (G.castPorts hu hv a) = G.castPorts hu hv (G.pairing.perm a) := by
  subst u' v'
  rfl

theorem castPorts_rotation (a : G.Dart) :
    (G.cast hu hv).rotation (G.castPorts hu hv a) = G.castPorts hu hv (G.rotation a) := by
  subst u' v'
  rfl

theorem cast_hub_relations :
    (∑ h : (G.cast hu hv).Hub, ([(G.cast hu hv).hubLabel h] : Multiset R)) =
      ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) := by
  subst u' v'
  rfl

theorem cast_hub_card : Fintype.card (G.cast hu hv).Hub = Fintype.card G.Hub := by
  subst u' v'
  rfl

theorem cast_sign : (G.cast hu hv).sign = G.sign := by
  subst u' v'
  rfl

theorem cast_noJoints (h : IsEmpty G.Joint) : IsEmpty (G.cast hu hv).Joint := by
  subst u' v'
  exact h

theorem cast_eulerDefect :
    eulerDefect (G.cast hu hv).pairing.perm (G.cast hu hv).circuitStep =
      eulerDefect G.pairing.perm G.circuitStep := by
  subst u' v'
  rfl

theorem cast_boundaryNoncrossing (h : G.BoundaryNoncrossing) :
    (G.cast hu hv).BoundaryNoncrossing := by
  subst u' v'
  exact h

theorem cast_boundarySeesComponents (h : G.BoundarySeesComponents) :
    (G.cast hu hv).BoundarySeesComponents := by
  subst u' v'
  exact h

end ThomGame.Pictures.PortGraph
