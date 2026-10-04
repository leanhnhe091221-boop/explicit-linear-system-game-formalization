module

public import ThomGame.Pictures.SunRimCover

/-!
# Actual finite inward-switch traces terminate in facial rim covers

Each rim is one original face orbit and every rim edge joins distinct
hub labels, the covering condition of Definition 7.7. This theorem keeps
the original smoothing and its circle records; it makes no additional
geometric placement or structural replacement assertion.
-/

@[expose] public section
namespace ThomGame.Pictures

open scoped BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  (hn : 3 ≤ n) (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

namespace PortGraph

def SunRimsFacialCovers (G : PortGraph (sunPresentation n b) [] w) : Prop :=
  ∀ a : G.SunRimDart hn,
    (∃ side, (G.sunRimSimpleCircuit hn (by simp) hw a).BoundsFaceOrbit side) ∧
      (G.sunRimSimpleCircuit hn (by simp) hw a).IsLabelCover

theorem SunFaceState.facial_covers {G : PortGraph (sunPresentation n b) [] w}
    (H : G.SunFaceState hn hw) : G.SunRimsFacialCovers hn hw := H.rims_facial_covers hn hw

end PortGraph

namespace Smoothing

theorem exists_sun_facial_cover_switches {d : Diagram (sunPresentation n b) [] w}
    {G : PortGraph (sunPresentation n b) [] w} [IsEmpty G.Joint] {cs : List (Fin n ⊕ Fin n)}
    (t : Smoothing d.graph G cs) (hm : d.CharacterMinimal) :
    ∃ (H : PortGraph (sunPresentation n b) [] w) (q : PortGraph.SunSwitchTrace G H),
      q.Inward hn hw ∧ H.SunFaceState hn hw ∧ H.SunRimsFacialCovers hn hw ∧
      (∑ h : H.Hub, ([H.hubLabel h] : Multiset (Fin n))) = (d.labels : Multiset (Fin n)) ∧
      Fintype.card H.Hub = d.size ∧ H.sign = d.sign ∧
      H.boundaryNext = d.graph.boundaryNext ∧
      q.length ≤ G.sunTotalInteriorSpokeCount hn (by simp) hw
        (t.sunMinimalState hm).euler (t.sunMinimalState hm).sees
        (t.sun_rim_meetsBoundary hm hn (by simp) hw) := by
  obtain ⟨H, q, hq, hH, hl, hc, hs, hb, hlen⟩ := t.exists_sun_face_switches hn hw hm
  exact ⟨H, q, hq, hH, hH.facial_covers hn hw, hl, hc, hs, hb, hlen⟩

end Smoothing
end ThomGame.Pictures
