module

public import ThomGame.Pictures.DiagramBoundaryMoves

/-!
# Relabelling and deleting the edges and relation vertices of diagrams

Local relation diagrams extend by the actual diagram constructors.
Their labels are precisely the retained images of the original labels,
up to permutation. Thus relabelling never increases relation-vertex size.
The target sign is computed from the retained target labels; it is not
assumed to equal the original sign.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S T U : Type*} {P : InvolutionPresentation R S} {Q : InvolutionPresentation T U}

namespace Diagram

theorem exists_empty_of_even_monochromatic (w : List U) (he : Even w.length)
    (hm : ∀ a ∈ w, ∀ b ∈ w, a = b) :
    ∃ d : Diagram Q w [], d.labels = [] := by
  cases w with
  | nil => exact ⟨.identity [], rfl⟩
  | cons a w =>
    have hw : a :: w = List.replicate (a :: w).length a :=
      List.eq_replicate_of_mem (fun b hb => hm b hb a (by simp))
    obtain ⟨n, hn⟩ := he
    have hb : List.replicate n a ++ (List.replicate n a).reverse = a :: w := by
      rw [List.reverse_replicate, ← List.replicate_add, ← hn, ← hw]
    exact ⟨(capWord Q (List.replicate n a)).cast hb rfl, by rw [labels_cast, labels_capWord]⟩

end Diagram

structure Relabelling (P : InvolutionPresentation R S) (Q : InvolutionPresentation T U) where
  vertex : R → Option T
  edge : S → Option U
  relation : ∀ r, Diagram Q ((P.word r).filterMap edge) []
  labels_relation : ∀ r, (relation r).labels = (vertex r).toList

namespace Relabelling

variable (f : Relabelling P Q)

def cap (s : S) : Diagram Q ([s, s].filterMap f.edge) [] :=
  match he : f.edge s with
  | none => (Diagram.identity []).cast (by simp [he]) rfl
  | some t => (Diagram.cap t).cast (by simp [he]) rfl

theorem labels_cap (s : S) : (f.cap s).labels = [] := by
  unfold cap
  split <;> simp [Diagram.labels_cast, Diagram.labels]

def diagram : {u v : List S} → Diagram P u v → Diagram Q (u.filterMap f.edge) (v.filterMap f.edge)
  | _, _, .identity w => .identity (w.filterMap f.edge)
  | _, _, .cap s => f.cap s
  | _, _, .cup s => (f.cap s).adjoint
  | _, _, .down r => f.relation r
  | _, _, .up r => (f.relation r).adjoint
  | _, _, .comp d e => (diagram d).comp (diagram e)
  | _, _, .tensor d e => ((diagram d).tensor (diagram e)).cast
      (by rw [List.filterMap_append]) (by rw [List.filterMap_append])

theorem labels_diagram_perm {u v : List S} (d : Diagram P u v) :
    (f.diagram d).labels.Perm (d.labels.filterMap f.vertex) := by
  induction d with
  | identity w => exact .refl []
  | cap s => simpa only [diagram, Diagram.labels, List.filterMap_nil, labels_cap] using List.Perm.refl ([] : List T)
  | cup s =>
    simpa only [diagram, Diagram.labels, List.filterMap_nil, labels_cap] using (f.cap s).labels_adjoint_perm
  | down r =>
    cases hv : f.vertex r <;>
      simp [diagram, f.labels_relation, Diagram.labels, hv]
  | up r =>
    cases hv : f.vertex r <;>
      simpa [diagram, Diagram.labels, List.filterMap_cons, f.labels_relation, hv] using
        (f.relation r).labels_adjoint_perm
  | comp d e ihd ihe =>
    simpa only [diagram, Diagram.labels, List.filterMap_append] using ihd.append ihe
  | tensor d e ihd ihe =>
    simpa only [diagram, Diagram.labels_cast, Diagram.labels, List.filterMap_append] using ihd.append ihe

theorem size_diagram {u v : List S} (d : Diagram P u v) :
    (f.diagram d).size = (d.labels.filterMap f.vertex).length :=
  (f.labels_diagram_perm d).length_eq

theorem size_diagram_le {u v : List S} (d : Diagram P u v) :
    (f.diagram d).size ≤ d.size := by
  rw [f.size_diagram]
  exact List.length_filterMap_le f.vertex d.labels

theorem sign_diagram {u v : List S} (d : Diagram P u v) :
    (f.diagram d).sign = ((d.labels.filterMap f.vertex).map Q.parity).sum :=
  ((f.labels_diagram_perm d).map Q.parity).sum_eq

theorem sign_diagram_zero {u v : List S} (d : Diagram P u v)
    (hz : ∀ r t, f.vertex r = some t → Q.parity t = 0) : (f.diagram d).sign = 0 := by
  rw [f.sign_diagram]
  have he : ((d.labels.filterMap f.vertex).map Q.parity) =
      List.replicate (d.labels.filterMap f.vertex).length 0 := by
    apply List.map_eq_replicate_iff.mpr
    intro t ht
    obtain ⟨r, _, hr⟩ := List.mem_filterMap.mp ht
    exact hz r t hr
  rw [he]
  simp

theorem filterMap_eq_of_fixed {w : List S} (f : S → Option S)
    (hw : ∀ s ∈ w, f s = some s) : w.filterMap f = w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    rw [List.filterMap_cons, hw s (by simp)]
    change s :: w.filterMap f = s :: w
    congr 1
    exact ih (fun t ht => hw t (by simp [ht]))

end Relabelling
end ThomGame.Pictures
