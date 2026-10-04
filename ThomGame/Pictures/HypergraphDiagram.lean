module

public import ThomGame.Pictures.DiagramRelabel
public import ThomGame.Pictures.SunCharacter

/-!
# Generalized hypergraph maps act on diagrams with trivalent target

Retained rows are realized by one target vertex with a suitable cyclic
order or reversal. Deleted rows are joined by caps, using their even
monochromatic incidence condition. This constructs diagrams with the
actual filtered boundary and retained relation labels, as in the
trivalent instance of Slofstra Proposition 8.13.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S T U : Type*} {P : InvolutionPresentation R S} {Q : InvolutionPresentation T U}
  {H : Hypergraph R S} {K : Hypergraph T U}

theorem exists_relation_image (φ : H.GeneralizedHom K)
    (hP : ∀ r, (P.word r : Multiset S) = H.incidence r)
    (hQ : ∀ t, (Q.word t : Multiset U) = K.incidence t)
    (hthree : ∀ t, (Q.word t).length = 3) (r : R) :
    ∃ d : Diagram Q ((P.word r).filterMap φ.edge) [], d.labels = (φ.vertex r).toList := by
  cases hv : φ.vertex r with
  | none =>
    have hd := φ.deleted r hv
    rw [← hP r, Multiset.filterMap_coe] at hd
    have he : Even ((P.word r).filterMap φ.edge).length := hd.1
    have hm : ∀ a ∈ (P.word r).filterMap φ.edge,
        ∀ b ∈ (P.word r).filterMap φ.edge, a = b := hd.2
    obtain ⟨d, hd⟩ := Diagram.exists_empty_of_even_monochromatic _ he hm (Q := Q)
    exact ⟨d, by simpa [hv] using hd⟩
  | some t =>
    have hp : ((P.word r).filterMap φ.edge).Perm (Q.word t) := by
      apply Multiset.coe_eq_coe.mp
      rw [← Multiset.filterMap_coe, hP, φ.retained r t hv, hQ]
    obtain ⟨a, b, c, ht⟩ := List.length_eq_three.mp (hthree t)
    let star : Diagram Q [a, b, c] [] := (Diagram.down t).cast ht rfl
    obtain ⟨d, hd⟩ := star.exists_permuted_triangle (ht ▸ hp)
    have hd' : d.labels.Perm [t] := by
      simpa only [star, Diagram.labels_cast, Diagram.labels] using hd
    exact ⟨d, by simpa [hv] using hd'⟩

noncomputable def Relabelling.ofGeneralizedHom (φ : H.GeneralizedHom K)
    (hP : ∀ r, (P.word r : Multiset S) = H.incidence r)
    (hQ : ∀ t, (Q.word t : Multiset U) = K.incidence t)
    (hthree : ∀ t, (Q.word t).length = 3) : Relabelling P Q where
  vertex := φ.vertex
  edge := φ.edge
  relation r := Classical.choose (exists_relation_image φ hP hQ hthree r)
  labels_relation r := Classical.choose_spec (exists_relation_image φ hP hQ hthree r)

noncomputable def Relabelling.toSun {n : Nat} (φ : H.GeneralizedHom (Hypergraph.sun n))
    (hP : ∀ r, (P.word r : Multiset S) = H.incidence r) (b : Fin n → ZMod 2) :
    Relabelling P (sunPresentation n b) :=
  .ofGeneralizedHom φ hP (sunPresentation_incidence n b) (fun _ => rfl)

end ThomGame.Pictures
