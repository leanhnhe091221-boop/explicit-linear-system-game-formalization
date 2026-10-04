module

public import ThomGame.Pictures.GraphCharge
public import ThomGame.Finite.HypergraphCycles

/-!
# Character of closed sun diagrams

Each sun vertex has its own spoke. Charging just that spoke determines
the parity of the number of occurrences of that vertex from the boundary.
Every closed diagram therefore has zero character, as in Slofstra Lemma
10.3. The proof does not assume the facial normalization of sun pictures.
-/

@[expose] public section
namespace ThomGame.Pictures

open scoped BigOperators

def sunPresentation (n : Nat) (b : Fin n → ZMod 2) :
    InvolutionPresentation (Fin n) (Fin n ⊕ Fin n) where
  word j := [Sum.inl j, Sum.inr j, Sum.inr (finRotate n j)]
  parity := b

theorem sunPresentation_incidence (n : Nat) (b : Fin n → ZMod 2) (j : Fin n) :
    ((sunPresentation n b).word j : Multiset (Fin n ⊕ Fin n)) =
      (Hypergraph.sun n).incidence j := rfl

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}

theorem Diagram.sun_character (d : Diagram (sunPresentation n b) u v) (j : Fin n) :
    d.character j = (u.count (.inl j) : ZMod 2) + (v.count (.inl j) : ZMod 2) := by
  let χ : Fin n ⊕ Fin n → ZMod 2 := fun e => if e = .inl j then 1 else 0
  have hw (i : Fin n) : (((sunPresentation n b).word i).map χ).sum = if i = j then 1 else 0 := by
    simp [sunPresentation, χ]
  have h := d.charge_balance χ
  simp_rw [hw] at h
  change (d.labels.map (fun i => if i = j then (1 : ZMod 2) else 0)).sum =
    (u.map (fun e => if e = .inl j then (1 : ZMod 2) else 0)).sum +
      (v.map (fun e => if e = .inl j then (1 : ZMod 2) else 0)).sum at h
  rw [sum_indicator_eq_count, sum_indicator_eq_count, sum_indicator_eq_count] at h
  exact h

theorem Diagram.closed_sun_character (d : Diagram (sunPresentation n b) [] []) (j : Fin n) :
    d.character j = 0 := by simpa using d.sun_character j

theorem Diagram.closed_sun_sign (d : Diagram (sunPresentation n b) [] []) : d.sign = 0 := by
  rw [d.sign_eq_character]
  simp [d.closed_sun_character]

theorem PortGraph.sun_character (G : PortGraph (sunPresentation n b) u v) (j : Fin n) :
    G.character j = (u.count (.inl j) : ZMod 2) + (v.count (.inl j) : ZMod 2) := by
  let χ : Fin n ⊕ Fin n → ZMod 2 := fun e => if e = .inl j then 1 else 0
  have hw (i : Fin n) : (((sunPresentation n b).word i).map χ).sum = if i = j then 1 else 0 := by
    simp [sunPresentation, χ]
  have h := G.charge_balance χ
  simp_rw [hw] at h
  change (∑ h : G.Hub, if G.hubLabel h = j then (1 : ZMod 2) else 0) =
    (u.map (fun e => if e = .inl j then (1 : ZMod 2) else 0)).sum +
      (v.map (fun e => if e = .inl j then (1 : ZMod 2) else 0)).sum at h
  rw [sum_indicator_eq_count, sum_indicator_eq_count] at h
  rw [G.character_eq_sum]
  exact h

theorem PortGraph.closed_sun_character (G : PortGraph (sunPresentation n b) [] []) (j : Fin n) :
    G.character j = 0 := by simpa using G.sun_character j

theorem PortGraph.closed_sun_sign (G : PortGraph (sunPresentation n b) [] []) : G.sign = 0 := by
  rw [G.sign_eq_character]
  simp [G.closed_sun_character]

end ThomGame.Pictures
