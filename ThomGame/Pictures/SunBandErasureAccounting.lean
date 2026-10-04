module

public import ThomGame.Pictures.SunBandExternalPorts
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact hub and parity accounting for the proposed cycle erasure

The selected vertices are the actual distinct hubs of the circuit.
Removing all of them strictly decreases size, and the actual spoke
matching proves that every hub-label weight in ZMod 2 is unchanged.
The graph and planar diagram realizing this erasure are separate work.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open scoped Classical BigOperators

section General

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} [IsEmpty G.Joint] (C : G.SimpleCircuit)

abbrev ErasedCircuitHub := {h : G.Hub // h ∉ Set.range C.hubAt}

theorem erasedCircuitHub_sum {M : Type*} [AddCommMonoid M] (f : G.Hub → M) :
    (∑ h : C.ErasedCircuitHub, f h.val) + (∑ k : Fin C.length, f (C.hubAt k)) = ∑ h : G.Hub, f h := by
  let : Fintype {h : G.Hub // h ∈ Set.range C.hubAt} :=
    Subtype.fintype (fun h => h ∈ Set.range C.hubAt)
  have hs := Fintype.sum_subtype_add_sum_subtype (fun h => h ∈ Set.range C.hubAt) f
  have he := C.hubAtRangeEquiv.sum_comp (fun h => f h.val)
  change (∑ k : Fin C.length, f (C.hubAt k)) = _ at he
  exact (add_comm _ _).trans
    ((congrArg (fun z : M => z + (∑ h : C.ErasedCircuitHub, f h.val)) he).trans hs)

theorem erasedCircuitHub_card : Fintype.card C.ErasedCircuitHub + C.length = Fintype.card G.Hub := by
  simpa using C.erasedCircuitHub_sum (fun _ => (1 : Nat))

theorem erasedCircuitHub_card_lt : Fintype.card C.ErasedCircuitHub < Fintype.card G.Hub := by
  have hn := C.erasedCircuitHub_card
  have hp := C.length_pos
  omega

end General

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (hn : 3 ≤ n) (i : Fin n)
  (hband : ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)))

include hn hband in
theorem sunBand_sum_weight_zero (χ : Fin n → ZMod 2) :
    (∑ k : Fin C.length, χ (G.hubLabel (C.hubAt k))) = 0 :=
  (C.sunBandSpokePairing hn i hband).sum_charge χ

include hn hband in
theorem sunBand_erased_weight (χ : Fin n → ZMod 2) :
    (∑ h : C.ErasedCircuitHub, χ (G.hubLabel h.val)) = ∑ h : G.Hub, χ (G.hubLabel h) := by
  have hs := C.erasedCircuitHub_sum (fun h => χ (G.hubLabel h))
  rw [C.sunBand_sum_weight_zero hn i hband χ, add_zero] at hs
  exact hs

noncomputable def sunBandLabelPairing (r : Fin n) :
    Pairing (fun k : {k : Fin C.length // G.hubLabel (C.hubAt k) = r} => G.hubLabel (C.hubAt k.val)) :=
  (C.sunBandSpokePairing hn i hband).restrict (fun k => G.hubLabel (C.hubAt k) = r)
    (fun k hk => (C.sunBandPartner_label hn i hband k).trans hk)

include hn hband in
theorem sunBand_label_count_even (r : Fin n) :
    Even (Fintype.card {k : Fin C.length // G.hubLabel (C.hubAt k) = r}) := by
  refine ⟨Fintype.card (C.sunBandLabelPairing hn i hband r).Edge, ?_⟩
  simpa only [two_mul] using (C.sunBandLabelPairing hn i hband r).dart_card_eq_twice_edge_card

end ThomGame.Pictures.PortGraph.SimpleCircuit
