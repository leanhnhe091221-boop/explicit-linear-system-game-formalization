module

public import ThomGame.Pictures.RowEdgeSwitchEuler
public import ThomGame.Pictures.RimTotalCount
public import ThomGame.Pictures.PairingSwitchComponentCounts

/-!
# Exact rim counts of the actual row edge reconnection

Restriction to a base cycle commutes with the same-label port exchange.
The local vertex pairing stays fixed. An oriented cut increases that
cycle's component count by one; cycles avoiding the cut label have
identical pairings and identical component quotients.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowEdgeSwitch

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {u v : List S} {G : SolutionGroup.RowGraph A u v} (s : G.RowEdgeSwitch)
  (γ : Hypergraph.Cycle A.hypergraph)
  (hu : ∀ z ∈ u, z ∉ Set.range γ.edge) (hv : ∀ z ∈ v, z ∉ Set.range γ.edge)

theorem rimVertexPairing_eq : s.graph.rimVertexPairing γ hu hv = G.rimVertexPairing γ hu hv := by
  apply Pairing.ext_twin
  funext x
  exact G.rimSwitch_unique γ hu hv x (s.graph.rimSwitch γ hu hv x)
    (s.graph.rimSwitch_vertex γ hu hv x) (s.graph.rimSwitch_ne_self γ hu hv x)

theorem rimPairing_of_avoids (h : Port.label G.jointLabel s.first ∉ Set.range γ.edge) :
    s.graph.rimPairing γ = G.rimPairing γ := by
  apply Pairing.ext_twin
  funext x
  apply Subtype.ext
  exact s.twin_of_label x.val (fun he => h (he ▸ x.property))

variable (ha : Port.label G.jointLabel s.first ∈ Set.range γ.edge)

noncomputable def rimSwap : Perm (G.RimDart γ) :=
  swap ⟨s.first, ha⟩ ⟨s.second, s.label_eq ▸ ha⟩

theorem rimSwap_val (x : G.RimDart γ) :
    (s.rimSwap γ ha x).val = s.portSwap x.val := by
  exact @Function.Injective.map_swap (G.RimDart γ) G.Dart
    (Classical.typeDecidableEq _) (Classical.typeDecidableEq _)
    Subtype.val Subtype.val_injective ⟨s.first, ha⟩ ⟨s.second, s.label_eq ▸ ha⟩ x

theorem rimPairing_perm :
    (s.graph.rimPairing γ).perm = s.rimSwap γ ha * (G.rimPairing γ).perm * s.rimSwap γ ha := by
  ext x
  apply Subtype.ext
  change s.graph.pairing.twin x.val =
    (s.rimSwap γ ha ((G.rimPairing γ).perm (s.rimSwap γ ha x))).val
  rw [s.rimSwap_val, s.twin]
  change _ = s.portSwap (G.pairing.twin (s.rimSwap γ ha x).val)
  exact congrArg (fun y => s.portSwap (G.pairing.twin y)) (s.rimSwap_val γ ha x).symm

end RowEdgeSwitch

namespace RowEdgeSwitch

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []} (s : G.RowEdgeSwitch)
  (γ : Hypergraph.Cycle A.hypergraph)

theorem rimCount_of_avoids (h : Port.label G.jointLabel s.first ∉ Set.range γ.edge) :
    s.graph.rimCount γ = G.rimCount γ := by
  unfold rimCount RimComponent
  rw [s.rimPairing_of_avoids γ h, s.rimVertexPairing_eq]
  rfl

theorem rimCount_split (ha : Port.label G.jointLabel s.first ∈ Set.range γ.edge)
    (h : (G.rimWalk γ (by simp) (by simp)).SameCycle
      ⟨s.first, ha⟩ ⟨s.second, s.label_eq ▸ ha⟩) :
    s.graph.rimCount γ = G.rimCount γ + 1 := by
  have hab : (⟨s.first, ha⟩ : G.RimDart γ) ≠ ⟨s.second, s.label_eq ▸ ha⟩ :=
    fun he => s.first_ne_second (congrArg Subtype.val he)
  have hc := PairingCycles.switchedEdge_component_card_split
    (G.rimPairing γ) (G.rimVertexPairing γ (by simp) (by simp)) hab h
  unfold rimCount RimComponent
  rw [s.rimVertexPairing_eq, s.rimPairing_perm γ ha]
  exact hc

theorem rimWalk_sameCycle_of_canonical_cuts (a : G.RimDart γ)
    {i k : Fin (G.rimSimpleCircuit γ (by simp) (by simp) a).length}
    (hi : s.first = (G.rimSimpleCircuit γ (by simp) (by simp) a).dart i)
    (hk : s.second = (G.rimSimpleCircuit γ (by simp) (by simp) a).dart k)
    (ha : Port.label G.jointLabel s.first ∈ Set.range γ.edge) :
    (G.rimWalk γ (by simp) (by simp)).SameCycle
      ⟨s.first, ha⟩ ⟨s.second, s.label_eq ▸ ha⟩ := by
  have hfirst : (⟨s.first, ha⟩ : G.RimDart γ) =
      OrbitEnumeration.dart (G.rimWalk γ (by simp) (by simp)) a i := Subtype.ext hi
  have hsecond : (⟨s.second, s.label_eq ▸ ha⟩ : G.RimDart γ) =
      OrbitEnumeration.dart (G.rimWalk γ (by simp) (by simp)) a k := Subtype.ext hk
  rw [hfirst, hsecond]
  exact (OrbitEnumeration.dart_sameCycle _ a i).symm.trans (OrbitEnumeration.dart_sameCycle _ a k)

theorem rimCount_split_of_canonical_cuts (a : G.RimDart γ)
    {i k : Fin (G.rimSimpleCircuit γ (by simp) (by simp) a).length}
    (hi : s.first = (G.rimSimpleCircuit γ (by simp) (by simp) a).dart i)
    (hk : s.second = (G.rimSimpleCircuit γ (by simp) (by simp) a).dart k) :
    s.graph.rimCount γ = G.rimCount γ + 1 := by
  have ha : Port.label G.jointLabel s.first ∈ Set.range γ.edge :=
    hi ▸ G.rimSimpleCircuit_rim γ (by simp) (by simp) a i
  exact s.rimCount_split γ ha (s.rimWalk_sameCycle_of_canonical_cuts γ a hi hk ha)

theorem totalRimCount_split_private {I : Type*} [Fintype I]
    (Φ : I → Hypergraph.Cycle A.hypergraph) (j : I)
    (hsplit : s.graph.rimCount (Φ j) = G.rimCount (Φ j) + 1)
    (hprivate : ∀ k : I, k ≠ j → Port.label G.jointLabel s.first ∉ Set.range (Φ k).edge) :
    s.graph.totalRimCount Φ = G.totalRimCount Φ + 1 := by
  have he (k : I) : s.graph.rimCount (Φ k) = G.rimCount (Φ k) + if k = j then 1 else 0 := by
    by_cases hk : k = j
    · subst k
      rw [ite_eq_left rfl]
      exact hsplit
    · rw [ite_eq_right hk, Nat.add_zero]
      exact s.rimCount_of_avoids (Φ k) (hprivate k hk)
  unfold totalRimCount
  simp only [he, Finset.sum_add_distrib]
  simp

end RowEdgeSwitch
end ThomGame.Pictures.PortGraph
