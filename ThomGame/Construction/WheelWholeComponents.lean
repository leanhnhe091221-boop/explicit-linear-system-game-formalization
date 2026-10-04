module

public import ThomGame.Construction.WheelAllFacialCopies
public import ThomGame.Pictures.WheelComponentClassification

/-!
# Whole-wheel components in the actual numbered Sigma normal form

The auxiliary-edge component of every hub is a single complete wheel.
The original numbered row labels have one preimage each, its hub count
is three times the wheel length, and its rhs sum is the original relation
parity. No disk boundary or wheel-collapse theorem is assumed here.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph
open scoped BigOperators

variable (H : SigmaGraph [] []) [IsEmpty H.Joint]

abbrev SigmaAuxiliaryConnected : H.Hub → H.Hub → Prop :=
  wheelFamily.AuxiliaryConnected rowEquiv colEquiv H

theorem sigma_whole_wheel_component
    (hf : ∀ i : WheelCycleIndex, SigmaRimsFacialCopies H i)
    (h : H.Hub) (r : WheelIndex) (j : Fin (wheelFamily.size r)) (k : Fin 3)
    (hh : H.hubLabel h = rowEquiv ⟨r, j, k⟩) :
    wheelFamily.WholeWheelComponent rowEquiv colEquiv H r h := by
  have hlen : 3 ≤ wheelFamily.size r := Nat.le_trans (by decide : 3 ≤ 4) (wheelWord_length_ge_four r)
  have hb : ∀ a : H.RimDart (wheelFamily.reindexedCentralCycle rowEquiv colEquiv r hlen),
      (H.rimSimpleCircuit _
        (wheelFamily.reindexedCentralCycle rowEquiv colEquiv r hlen).empty_boundary_no_rim
        (wheelFamily.reindexedCentralCycle rowEquiv colEquiv r hlen).empty_boundary_no_rim a).IsLabelCopy :=
    fun a => (hf (.inl r) a).2
  have hp : ∀ (j : Fin (wheelFamily.size r))
      (a : H.RimDart (wheelFamily.reindexedPentagonCycle rowEquiv colEquiv r j)),
      (H.rimSimpleCircuit _
        (wheelFamily.reindexedPentagonCycle rowEquiv colEquiv r j).empty_boundary_no_rim
        (wheelFamily.reindexedPentagonCycle rowEquiv colEquiv r j).empty_boundary_no_rim a).IsLabelCopy :=
    fun j a => (hf (.inr ⟨r, j⟩) a).2
  exact wheelFamily.component_one_hub_per_row rowEquiv colEquiv H r hlen hb hp h j k hh

theorem sigma_every_hub_in_whole_wheel
    (hf : ∀ i : WheelCycleIndex, SigmaRimsFacialCopies H i) (h : H.Hub) :
    ∃ r : WheelIndex, wheelFamily.WholeWheelComponent rowEquiv colEquiv H r h := by
  exact wheelFamily.every_hub_in_whole_wheel rowEquiv colEquiv H
    (fun r => Nat.le_trans (by decide : 3 ≤ 4) (wheelWord_length_ge_four r))
    (fun r a => (hf (.inl r) a).2) (fun r j a => (hf (.inr ⟨r, j⟩) a).2) h

theorem J_sigma_eq_one_iff_whole_wheel_normal_form :
    J_sigma = 1 ↔ ∃ H : SigmaGraph [] [], IsEmpty H.Joint ∧
      RibbonConnectivity.eulerDefect H.pairing.perm H.circuitStep = 0 ∧ H.sign = 1 ∧
      (∀ i : WheelCycleIndex, SigmaRimsFacialCopies H i) ∧
      ∀ h : H.Hub, ∃ r : WheelIndex, wheelFamily.WholeWheelComponent rowEquiv colEquiv H r h := by
  constructor
  · intro hj
    obtain ⟨H, hJ, he, hs, hf⟩ := J_sigma_eq_one_iff_all_facial_copies.mp hj
    let : IsEmpty H.Joint := hJ
    exact ⟨H, hJ, he, hs, hf, sigma_every_hub_in_whole_wheel H hf⟩
  · rintro ⟨H, hJ, he, hs, hf, _⟩
    exact J_sigma_eq_one_iff_all_facial_copies.mpr ⟨H, hJ, he, hs, hf⟩

end ThomGame.Construction
