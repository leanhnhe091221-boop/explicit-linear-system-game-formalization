module

public import ThomGame.Pictures.WheelLiftComponents
public import ThomGame.Pictures.FacialRimHubOrientation

/-!
# Facial central and pentagon rims orient every lifted wheel coherently

The actual b and c edges propagate the local hub flip to the central
ring. The facial central ring propagates it through all positions. Thus
all three types of hubs in the wheel have one common orientation.
-/

@[expose] public section
namespace ThomGame.Wheel.Family.GraphLift

open Pictures PortGraph Equiv

variable {R V R' V' : Type*} [DecidableEq R] [DecidableEq V]
  [DecidableEq R'] [DecidableEq V'] {F : Family R V}
  {rows : F.Row ≃ R'} {cols : F.Col ≃ V'}
  {G : SolutionGroup.RowGraph (F.system.reindex rows cols) [] []}
  {r : R} (L : F.GraphLift rows cols G r)

omit [DecidableEq R] [DecidableEq V] [DecidableEq R'] [DecidableEq V'] in
theorem port_label (j : Fin (F.size r)) (k p : Fin 3) :
    Port.label G.jointLabel (.hub (L.hub j k) p : G.Dart) = cols (F.columns r j k p) := by
  rw [SolutionGroup.rowGraph_port_label, L.label, SparseSystem.reindex_column]
  rfl

variable [IsEmpty G.Joint] (hlen : 3 ≤ F.size r)
  (hb : ∀ a : G.RimDart (F.reindexedCentralCycle rows cols r hlen),
    ∃ side, (G.rimSimpleCircuit _ (F.reindexedCentralCycle rows cols r hlen).empty_boundary_no_rim
      (F.reindexedCentralCycle rows cols r hlen).empty_boundary_no_rim a).BoundsFaceOrbit side)
  (hp : ∀ (j : Fin (F.size r)) (a : G.RimDart (F.reindexedPentagonCycle rows cols r j)),
    ∃ side, (G.rimSimpleCircuit _ (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim
      (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim a).BoundsFaceOrbit side)

include hb in
theorem central_flip_prev (j : Fin (F.size r)) :
    G.hubFlip (L.hub ((finRotate (F.size r)).symm j) 2) = G.hubFlip (L.hub j 2) := by
  have hm (i : Fin (F.size r)) :
      Port.label G.jointLabel (.hub (L.hub i 2) (1 : Fin 3) : G.Dart) ∈
        Set.range (F.reindexedCentralCycle rows cols r hlen).edge ∧
      Port.label G.jointLabel (.hub (L.hub i 2) (2 : Fin 3) : G.Dart) ∈
        Set.range (F.reindexedCentralCycle rows cols r hlen).edge := by
    rw [L.port_label, L.port_label]
    exact ⟨⟨i, rfl⟩, ⟨finRotate (F.size r) i, rfl⟩⟩
  apply G.hubFlip_eq_of_facial_rim_step _ hb _ _ 2 2
    (hm _).2 (hm _).1 (hm _).2 (hm _).1
  exact (congrArg G.pairing.twin (L.twin_d j)).symm.trans (G.pairing.involutive _)

include hp in
theorem layer_flips (j : Fin (F.size r)) :
    G.hubFlip (L.hub j 0) = G.hubFlip (L.hub j 1) ∧
      G.hubFlip (L.hub j 1) = G.hubFlip (L.hub j 2) := by
  let γ := F.reindexedPentagonCycle rows cols r j
  have h01 : Port.label G.jointLabel (.hub (L.hub j 0) (1 : Fin 3) : G.Dart) ∈ Set.range γ.edge :=
    ⟨0, (L.port_label j 0 1).symm⟩
  have h02 : Port.label G.jointLabel (.hub (L.hub j 0) (2 : Fin 3) : G.Dart) ∈ Set.range γ.edge :=
    ⟨1, (L.port_label j 0 2).symm⟩
  have h10 : Port.label G.jointLabel (.hub (L.hub j 1) (0 : Fin 3) : G.Dart) ∈ Set.range γ.edge :=
    ⟨1, (L.port_label j 1 0).symm⟩
  have h11 : Port.label G.jointLabel (.hub (L.hub j 1) (1 : Fin 3) : G.Dart) ∈ Set.range γ.edge :=
    ⟨2, (L.port_label j 1 1).symm⟩
  have h20 : Port.label G.jointLabel (.hub (L.hub j 2) (0 : Fin 3) : G.Dart) ∈ Set.range γ.edge :=
    ⟨2, (L.port_label j 2 0).symm⟩
  have h21 : Port.label G.jointLabel (.hub (L.hub j 2) (1 : Fin 3) : G.Dart) ∈ Set.range γ.edge :=
    ⟨3, (L.port_label j 2 1).symm⟩
  exact ⟨G.hubFlip_eq_of_facial_rim_step γ (hp j) _ _ 2 1 h02 h01 h11 h10 (L.twin_b j),
    G.hubFlip_eq_of_facial_rim_step γ (hp j) _ _ 1 1 h11 h10 h21 h20 (L.twin_c j)⟩

include hb in
theorem central_flips (i j : Fin (F.size r)) :
    G.hubFlip (L.hub i 2) = G.hubFlip (L.hub j 2) := by
  have step (k : Fin (F.size r)) :
      G.hubFlip (L.hub k 2) = G.hubFlip (L.hub (finRotate (F.size r) k) 2) := by
    simpa only [symm_apply_apply] using L.central_flip_prev hlen hb (finRotate (F.size r) k)
  obtain ⟨n, hn⟩ := (finRotate_sameCycle i j).exists_nat_pow_eq
  rw [← hn]
  clear hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (step _)

include hb hp in
theorem hubFlip_eq (i j : Fin (F.size r)) (k l : Fin 3) :
    G.hubFlip (L.hub i k) = G.hubFlip (L.hub j l) := by
  have layer (a : Fin (F.size r)) (b : Fin 3) :
      G.hubFlip (L.hub a b) = G.hubFlip (L.hub a 2) := by
    have hh := L.layer_flips hp a
    fin_cases b
    · exact hh.1.trans hh.2
    · exact hh.2
    · rfl
  exact (layer i k).trans ((L.central_flips hlen hb i j).trans (layer j l).symm)

include hb hp in
theorem exists_uniform_orientation :
    ∃ b : Bool, ∀ (j : Fin (F.size r)) (k : Fin 3), G.hubFlip (L.hub j k) = b :=
  ⟨G.hubFlip (L.hub 0 0), fun j k => L.hubFlip_eq hlen hb hp j 0 k 0⟩

end ThomGame.Wheel.Family.GraphLift
