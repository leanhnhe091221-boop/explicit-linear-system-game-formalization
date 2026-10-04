module

public import ThomGame.Pictures.WheelComponentClassification
public import ThomGame.Pictures.WheelOrdinaryReturn

/-!
# A disjoint atlas of all actual wheel components

The auxiliary-component quotient indexes actual whole-wheel lifts.
Their hub maps partition the original hub set, and their outer ports
give an explicit bijection onto all retained ordinary ports. No wheel
or port is duplicated by the choice of a representative.
-/

@[expose] public section
namespace ThomGame.Wheel.Family

open Pictures PortGraph Equiv
open scoped Classical BigOperators

variable {R V R' V' : Type*} (F : Family R V)
  (rows : F.Row ≃ R') (cols : F.Col ≃ V')
  (G : SolutionGroup.RowGraph (F.system.reindex rows cols) [] [])

def auxiliarySetoid : Setoid G.Hub where
  r := F.AuxiliaryConnected rows cols G
  iseqv := ⟨fun h => Relation.EqvGen.refl h,
    fun {_ _} hh => Relation.EqvGen.symm _ _ hh,
    fun {_ _ _} hh hk => Relation.EqvGen.trans _ _ _ hh hk⟩

structure GraphAtlas where
  Component : Type
  [componentFintype : Fintype Component]
  wheel : Component → R
  lift : (c : Component) → F.GraphLift rows cols G (wheel c)
  cover : ∀ h : G.Hub, ∃ (c : Component) (j : Fin (F.size (wheel c))) (k : Fin 3),
    (lift c).hub j k = h
  disjoint : ∀ (c d : Component) (i : Fin (F.size (wheel c))) (j : Fin (F.size (wheel d)))
    (k l : Fin 3), (lift c).hub i k = (lift d).hub j l → c = d

attribute [instance] GraphAtlas.componentFintype

noncomputable def graphAtlasOfComponents
    (hall : ∀ h : G.Hub, ∃ r : R, F.WholeWheelComponent rows cols G r h) :
    F.GraphAtlas rows cols G := by
  let C := Quotient (F.auxiliarySetoid rows cols G)
  let wheel (c : C) : R := (hall c.out).choose
  let lift (c : C) : F.GraphLift rows cols G (wheel c) := (hall c.out).choose_spec.choose
  have hm (c : C) (h : G.Hub) :
      F.AuxiliaryConnected rows cols G c.out h ↔ (lift c).Contains h :=
    (hall c.out).choose_spec.choose_spec.1 h
  have hclass (c : C) (j : Fin (F.size (wheel c))) (k : Fin 3) :
      Quotient.mk (F.auxiliarySetoid rows cols G) ((lift c).hub j k) = c := by
    have hc := (hm c _).mpr ⟨j, k, rfl⟩
    exact (Quotient.sound hc).symm.trans (Quotient.out_eq c)
  refine {
    Component := C
    componentFintype := Fintype.ofFinite C
    wheel := wheel
    lift := lift
    cover := ?_
    disjoint := ?_ }
  · intro h
    let c : C := Quotient.mk (F.auxiliarySetoid rows cols G) h
    have hc : F.AuxiliaryConnected rows cols G c.out h := Quotient.exact (Quotient.out_eq c)
    obtain ⟨j, k, hj⟩ := (hm c h).mp hc
    exact ⟨c, j, k, hj⟩
  · intro c d i j k l hh
    exact (hclass c i k).symm.trans
      ((congrArg (Quotient.mk (F.auxiliarySetoid rows cols G)) hh).trans (hclass d j l))

namespace GraphAtlas

variable {F rows cols G} (D : F.GraphAtlas rows cols G)

def hub (x : (c : D.Component) × (Fin (F.size (D.wheel c)) × Fin 3)) : G.Hub :=
  (D.lift x.1).hub x.2.1 x.2.2

theorem hub_bijective : Function.Bijective D.hub := by
  constructor
  · rintro ⟨c, i, k⟩ ⟨d, j, l⟩ hh
    have hcd := D.disjoint c d i j k l hh
    subst d
    have he := (D.lift c).hub_injective hh
    exact congrArg (Sigma.mk c) he
  · intro h
    obtain ⟨c, j, k, hh⟩ := D.cover h
    exact ⟨⟨c, j, k⟩, hh⟩

noncomputable def hubEquiv :
    ((c : D.Component) × (Fin (F.size (D.wheel c)) × Fin 3)) ≃ G.Hub :=
  Equiv.ofBijective D.hub D.hub_bijective

def outerPort (x : (c : D.Component) × Fin (F.size (D.wheel c))) : F.OrdinaryPort rows cols G :=
  (D.lift x.1).ordinaryPort x.2

theorem outerPort_injective : Function.Injective D.outerPort := by
  rintro ⟨c, i⟩ ⟨d, j⟩ hh
  have hp := congrArg Subtype.val hh
  have hv : (D.lift c).hub i 0 = (D.lift d).hub j 0 :=
    Sum.inl.inj (Sum.inr.inj (congrArg Port.vertex hp))
  have hcd := D.disjoint c d i j 0 0 hv
  subst d
  have he : i = j := congrArg Prod.fst
    (show (i, (0 : Fin 3)) = (j, 0) from (D.lift c).hub_injective hv)
  exact congrArg (Sigma.mk c) he

variable [IsEmpty G.Joint]

theorem outerPort_surjective : Function.Surjective D.outerPort := by
  intro x
  obtain ⟨h, r, j, hx, _⟩ := F.ordinaryPort_exists_hub rows cols G x
  obtain ⟨c, i, k, hi⟩ := D.cover h
  have ho : F.IsOrdinaryPort rows cols G (.hub ((D.lift c).hub i k) (0 : Fin 3)) := by
    have he : (.hub ((D.lift c).hub i k) (0 : Fin 3) : G.Dart) = x.val :=
      (congrArg (fun h => (.hub h (0 : Fin 3) : G.Dart)) hi).trans hx.symm
    exact he.symm ▸ x.property
  have hk := ((D.lift c).ordinary_port_iff i k 0).mp ho
  rcases hk with ⟨rfl, _⟩
  exact ⟨⟨c, i⟩, Subtype.ext ((congrArg (fun h => (.hub h (0 : Fin 3) : G.Dart)) hi).trans hx.symm)⟩

noncomputable def outerPortEquiv :
    ((c : D.Component) × Fin (F.size (D.wheel c))) ≃ F.OrdinaryPort rows cols G :=
  Equiv.ofBijective D.outerPort ⟨D.outerPort_injective, D.outerPort_surjective⟩

omit [IsEmpty G.Joint] in
theorem rhs_sum : (∑ h : G.Hub, (F.system.reindex rows cols).rhs (G.hubLabel h)) =
    ∑ c : D.Component, F.parity (D.wheel c) := by
  rw [← D.hubEquiv.sum_comp (fun h => (F.system.reindex rows cols).rhs (G.hubLabel h))]
  change (∑ x : (c : D.Component) × (Fin (F.size (D.wheel c)) × Fin 3),
    (F.system.reindex rows cols).rhs (G.hubLabel ((D.lift x.1).hub x.2.1 x.2.2))) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp_rw [(D.lift c).label, SparseSystem.reindex_rhs]
  rw [Fintype.sum_prod_type]
  simp [system, Fin.sum_univ_succ]
  change (∑ j : Fin (F.size (D.wheel c)), if j = (0 : Fin (F.size (D.wheel c))) then
    F.parity (D.wheel c) else 0) = _
  simp

end GraphAtlas
end ThomGame.Wheel.Family
