module

public import ThomGame.Pictures.MarkedReturn
public import ThomGame.Pictures.GraphRotation
public import ThomGame.Pictures.GraphPrimitives

/-!
# Successive boundary ports on graph circuits

The boundary successor follows the actual circuit until it first reaches
another boundary port. The top and bottom occurrences remain separately
indexed even when their labels coincide. The primitive formulas read a
downward hub forward and an upward hub backward. No noncrossing or disk
separation assertion is included in this definition.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

abbrev BoundaryIndex (u v : List S) := Fin u.length ⊕ Fin v.length

def IsBoundary (G : PortGraph P u v) : G.Dart → Prop
  | .top _ => True
  | .bottom _ => True
  | .hub _ _ => False
  | .joint _ _ => False

def boundaryPorts (G : PortGraph P u v) : BoundaryIndex u v ≃ {a : G.Dart // G.IsBoundary a} where
  toFun
    | .inl i => ⟨.top i, trivial⟩
    | .inr i => ⟨.bottom i, trivial⟩
  invFun a := match a with
    | ⟨.top i, _⟩ => .inl i
    | ⟨.bottom i, _⟩ => .inr i
    | ⟨.hub _ _, h⟩ => h.elim
    | ⟨.joint _ _, h⟩ => h.elim
  left_inv i := by cases i <;> rfl
  right_inv a := by
    rcases a with ⟨a, ha⟩
    cases a <;> first | rfl | exact ha.elim

def boundaryDart (G : PortGraph P u v) : BoundaryIndex u v ↪ G.Dart :=
  (boundaryPorts G).toEmbedding.trans (Function.Embedding.subtype _)

noncomputable def boundaryTime (G : PortGraph P u v) (i : BoundaryIndex u v) : Nat :=
  MarkedReturn.time G.circuitStep G.IsBoundary (G.boundaryPorts i)

noncomputable def boundaryNext (G : PortGraph P u v) : Equiv.Perm (BoundaryIndex u v) :=
  (G.boundaryPorts.trans (MarkedReturn.perm G.circuitStep G.IsBoundary)).trans G.boundaryPorts.symm

theorem boundaryTime_pos (G : PortGraph P u v) (i : BoundaryIndex u v) :
    0 < G.boundaryTime i := MarkedReturn.time_pos _ _ _

theorem boundaryNext_return (G : PortGraph P u v) (i : BoundaryIndex u v) :
    G.boundaryDart (G.boundaryNext i) =
      (G.circuitStep ^ G.boundaryTime i) (G.boundaryDart i) := by
  change (G.boundaryPorts (G.boundaryPorts.symm
    (MarkedReturn.perm G.circuitStep G.IsBoundary (G.boundaryPorts i)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem boundaryNext_first (G : PortGraph P u v) (i : BoundaryIndex u v)
    {n : Nat} (hn : 0 < n) (ht : n < G.boundaryTime i) :
    ¬ G.IsBoundary ((G.circuitStep ^ n) (G.boundaryDart i)) :=
  MarkedReturn.before_time_not_mem _ _ _ hn ht

theorem boundaryNext_eq_of_first (G : PortGraph P u v) (i j : BoundaryIndex u v)
    {n : Nat} (hn : 0 < n)
    (he : (G.circuitStep ^ n) (G.boundaryDart i) = G.boundaryDart j)
    (hf : ∀ k, 0 < k → k < n → ¬ G.IsBoundary ((G.circuitStep ^ k) (G.boundaryDart i))) :
    G.boundaryNext i = j := by
  have hp : G.IsBoundary ((G.circuitStep ^ n) (G.boundaryDart i)) :=
    he.symm ▸ (G.boundaryPorts j).property
  have ht := MarkedReturn.time_eq_of_first G.circuitStep G.IsBoundary (G.boundaryPorts i) hn hp hf
  apply G.boundaryDart.injective
  rw [G.boundaryNext_return]
  change (G.circuitStep ^ MarkedReturn.time G.circuitStep G.IsBoundary (G.boundaryPorts i))
    (G.boundaryDart i) = G.boundaryDart j
  rw [ht]
  exact he

theorem boundaryNext_eq_of_step (G : PortGraph P u v) (i j : BoundaryIndex u v)
    (he : G.circuitStep (G.boundaryDart i) = G.boundaryDart j) : G.boundaryNext i = j :=
  G.boundaryNext_eq_of_first i j (n := 1) (by omega) (by simpa using he)
    (by intro k hk hkn; omega)

theorem boundaryNext_eq_of_two_steps (G : PortGraph P u v) (i j : BoundaryIndex u v)
    (hi : ¬ G.IsBoundary (G.circuitStep (G.boundaryDart i)))
    (he : G.circuitStep (G.circuitStep (G.boundaryDart i)) = G.boundaryDart j) :
    G.boundaryNext i = j :=
  G.boundaryNext_eq_of_first i j (n := 2) (by omega)
    (by simpa only [pow_two, Equiv.Perm.mul_apply] using he) (by
      intro k hk hkn
      have : k = 1 := by omega
      subst k
      simpa using hi)

theorem boundaryPorts_next (G : PortGraph P u v) (i : BoundaryIndex u v) :
    MarkedReturn.perm G.circuitStep G.IsBoundary (G.boundaryPorts i) =
      G.boundaryPorts (G.boundaryNext i) := by
  change _ = G.boundaryPorts (G.boundaryPorts.symm _)
  rw [Equiv.apply_symm_apply]
  rfl

theorem boundaryNext_sameCycle_iff (G : PortGraph P u v) (i j : BoundaryIndex u v) :
    G.boundaryNext.SameCycle i j ↔ G.circuit (G.boundaryDart i) = G.circuit (G.boundaryDart j) :=
  (FiniteReturn.sameCycle_congr _ _ G.boundaryPorts G.boundaryPorts_next i j).trans
    ((MarkedReturn.sameCycle_iff _ _ _ _).trans (G.circuit_eq_iff _ _).symm)

variable (P)

theorem boundaryNext_identity_top (w : List S) (i : Fin w.length) :
    (identity P w).boundaryNext (.inl i) = .inr i :=
  boundaryNext_eq_of_step _ _ _ rfl

theorem boundaryNext_identity_bottom (w : List S) (i : Fin w.length) :
    (identity P w).boundaryNext (.inr i) = .inl i :=
  boundaryNext_eq_of_step _ _ _ rfl

theorem boundaryNext_cap (s : S) (i : Fin 2) :
    (cap P s).boundaryNext (.inl i) = .inl i.rev :=
  boundaryNext_eq_of_step _ _ _ rfl

theorem boundaryNext_cup (s : S) (i : Fin 2) :
    (cup P s).boundaryNext (.inr i) = .inr i.rev :=
  boundaryNext_eq_of_step _ _ _ rfl

theorem boundaryNext_down (r : R) (i : Fin (P.word r).length) :
    (down P r).boundaryNext (.inl i) = .inl (finRotate _ i) :=
  boundaryNext_eq_of_two_steps _ _ _ (fun h => h) rfl

theorem boundaryNext_up (r : R) (i : Fin (P.word r).length) :
    (up P r).boundaryNext (.inr i) = .inr ((finRotate _).symm i) :=
  boundaryNext_eq_of_two_steps _ _ _ (fun h => h) rfl

end ThomGame.Pictures.PortGraph
