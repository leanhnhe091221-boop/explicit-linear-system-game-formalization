module

public import ThomGame.Pictures.GraphRotation
public import ThomGame.Pictures.OrbitTransport
public import ThomGame.Pictures.PermutationSurgery

/-!
# The two pairings on an indexed circuit

The two ports at a vertex are indexed by a Boolean. Vertex pairing
exchanges them; edge pairing connects the outgoing port to the incoming
port at the next vertex. Their product has exactly two orbits, including
for loops and digons.
-/

@[expose] public section
namespace ThomGame.Pictures.CircuitPermutations

open Equiv FiniteReturn

variable (n : Nat)

def vertex : Perm (Fin n × Bool) where
  toFun x := (x.1, !x.2)
  invFun x := (x.1, !x.2)
  left_inv x := by simp
  right_inv x := by simp

def edge : Perm (Fin n × Bool) where
  toFun
    | (i, false) => (finRotate n i, true)
    | (i, true) => ((finRotate n).symm i, false)
  invFun
    | (i, false) => (finRotate n i, true)
    | (i, true) => ((finRotate n).symm i, false)
  left_inv x := by rcases x with ⟨i, s⟩; cases s <;> simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv x := by rcases x with ⟨i, s⟩; cases s <;> simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem vertex_involutive : Function.Involutive (vertex n) := by
  intro x
  exact (vertex n).left_inv x

theorem vertex_ne_self (x : Fin n × Bool) : vertex n x ≠ x := by
  intro h
  have he := congrArg Prod.snd h
  exact (Bool.not_eq_self _).mp he

theorem edge_involutive : Function.Involutive (edge n) := by
  intro x
  exact (edge n).left_inv x

theorem edge_snd (x : Fin n × Bool) : (edge n x).2 = !x.2 := by
  rcases x with ⟨i, s⟩
  cases s <;> rfl

theorem vertex_sameCycle (x y : Fin n × Bool) :
    (vertex n).SameCycle x y ↔ x.1 = y.1 := by
  constructor
  · exact CycleSurgery.invariant_sameCycle (vertex n) Prod.fst (fun _ => rfl)
  · rcases x with ⟨i, s⟩
    rcases y with ⟨j, t⟩
    intro he
    change i = j at he
    subst j
    cases s <;> cases t
    · exact Perm.SameCycle.rfl
    · exact ⟨1, rfl⟩
    · exact ⟨1, rfl⟩
    · exact Perm.SameCycle.rfl

def vertexOrbitEquiv : Orbit (vertex n) ≃ Fin n where
  toFun := Quotient.lift Prod.fst (fun x y h => (vertex_sameCycle n x y).mp h)
  invFun i := orbit (vertex n) (i, false)
  left_inv c := Quotient.inductionOn c fun _x =>
    (orbit_eq_iff _ _ _).mpr ((vertex_sameCycle n _ _).mpr rfl)
  right_inv _ := rfl

theorem vertex_orbit_card : Nat.card (Orbit (vertex n)) = n := by
  rw [Nat.card_congr (vertexOrbitEquiv n), Nat.card_fin]

/-- A permutation with exactly the two ports of each vertex as its
orbits must exchange those ports. -/
theorem eq_vertex_of_cycles {A : Type*} (f : Perm A) (e : Fin n × Bool ≃ A)
    (h : ∀ x y, f.SameCycle (e x) (e y) ↔ x.1 = y.1) (x : Fin n × Bool) :
    f (e x) = e (vertex n x) := by
  obtain ⟨y, hy⟩ := e.surjective (f (e x))
  have hi : x.1 = y.1 := (h x y).mp (hy.symm ▸ (show f.SameCycle (e x) (f (e x)) from
    ⟨1, by simp⟩))
  have hn : y ≠ x := by
    intro he
    have hf : f (e x) = e x := hy.symm.trans (congrArg e he)
    have hp : f.SameCycle (e x) (e (vertex n x)) := (h x (vertex n x)).mpr rfl
    exact vertex_ne_self n x (e.injective (hp.eq_of_left hf).symm)
  have he : y = vertex n x := by
    rcases x with ⟨i, s⟩
    rcases y with ⟨j, t⟩
    change i = j at hi
    subst j
    cases s <;> cases t
    · exact (hn rfl).elim
    · rfl
    · rfl
    · exact (hn rfl).elim
  exact hy.symm.trans (congrArg e he)

/-- Renumber incoming ports by the edge whose other end is outgoing. -/
def edgeNumbering : Perm (Fin n × Bool) where
  toFun
    | (i, false) => (i, false)
    | (i, true) => (finRotate n i, true)
  invFun
    | (i, false) => (i, false)
    | (i, true) => ((finRotate n).symm i, true)
  left_inv x := by rcases x with ⟨i, s⟩; cases s <;> simp only [Equiv.symm_apply_apply]
  right_inv x := by rcases x with ⟨i, s⟩; cases s <;> simp only [Equiv.apply_symm_apply]

theorem edgeNumbering_vertex (x : Fin n × Bool) :
    edge n (edgeNumbering n x) = edgeNumbering n (vertex n x) := by
  rcases x with ⟨i, s⟩
  cases s
  · rfl
  · change ((finRotate n).symm (finRotate n i), false) = (i, false)
    rw [Equiv.symm_apply_apply]

theorem edge_orbit_card : Nat.card (Orbit (edge n)) = n := by
  rw [← Nat.card_congr (orbitEquiv (vertex n) (edge n) (edgeNumbering n)
    (edgeNumbering_vertex n)), vertex_orbit_card]

def sides : Perm (Fin n × Bool) := edge n * vertex n

theorem sides_false (i : Fin n) : sides n (i, false) = ((finRotate n).symm i, false) := rfl

theorem sides_true (i : Fin n) : sides n (i, true) = (finRotate n i, true) := rfl

theorem sides_snd (x : Fin n × Bool) : (sides n x).2 = x.2 := by
  rcases x with ⟨i, s⟩
  cases s <;> rfl

theorem sides_pow_false (k : Nat) (i : Fin n) :
    (sides n ^ k) (i, false) = (((finRotate n).symm ^ k) i, false) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Perm.mul_apply, ih, sides_false, pow_succ', Perm.mul_apply]

theorem sides_pow_true (k : Nat) (i : Fin n) :
    (sides n ^ k) (i, true) = ((finRotate n ^ k) i, true) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Perm.mul_apply, ih, sides_true, pow_succ', Perm.mul_apply]

theorem sides_sameCycle (x y : Fin n × Bool) : (sides n).SameCycle x y ↔ x.2 = y.2 := by
  constructor
  · exact CycleSurgery.invariant_sameCycle (sides n) Prod.snd (sides_snd n)
  · rcases x with ⟨i, s⟩
    rcases y with ⟨j, t⟩
    intro he
    change s = t at he
    subst t
    cases s
    · obtain ⟨k, hk⟩ := (PortGraph.finRotate_sameCycle i j).inv.exists_nat_pow_eq
      exact ⟨(k : Int), by rw [zpow_natCast, sides_pow_false]; exact congrArg (·, false) hk⟩
    · obtain ⟨k, hk⟩ := (PortGraph.finRotate_sameCycle i j).exists_nat_pow_eq
      exact ⟨(k : Int), by rw [zpow_natCast, sides_pow_true]; exact congrArg (·, true) hk⟩

def sidesOrbitEquiv [NeZero n] : Orbit (sides n) ≃ Bool where
  toFun := Quotient.lift Prod.snd (fun x y h => (sides_sameCycle n x y).mp h)
  invFun s := orbit (sides n) (0, s)
  left_inv c := Quotient.inductionOn c fun _x =>
    (orbit_eq_iff _ _ _).mpr ((sides_sameCycle n _ _).mpr rfl)
  right_inv _ := rfl

theorem sides_orbit_card [NeZero n] : Nat.card (Orbit (sides n)) = 2 := by
  rw [Nat.card_congr (sidesOrbitEquiv n)]
  simp

end ThomGame.Pictures.CircuitPermutations
