module

public import ThomGame.Finite.PentagonFold
public import ThomGame.Finite.WheelPentagon

/-! # A global wheel morphism from an alternating phase -/

@[expose] public section
namespace ThomGame.Wheel.Family

variable {R V : Type*} [DecidableEq V] (F : Family R V)

structure FoldPhase (s : V) where
  value : (r : R) → Fin (F.size r) → ZMod 2
  next : ∀ r j, value r (finRotate (F.size r) j) =
    value r j + if F.letter r j = s then 1 else 0

def foldHit (s : V) (r : R) (j : Fin (F.size r)) : Bool := decide (F.letter r j = s)

def foldVertex (s : V) (p : F.FoldPhase s) : F.Row → Option (Fin 5)
  | ⟨r, j, k⟩ => PentagonFold.vertex (F.foldHit s r j)
      (F.foldHit s r (finRotate (F.size r) j)) (p.value r j) k

def foldEdge (s : V) (p : F.FoldPhase s) : F.Col → Option PentagonFold.Edge
  | .inl t => PentagonFold.ordinary (decide (t = s))
  | .inr ⟨r, j, k⟩ => PentagonFold.aux (F.foldHit s r j)
      (F.foldHit s r (finRotate (F.size r) j)) (p.value r j) k

theorem foldEdge_aux (s : V) (p : F.FoldPhase s) (r : R) (j : Fin (F.size r)) (k : Fin 4) :
    F.foldEdge s p (F.aux r j k) = PentagonFold.aux (F.foldHit s r j)
      (F.foldHit s r (finRotate (F.size r) j)) (p.value r j) k := rfl

theorem fold_row_images (s : V) (p : F.FoldPhase s) (r : R) (j : Fin (F.size r)) (k : Fin 3) :
    (F.system.hypergraph.incidence ⟨r, j, k⟩).filterMap (F.foldEdge s p) =
      PentagonFold.rowImages (F.foldHit s r j) (F.foldHit s r (finRotate (F.size r) j))
        (p.value r j) k := by
  have hn : p.value r (j + 1) = p.value r j + if F.letter r j = s then 1 else 0 := by
    simpa only [finRotate_apply] using p.next r j
  fin_cases k <;>
    simp [SparseSystem.hypergraph, system, columns, foldEdge, aux, foldHit,
      PentagonFold.aux, PentagonFold.rowImages, PentagonFold.step, hn, List.filterMap_cons]

theorem foldHit_separated (s : V)
    (hsep : ∀ r j, F.letter r j ≠ F.letter r (finRotate (F.size r) j))
    (r : R) (j : Fin (F.size r)) :
    ¬ (F.foldHit s r j = true ∧ F.foldHit s r (finRotate (F.size r) j) = true) := by
  rintro ⟨hx, hy⟩
  have hx' : F.letter r j = s := of_decide_eq_true hx
  have hy' : F.letter r (finRotate (F.size r) j) = s := of_decide_eq_true hy
  exact hsep r j (hx'.trans hy'.symm)

def foldHom (s : V) (p : F.FoldPhase s)
    (hsep : ∀ r j, F.letter r j ≠ F.letter r (finRotate (F.size r) j)) :
    Hypergraph.GeneralizedHom F.system.hypergraph (Hypergraph.sun 5) where
  vertex := F.foldVertex s p
  edge := F.foldEdge s p
  retained := by
    rintro ⟨r, j, k⟩ v hv
    rw [F.fold_row_images]
    exact PentagonFold.retained _ _ _ _ (F.foldHit_separated s hsep r j) hv
  deleted := by
    rintro ⟨r, j, k⟩ hv
    rw [F.fold_row_images]
    exact PentagonFold.deleted _ _ _ _ (F.foldHit_separated s hsep r j) hv

variable [DecidableEq R]

def foldRetraction (s : V) (p : F.FoldPhase s)
    (hsep : ∀ r j, F.letter r j ≠ F.letter r (finRotate (F.size r) j))
    (r : R) (j : Fin (F.size r)) (hs : F.letter r j = s) (hp : p.value r j = 0)
    (hlen : 3 ≤ F.size r) : Hypergraph.Retraction F.system.hypergraph (Hypergraph.sun 5) := by
  have hsn : F.letter r (finRotate (F.size r) j) ≠ s := by
    intro h
    exact hsep r j (hs.trans h.symm)
  have hsp : F.letter r ((finRotate (F.size r)).symm j) ≠ s := by
    intro h
    apply hsep r ((finRotate (F.size r)).symm j)
    simpa only [Equiv.apply_symm_apply] using h.trans hs.symm
  have hpn : p.value r (finRotate (F.size r) j) = 1 := by rw [p.next, hp, ite_eq_left hs, zero_add]
  have hpp : p.value r ((finRotate (F.size r)).symm j) = 0 := by
    have h := p.next r ((finRotate (F.size r)).symm j)
    simpa only [Equiv.apply_symm_apply, hp, ite_eq_right hsp, add_zero] using h.symm
  simp only [finRotate_apply, finRotate_symm_apply] at hsn hsp hpn hpp
  refine {
    inclusion := F.pentagonOpenEmbedding r j hlen
    retract := F.foldHom s p hsep
    vertex_leftInverse := ?_
    edge_leftInverse := ?_ }
  · intro i
    fin_cases i <;>
      simp [foldHom, foldVertex, foldHit, pentagonOpenEmbedding, pentagonVertex,
        PentagonFold.vertex, hs, hp, hsp, hpp]
  · rintro (i | i) <;> fin_cases i <;>
      simp [foldHom, foldEdge, foldHit, pentagonOpenEmbedding, pentagonSpoke, pentagonRim,
        aux, PentagonFold.aux, PentagonFold.ordinary, PentagonFold.a, PentagonFold.b,
        PentagonFold.c, PentagonFold.d, hs, hp, hsn, hsp, hpn, hpp]

theorem pentagon_rhs_zero (r : R) (j : Fin (F.size r))
    (hz : F.system.rhs ⟨r, j, 0⟩ = 0) (i : Fin 5) :
    F.system.rhs ((F.pentagonCycle r j).vertex i) = 0 := by
  change F.system.rhs (F.pentagonVertex r j i) = 0
  fin_cases i
  · exact hz
  all_goals simp [pentagonVertex, system]

def foldStellar (s : V) (p : F.FoldPhase s)
    (hsep : ∀ r j, F.letter r j ≠ F.letter r (finRotate (F.size r) j))
    (r : R) (j : Fin (F.size r)) (hs : F.letter r j = s) (hp : p.value r j = 0)
    (hlen : 3 ≤ F.size r) (hz : F.system.rhs ⟨r, j, 0⟩ = 0) :
    (F.pentagonCycle r j).Stellar F.system.rhs where
  retraction := F.foldRetraction s p hsep r j hs hp hlen
  vertex_eq _ := rfl
  rim_eq _ := rfl
  rhs_zero := F.pentagon_rhs_zero r j hz

end ThomGame.Wheel.Family
