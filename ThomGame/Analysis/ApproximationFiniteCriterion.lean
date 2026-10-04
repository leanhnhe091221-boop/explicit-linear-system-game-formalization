module

public import ThomGame.Analysis.UnitaryFiniteEquivalence
public import ThomGame.Analysis.ApproximationCriterion

/-!
# Uniform approximate triviality and actual finite-algebra representations

Exact unitary lifting transports the previously proved approximation
criterion to the full unitary groups of the actual matrix quotient and
its finite weakly closed operator algebra. Approximate representations
still start at the free group, and dimensions vary over all positive
natural numbers. No injectivity assumption is imposed on representations.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable {S : Type*} (rels : Set (FreeGroup S)) (v : FreeGroup S)

theorem approximatelyTrivial_matrixQuotient_killed {ι : Type*} (dims : ι → Nat)
    (hd : ∀ i, 0 < dims i) (L : Filter ι) (hfinite : rels.Finite)
    (h : ApproximatelyTrivial rels v)
    (φ : PresentedGroup rels →* unitary (MatrixTracialQuotient dims L)) :
    φ (PresentedGroup.mk rels v) = 1 := by
  let e := unitaryQuotientEquiv dims hd L
  have hk := approximatelyTrivial_quotient_killed rels dims L v hfinite hd h
    (e.symm.toMonoidHom.comp φ)
  apply e.symm.injective
  rw [map_one]
  exact hk

theorem approximatelyTrivial_iff_matrixQuotient_killed (hfinite : rels.Finite)
    (L : Filter Nat) [L.NeBot] (hL : L ≤ atTop) :
    ApproximatelyTrivial rels v ↔
      ∀ (dims : Nat → Nat), (∀ n, 0 < dims n) →
        ∀ φ : PresentedGroup rels →* unitary (MatrixTracialQuotient dims L),
          φ (PresentedGroup.mk rels v) = 1 := by
  constructor
  · intro h dims hd φ
    exact approximatelyTrivial_matrixQuotient_killed rels v dims hd L hfinite h φ
  · intro hk
    apply (approximatelyTrivial_iff_quotient_killed rels v hfinite L hL).mpr
    intro dims hd φ
    apply unitaryQuotientEmbedding_injective dims L
    rw [map_one]
    exact hk dims hd ((unitaryQuotientEmbedding dims L).comp φ)

theorem approximatelyTrivial_finiteAlgebra_killed (dims : Nat → Nat)
    (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (hfinite : rels.Finite) (h : ApproximatelyTrivial rels v)
    (φ : PresentedGroup rels →* unitary (MatrixFiniteOperatorAlgebra dims hd L)) :
    φ (PresentedGroup.mk rels v) = 1 := by
  let e := unitaryQuotientFiniteEquiv dims hd L hL
  have hk := approximatelyTrivial_quotient_killed rels dims (L : Filter Nat) v hfinite hd h
    (e.symm.toMonoidHom.comp φ)
  apply e.symm.injective
  rw [map_one]
  exact hk

theorem approximatelyTrivial_iff_finiteAlgebra_killed (hfinite : rels.Finite)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) :
    ApproximatelyTrivial rels v ↔
      ∀ (dims : Nat → Nat) (hd : ∀ n, 0 < dims n),
        ∀ φ : PresentedGroup rels →* unitary (MatrixFiniteOperatorAlgebra dims hd L),
          φ (PresentedGroup.mk rels v) = 1 := by
  constructor
  · intro h dims hd φ
    exact approximatelyTrivial_finiteAlgebra_killed rels v dims hd L hL hfinite h φ
  · intro hk
    apply (approximatelyTrivial_iff_quotient_killed rels v hfinite (L : Filter Nat) hL).mpr
    intro dims hd φ
    apply unitaryQuotientFiniteEmbedding_injective dims hd L
    rw [map_one]
    exact hk dims hd ((unitaryQuotientFiniteEmbedding dims hd L).comp φ)

theorem approximatelyTrivial_iff_finiteAlgebra_hyperfilter_killed (hfinite : rels.Finite) :
    ApproximatelyTrivial rels v ↔
      ∀ (dims : Nat → Nat) (hd : ∀ n, 0 < dims n),
        ∀ φ : PresentedGroup rels →* unitary (MatrixFiniteOperatorAlgebra dims hd (hyperfilter Nat)),
          φ (PresentedGroup.mk rels v) = 1 :=
  approximatelyTrivial_iff_finiteAlgebra_killed rels v hfinite (hyperfilter Nat) Nat.hyperfilter_le_atTop

end ThomGame.Analysis
