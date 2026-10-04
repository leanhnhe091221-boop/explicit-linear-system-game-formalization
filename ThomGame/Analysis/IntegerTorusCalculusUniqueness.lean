module

public import ThomGame.Analysis.CommutativeTorusFunctionalCalculus
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! The two genuine coordinate characters determine the torus functional calculus uniquely. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerTorus

open scoped CStarAlgebra

theorem character_injective : Function.Injective character := by
  intro x y h
  apply AddCircle.injective_toCircle (one_ne_zero : (1 : ℝ) ≠ 0)
  exact Subtype.ext h

def coordinateAlgebra : StarSubalgebra ℂ C(Torus, ℂ) :=
  StarAlgebra.adjoin ℂ {coordinateCharacter false, coordinateCharacter true}

theorem coordinateCharacter_mem (b : Bool) : coordinateCharacter b ∈ coordinateAlgebra := by
  apply StarAlgebra.subset_adjoin
  cases b <;> simp

theorem coordinateAlgebra_separatesPoints : coordinateAlgebra.SeparatesPoints := by
  intro x y hxy
  by_cases h₀ : character x.1 = character y.1
  · have h₁ : character x.2 ≠ character y.2 := by
      intro h₁
      exact hxy (Prod.ext (character_injective h₀) (character_injective h₁))
    exact ⟨coordinateCharacter true, ⟨coordinateCharacter true, coordinateCharacter_mem true, rfl⟩, h₁⟩
  · exact ⟨coordinateCharacter false, ⟨coordinateCharacter false, coordinateCharacter_mem false, rfl⟩, h₀⟩

theorem coordinateAlgebra_dense : coordinateAlgebra.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    coordinateAlgebra coordinateAlgebra_separatesPoints

theorem torusStarAlgHom_ext {A : Type*} [CStarAlgebra A]
    (φ ψ : C(Torus, ℂ) →⋆ₐ[ℂ] A)
    (h : ∀ b : Bool, φ (coordinateCharacter b) = ψ (coordinateCharacter b)) : φ = ψ := by
  have hs : coordinateAlgebra ≤ StarAlgHom.equalizer φ ψ := by
    apply StarAlgHom.adjoin_le_equalizer
    intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · exact h false
    · rcases Set.mem_singleton_iff.mp hf with rfl
      exact h true
  have hc : IsClosed (StarAlgHom.equalizer φ ψ : Set C(Torus, ℂ)) :=
    isClosed_eq (map_continuous φ) (map_continuous ψ)
  have ht := StarSubalgebra.topologicalClosure_minimal hs hc
  rw [coordinateAlgebra_dense] at ht
  exact StarAlgHom.ext fun f => ht (show f ∈ (⊤ : StarSubalgebra ℂ C(Torus, ℂ)) from trivial)

end ThomGame.Analysis.IntegerTorus
