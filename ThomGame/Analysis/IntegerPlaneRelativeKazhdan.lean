module

public import ThomGame.Analysis.IntegerLatticeShearMeasure
public import ThomGame.Analysis.HilbertRelativeKazhdanBounds

/-! An unconditional relative Kazhdan bound for the genuine integer free-shear semidirect product. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

universe u

open IntegerPlane

def freeShearGenerator (i : Bool × Bool) : FreeShearProduct :=
  if i.1 then SemidirectProduct.inr (FreeGroup.of i.2)
  else SemidirectProduct.inl (latticeGenerator i.2)

def freeShearKazhdanSet : Finset FreeShearProduct := Finset.univ.image freeShearGenerator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def freeShearLatticeRepresentation (ρ : FreeShearProduct →* (H ≃ₗᵢ[ℂ] H)) :
    IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H) := ρ.comp SemidirectProduct.inl

omit [CompleteSpace H] in
theorem freeShear_representation_conjugate (ρ : FreeShearProduct →* (H ≃ₗᵢ[ℂ] H))
    (b : Bool) (v : IntegerPlane.Group) :
    ρ (freeShearGenerator (true, b)) * freeShearLatticeRepresentation ρ v *
        (ρ (freeShearGenerator (true, b)))⁻¹ =
      freeShearLatticeRepresentation ρ (IntegerPlane.shear b v) := by
  have h := congrArg ρ (SemidirectProduct.inl_aut (φ := freeAction) (FreeGroup.of b) v)
  simpa only [freeShearGenerator, ↓reduceIte, freeShearLatticeRepresentation,
    MonoidHom.comp_apply, freeAction_of, map_mul, map_inv] using h.symm

theorem freeShear_no_small_unit_vector (ρ : FreeShearProduct →* (H ≃ₗᵢ[ℂ] H))
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (horth : ξ ∈ (hilbertUnitaryInvariants (freeShearLatticeRepresentation ρ))ᗮ)
    (hmove : ∀ i : Bool × Bool, ‖ρ (freeShearGenerator i) ξ - ξ‖ ≤ 1 / 100) : False := by
  apply latticeShear_no_small_unit_vector (freeShearLatticeRepresentation ρ)
    (fun b => ρ (freeShearGenerator (true, b))) (freeShear_representation_conjugate ρ) ξ hξ horth
  · intro b
    exact hmove (false, b)
  · intro b
    exact hmove (true, b)

theorem freeShear_unit_displacement (ρ : FreeShearProduct →* (H ≃ₗᵢ[ℂ] H))
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (horth : ξ ∈ (hilbertUnitaryInvariants (freeShearLatticeRepresentation ρ))ᗮ) :
    ∃ i : Bool × Bool, 1 / 100 < ‖ρ (freeShearGenerator i) ξ - ξ‖ := by
  by_contra! h
  exact freeShear_no_small_unit_vector ρ ξ hξ horth h

theorem freeShear_relative_displacement (ρ : FreeShearProduct →* (H ≃ₗᵢ[ℂ] H)) (ξ : H)
    (horth : ξ ∈ (hilbertUnitaryInvariants (freeShearLatticeRepresentation ρ))ᗮ) :
    ∃ i : Bool × Bool, (1 / 100 : ℝ) * ‖ξ‖ ≤ ‖ρ (freeShearGenerator i) ξ - ξ‖ := by
  by_cases hξ : ξ = 0
  · exact ⟨(false, false), by simp [hξ]⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  let η : H := ((‖ξ‖⁻¹ : ℝ) : ℂ) • ξ
  have hη : ‖η‖ = 1 := by
    simp only [η, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ hn.ne'
  have hηorth : η ∈ (hilbertUnitaryInvariants (freeShearLatticeRepresentation ρ))ᗮ :=
    (hilbertUnitaryInvariants (freeShearLatticeRepresentation ρ))ᗮ.smul_mem _ horth
  obtain ⟨i, hi⟩ := freeShear_unit_displacement ρ η hη hηorth
  have hd : ‖ρ (freeShearGenerator i) η - η‖ = ‖ρ (freeShearGenerator i) ξ - ξ‖ / ‖ξ‖ := by
    simp only [η, map_smul, ← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), div_eq_inv_mul]
  rw [hd] at hi
  exact ⟨i, ((lt_div_iff₀ hn).mp hi).le⟩

theorem freeShear_relativeKazhdanBound :
    HilbertRelativeKazhdanBound.{u} (SemidirectProduct.inl : IntegerPlane.Group →* FreeShearProduct)
      freeShearKazhdanSet (1 / 100) := by
  intro H _ _ _ ρ ξ hξ
  obtain ⟨i, hi⟩ := freeShear_relative_displacement ρ ξ hξ
  exact ⟨freeShearGenerator i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩

end ThomGame.Analysis
