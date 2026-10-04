module

public import ThomGame.Analysis.IntegerPlaneRelativeKazhdan
public import ThomGame.Groups.IntegralShearPlaneSemidirect

/-! Relative Kazhdan bounds for the genuine integer root planes in the shear group. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

universe u

open Compressor IntegralShear

local instance : DecidableEq ShearGroup := Classical.decEq _

def rootPlaneKazhdanGenerator (r : Root) (i : Bool × Bool) : ShearGroup :=
  if i.1 then of (if i.2 then reverse r else r)
  else of (if i.2 then right r else across r)

def rootPlaneKazhdanSet (r : Root) : Finset ShearGroup :=
  Finset.univ.image (rootPlaneKazhdanGenerator r)

theorem rootPlaneHom_latticeGenerator (r : Root) (b : Bool) :
    rootPlaneHom r (latticeGenerator b) = of (if b then right r else across r) := by
  cases b <;> simp [rootPlaneHom, latticeGenerator, rootPlaneElement]

theorem rootPlaneSemidirectHom_generator (r : Root) (i : Bool × Bool) :
    rootPlaneSemidirectHom r (freeShearGenerator i) = rootPlaneKazhdanGenerator r i := by
  rcases i with ⟨a, b⟩
  cases a <;> cases b <;>
    simp [freeShearGenerator, rootPlaneKazhdanGenerator, rootPlaneHom_latticeGenerator]

theorem rootPlaneSemidirectHom_comp_inl (r : Root) :
    (rootPlaneSemidirectHom r).comp SemidirectProduct.inl = rootPlaneHom r := by
  ext v
  exact rootPlaneSemidirectHom_inl r v

theorem rootPlaneKazhdanSet_image (r : Root) :
    freeShearKazhdanSet.image (rootPlaneSemidirectHom r) = rootPlaneKazhdanSet r := by
  simp only [freeShearKazhdanSet, rootPlaneKazhdanSet, Finset.image_image,
    Function.comp_def, rootPlaneSemidirectHom_generator]

theorem rootPlane_relativeKazhdanBound (r : Root) :
    HilbertRelativeKazhdanBound.{u} (rootPlaneHom r) (rootPlaneKazhdanSet r) (1 / 100) := by
  have h := hilbertRelativeKazhdanBound_image _ _ _
    freeShear_relativeKazhdanBound.{u} (rootPlaneSemidirectHom r)
  rwa [rootPlaneSemidirectHom_comp_inl, rootPlaneKazhdanSet_image] at h

theorem rootPlane_nonzero_invariant (r : Root)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hmove : ∀ i : Bool × Bool, ‖ρ (rootPlaneKazhdanGenerator r i) ξ - ξ‖ < 1 / 100) :
    ∃ η : H, η ≠ 0 ∧ η ∈ hilbertUnitaryInvariants (ρ.comp (rootPlaneHom r)) := by
  apply hilbertRelativeKazhdanBound_nonzero_invariant _ _ _ (rootPlane_relativeKazhdanBound r)
    ρ ξ hξ
  intro g hg
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
  exact hmove i

end ThomGame.Analysis
