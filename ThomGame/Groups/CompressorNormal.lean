module

public import ThomGame.Groups.CompressorCompression
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Normality of the elementary subgroup N

Both signs of every shear conjugate every elementary generator to a word
of elementary generators. This proves normality in the actual quotient Q.
It does not assume any matrix model or property (T) theorem.
-/

@[expose] public section
namespace ThomGame.Compressor

def elementary : Generator → Bool
  | .inl _ => true
  | .inr _ => false

def elementarySubgroup : Subgroup GroupQ :=
  Subgroup.closure (ofGenerator '' {g | elementary g = true})

theorem ofGenerator_mem_elementarySubgroup (r : Root) (m : Coeff) :
    ofGenerator (.inl (r, m)) ∈ elementarySubgroup :=
  Subgroup.subset_closure ⟨.inl (r, m), rfl, rfl⟩

theorem positive_le_elementarySubgroup : positiveSubgroup ≤ elementarySubgroup := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨g, hg, rfl⟩
  cases g with
  | inl p => exact ofGenerator_mem_elementarySubgroup p.1 p.2
  | inr s => simp [positive] at hg

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem actionTarget_elementary : ∀ s r ε m a,
    a ∈ actionTarget s r ε m → elementary a.1 = true := by decide +kernel

theorem signed_shear_action (s r : Root) (ε : Bool) (m : Coeff) :
    (if ε then shearElement s else (shearElement s)⁻¹) * ofGenerator (.inl (r, m)) *
      (if ε then shearElement s else (shearElement s)⁻¹)⁻¹ =
        Word.eval ofGenerator (actionTarget s r ε m) := by
  have h := eval_rawRelator _ (action_relator_mem s r ε m)
  rw [Word.eval_equation_eq_one_iff] at h
  cases ε <;> simpa [conjugate, signed, shear, X, shearElement, mul_assoc] using h

theorem signed_shear_elementary_generator (s r : Root) (ε : Bool) (m : Coeff) :
    (if ε then shearElement s else (shearElement s)⁻¹) * ofGenerator (.inl (r, m)) *
      (if ε then shearElement s else (shearElement s)⁻¹)⁻¹ ∈ elementarySubgroup := by
  rw [signed_shear_action]
  apply Word.eval_mem
  intro a ha
  exact Subgroup.subset_closure ⟨a.1, actionTarget_elementary s r ε m a ha, rfl⟩

theorem signed_shear_preserves_elementary (s : Root) (ε : Bool)
    (x : GroupQ) (hx : x ∈ elementarySubgroup) :
    (if ε then shearElement s else (shearElement s)⁻¹) * x *
      (if ε then shearElement s else (shearElement s)⁻¹)⁻¹ ∈ elementarySubgroup := by
  have hclosed : elementarySubgroup ≤ elementarySubgroup.comap
      (MulAut.conj (if ε then shearElement s else (shearElement s)⁻¹)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g, hg, rfl⟩
    cases g with
    | inl p => exact signed_shear_elementary_generator s p.1 ε p.2
    | inr r => simp [elementary] at hg
  exact hclosed hx

theorem shear_mem_elementary_normalizer (s : Root) :
    shearElement s ∈ Subgroup.normalizer (elementarySubgroup : Set GroupQ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact signed_shear_preserves_elementary s true x
  · intro hx
    have h := signed_shear_preserves_elementary s false
      (shearElement s * x * (shearElement s)⁻¹) hx
    simpa [mul_assoc] using h

theorem elementary_normalizer_eq_top :
    Subgroup.normalizer (elementarySubgroup : Set GroupQ) = ⊤ := by
  apply top_unique
  intro x _
  apply generated_by _ _ x
  intro g
  cases g with
  | inl p => exact elementarySubgroup.le_normalizer (ofGenerator_mem_elementarySubgroup p.1 p.2)
  | inr s => exact shear_mem_elementary_normalizer s

theorem elementarySubgroup_normal : elementarySubgroup.Normal :=
  Subgroup.normalizer_eq_top_iff.mp elementary_normalizer_eq_top

instance : elementarySubgroup.Normal := elementarySubgroup_normal

end ThomGame.Compressor
