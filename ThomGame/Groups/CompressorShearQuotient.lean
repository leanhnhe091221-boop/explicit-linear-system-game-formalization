module

public import ThomGame.Groups.IntegralShearPresentation
public import ThomGame.Groups.CompressorNormal

/-!
# The integral shear presentation surjects onto the actual Q/N

All three families are checked against Q's existing ordered relation
list. Every elementary generator dies in the actual quotient by N, so
the resulting homomorphism is surjective. This does not yet identify
the source with SL₃(ℤ) or prove property (T).
-/

@[expose] public section
namespace ThomGame.Compressor

private theorem eval_of_shear_family (w : Word Generator)
    (hw : w ∈ shearComm ++ shearRoot ++ shearTorsion) : Word.eval ofGenerator w = 1 := by
  apply eval_rawRelator
  simp only [List.mem_append] at hw
  simp only [rawRelators, List.mem_append]
  tauto

theorem shear_comm_relation (r s : Root) (hrs : separated r s) :
    PrimeFiveRankThreeCover.comm (shearElement r) (shearElement s) = 1 := by
  have hmem : Word.commutator (shear r) (shear s) ∈ shearComm := by
    apply List.mem_flatMap.mpr
    refine ⟨r, mem_roots r, List.mem_flatMap.mpr ⟨s, mem_roots s, ?_⟩⟩
    simp only [hrs, ↓reduceIte, List.mem_singleton]
  have h := eval_of_shear_family _ (by simp only [List.mem_append]; tauto)
  simpa [shear, shearElement, PrimeFiveRankThreeCover.comm] using h

theorem shear_root_relation (r : Root) :
    PrimeFiveRankThreeCover.comm (shearElement r) (shearElement (right r)) = shearElement (across r) := by
  have hmem : Word.equation (Word.commutator (shear r) (shear (right r))) (shear (across r)) ∈ shearRoot :=
    List.mem_map.mpr ⟨r, mem_roots r, rfl⟩
  have h := eval_of_shear_family _ (by simp only [List.mem_append]; tauto)
  rw [Word.eval_equation_eq_one_iff] at h
  simpa [shear, shearElement, PrimeFiveRankThreeCover.comm] using h

theorem shear_torsion_relation :
    (shearElement root12 * (shearElement (reverse root12))⁻¹ * shearElement root12) ^ 4 = 1 := by
  have hmem : power (shear root12 ++ Word.inverse (shear (reverse root12)) ++ shear root12) 4 ∈ shearTorsion := by
    simp [shearTorsion]
  have h := eval_of_shear_family _ (by simp only [List.mem_append]; tauto)
  simpa [power, shear, shearElement, pow_succ, mul_assoc] using h

def integralShearModel : IntegralShear.Model GroupQ where
  x := shearElement
  separated := shear_comm_relation
  adjacent := shear_root_relation
  torsion := shear_torsion_relation

def integralShearToQ : IntegralShear.ShearGroup →* GroupQ := integralShearModel.toHom

@[simp] theorem integralShearToQ_of (r : Root) : integralShearToQ (IntegralShear.of r) = shearElement r :=
  integralShearModel.toHom_of r

def integralShearToQuotient : IntegralShear.ShearGroup →* GroupQ ⧸ elementarySubgroup :=
  (QuotientGroup.mk' elementarySubgroup).comp integralShearToQ

@[simp] theorem integralShearToQuotient_of (r : Root) :
    integralShearToQuotient (IntegralShear.of r) = (QuotientGroup.mk' elementarySubgroup) (shearElement r) := by
  simp only [integralShearToQuotient, MonoidHom.comp_apply, integralShearToQ_of]

theorem elementaryQuotient_elementary (r : Root) (m : Coeff) :
    (QuotientGroup.mk' elementarySubgroup) (ofGenerator (.inl (r, m))) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (ofGenerator_mem_elementarySubgroup r m)

theorem integralShearToQuotient_surjective : Function.Surjective integralShearToQuotient := by
  intro x
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective elementarySubgroup x
  have hq : q ∈ integralShearToQuotient.range.comap (QuotientGroup.mk' elementarySubgroup) := by
    apply generated_by
    intro g
    cases g with
    | inl p =>
        change (QuotientGroup.mk' elementarySubgroup) (ofGenerator (.inl (p.1, p.2))) ∈ integralShearToQuotient.range
        rw [elementaryQuotient_elementary]
        exact integralShearToQuotient.range.one_mem
    | inr r => exact ⟨IntegralShear.of r, integralShearToQuotient_of r⟩
  exact hq

end ThomGame.Compressor
