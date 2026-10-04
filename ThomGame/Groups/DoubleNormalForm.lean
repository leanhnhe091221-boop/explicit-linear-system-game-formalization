module

public import ThomGame.Groups.DoubleToLambda
public import ThomGame.Groups.AmalgamPowers
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.Group

/-!
# The obstruction word and strict compression

The actual specified word is conjugate to an alternating two-letter word
in Q *_H Q. Its infinite order follows from the single remaining strictness
condition t⁻¹ h t ∉ H. That condition requires the Laurent matrix model and
is an explicit hypothesis here, not an asserted fact or a custom axiom.
-/

@[expose] public section
namespace ThomGame.Double

theorem obstruction_conjugate :
    t₂Element⁻¹ * obstructionElement * t₂Element =
      copyHom true Compressor.backwardConjugate * copyHom false Compressor.backwardConjugate⁻¹ := by
  rw [obstruction_formula]
  simp only [Compressor.backwardConjugate, Compressor.hElement, Compressor.tElement,
    map_mul, map_inv, copy_h, copy_t₁, copy_t₂]
  group

theorem obstruction_pow_ne_one
    (hstrict : Compressor.backwardConjugate ∉ Compressor.positiveSubgroup)
    (n : Nat) (hn : 0 < n) : obstructionElement ^ n ≠ 1 := by
  intro hp
  have hconj : (t₂Element⁻¹ * obstructionElement * t₂Element) ^ n = 1 := by
    simpa only [inv_inv, hp, mul_one, inv_mul_cancel] using
      (conj_pow (a := t₂Element⁻¹) (b := obstructionElement) (i := n))
  rw [obstruction_conjugate] at hconj
  have hamalgam := congrArg amalgamEquiv hconj
  simp only [map_pow, map_mul, amalgamEquiv_copy, map_one] at hamalgam
  have hx : Compressor.backwardConjugate ∉ (amalgamMaps true).range := by
    simpa only [amalgamMaps, Subgroup.range_subtype] using hstrict
  have hy : Compressor.backwardConjugate⁻¹ ∉ (amalgamMaps false).range := by
    simpa only [amalgamMaps, Subgroup.range_subtype, Subgroup.inv_mem_iff] using hstrict
  exact AmalgamPowers.alternating_pow_ne_one amalgamMaps true false (by decide)
    Compressor.backwardConjugate Compressor.backwardConjugate⁻¹ hx hy
    (fun _ => Subtype.val_injective) n hn hamalgam

theorem obstruction_not_isOfFinOrder
    (hstrict : Compressor.backwardConjugate ∉ Compressor.positiveSubgroup) :
    ¬ IsOfFinOrder obstructionElement := by
  intro h
  obtain ⟨n, hn, hp⟩ := h.exists_pow_eq_one
  exact obstruction_pow_ne_one hstrict n hn hp

end ThomGame.Double
