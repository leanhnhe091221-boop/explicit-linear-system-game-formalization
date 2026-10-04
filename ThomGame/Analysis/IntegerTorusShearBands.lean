module

public import ThomGame.Analysis.IntegerTorusCoordinates

/-! Four disjoint bands obtained by three and six integer shears of small cones. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerTorus

open Set MeasureTheory
open scoped Function

def smallSquare : Set Torus := {x | |rep x.1| ≤ 1 / 16 ∧ |rep x.2| ≤ 1 / 16}

def cone (vertical : Bool) : Set Torus :=
  {x | x ∈ smallSquare ∧ x ≠ 0 ∧
    if vertical then |rep x.1| < |rep x.2| else |rep x.2| ≤ |rep x.1|}

def shift (far : Bool) : ℤ := if far then 6 else 3

def shearMap (i : Bool × Bool) : Torus ≃ₜ Torus :=
  if i.1 then upper (shift i.2) else lower (shift i.2)

def band (i : Bool × Bool) : Set Torus := {x |
  if i.1 then
    0 < |rep x.2| ∧ ((shift i.2 : ℤ) : ℝ) * |rep x.2| - |rep x.2| ≤ |rep x.1| ∧
      |rep x.1| ≤ ((shift i.2 : ℤ) : ℝ) * |rep x.2| + |rep x.2|
  else
    0 < |rep x.1| ∧ ((shift i.2 : ℤ) : ℝ) * |rep x.1| - |rep x.1| ≤ |rep x.2| ∧
      |rep x.2| ≤ ((shift i.2 : ℤ) : ℝ) * |rep x.1| + |rep x.1|}

theorem smallSquare_measurable : MeasurableSet smallSquare :=
  (measurableSet_le (continuous_abs.measurable.comp (rep_measurable.comp measurable_fst)) measurable_const).inter
    (measurableSet_le (continuous_abs.measurable.comp (rep_measurable.comp measurable_snd)) measurable_const)

theorem cone_measurable (b : Bool) : MeasurableSet (cone b) := by
  cases b
  · exact smallSquare_measurable.inter ((measurableSet_singleton (0 : Torus)).compl.inter
      (measurableSet_le (continuous_abs.measurable.comp (rep_measurable.comp measurable_snd))
        (continuous_abs.measurable.comp (rep_measurable.comp measurable_fst))))
  · exact smallSquare_measurable.inter ((measurableSet_singleton (0 : Torus)).compl.inter
      (measurableSet_lt (continuous_abs.measurable.comp (rep_measurable.comp measurable_fst))
        (continuous_abs.measurable.comp (rep_measurable.comp measurable_snd))))

theorem cones_disjoint : Disjoint (cone false) (cone true) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (not_lt_of_ge hx.2.2) hy.2.2

theorem cones_union : cone false ∪ cone true = smallSquare \ {0} := by
  ext x
  simp only [cone, Set.mem_union, Set.mem_ofPred_eq, Bool.false_eq_true, ↓reduceIte,
    Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h) <;> exact ⟨h.1, h.2.1⟩
  · rintro ⟨hs, hn⟩
    rcases le_or_gt |rep x.2| |rep x.1| with h | h
    · exact Or.inl ⟨hs, hn, h⟩
    · exact Or.inr ⟨hs, hn, h⟩

theorem shear_abs_bounds {a b k : ℝ} (hk : 0 ≤ k) (hab : |b| ≤ |a|) :
    k * |a| - |a| ≤ |k * a + b| ∧ |k * a + b| ≤ k * |a| + |a| := by
  have hup := abs_add_le (k * a) b
  have hlo := abs_add_le (k * a + b) (-b)
  rw [abs_mul, abs_of_nonneg hk] at hup
  simp only [add_neg_cancel_right, abs_mul, abs_of_nonneg hk, abs_neg] at hlo
  constructor <;> linarith

theorem shear_small {a b : ℝ} (ha : |a| ≤ 1 / 16) (hb : |b| ≤ 1 / 16) (f : Bool) :
    |((shift f : ℤ) : ℝ) * a + b| < 1 / 2 := by
  have h := abs_add_le (((shift f : ℤ) : ℝ) * a) b
  rw [abs_mul] at h
  cases f <;> norm_num [shift] at h ⊢ <;> linarith

theorem lower_rep_on_small (f : Bool) (x : Torus) (hx : x ∈ smallSquare) :
    pointRep (lower (shift f) x) = (rep x.1, ((shift f : ℤ) : ℝ) * rep x.1 + rep x.2) := by
  have h := shear_small hx.1 hx.2 f
  have h₁ : rep x.1 ∈ Ico (-(1 / 2 : ℝ)) (1 / 2) := rep_mem x.1
  have h₂ : ((shift f : ℤ) : ℝ) * rep x.1 + rep x.2 ∈ Ico (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2⟩
  conv_lhs => rw [← ofReal_pointRep x, lower_ofReal]
  exact pointRep_ofReal _ h₁ h₂

theorem upper_rep_on_small (f : Bool) (x : Torus) (hx : x ∈ smallSquare) :
    pointRep (upper (shift f) x) = (((shift f : ℤ) : ℝ) * rep x.2 + rep x.1, rep x.2) := by
  have h := shear_small hx.2 hx.1 f
  have h₁ : ((shift f : ℤ) : ℝ) * rep x.2 + rep x.1 ∈ Ico (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2⟩
  have h₂ : rep x.2 ∈ Ico (-(1 / 2 : ℝ)) (1 / 2) := rep_mem x.2
  conv_lhs => rw [← ofReal_pointRep x, upper_ofReal]
  exact pointRep_ofReal _ h₁ h₂

theorem coneImage_subset_band (i : Bool × Bool) : shearMap i '' cone i.1 ⊆ band i := by
  rintro y ⟨x, hx, rfl⟩
  have hn : ¬(rep x.1 = 0 ∧ rep x.2 = 0) := by
    intro hz
    apply hx.2.1
    exact Prod.ext ((rep_eq_zero_iff _).mp hz.1) ((rep_eq_zero_iff _).mp hz.2)
  rcases i with ⟨b, f⟩
  have hk : (0 : ℝ) ≤ ((shift f : ℤ) : ℝ) := by cases f <;> norm_num [shift]
  cases b
  · have he := lower_rep_on_small f x hx.1
    have hb := shear_abs_bounds hk hx.2.2
    have hp : 0 < |rep x.1| := by
      by_contra h
      have hx0 : rep x.1 = 0 := abs_eq_zero.mp (le_antisymm (le_of_not_gt h) (abs_nonneg _))
      have hy0 : rep x.2 = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hx0] using hx.2.2) (abs_nonneg _))
      exact hn ⟨hx0, hy0⟩
    simp only [band, shearMap, Set.mem_ofPred_eq, Bool.false_eq_true, ↓reduceIte]
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    change rep (lower (shift f) x).1 = _ at hfst
    change rep (lower (shift f) x).2 = _ at hsnd
    rw [hfst, hsnd]
    exact ⟨hp, hb⟩
  · have he := upper_rep_on_small f x hx.1
    have hb := shear_abs_bounds hk hx.2.2.le
    have hp : 0 < |rep x.2| := (abs_nonneg _).trans_lt hx.2.2
    simp only [band, shearMap, Set.mem_ofPred_eq, ↓reduceIte]
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    change rep (upper (shift f) x).1 = _ at hfst
    change rep (upper (shift f) x).2 = _ at hsnd
    rw [hfst, hsnd]
    exact ⟨hp, hb⟩

theorem bands_pairwise_disjoint : Pairwise (Disjoint on band) := by
  rintro ⟨b, f⟩ ⟨c, g⟩ hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  cases b <;> cases f <;> cases c <;> cases g <;>
    simp only [band, shift, Set.mem_ofPred_eq, Bool.false_eq_true, ↓reduceIte,
      Int.cast_ofNat] at hx hy hne <;> try contradiction
  all_goals rcases hx with ⟨h₁, h₂, h₃⟩; rcases hy with ⟨h₄, h₅, h₆⟩; linarith

theorem coneImages_pairwise_disjoint : Pairwise (Disjoint on fun i => shearMap i '' cone i.1) := by
  intro i j hij
  exact (bands_pairwise_disjoint hij).mono (coneImage_subset_band i) (coneImage_subset_band j)

theorem coneImage_measurable (i : Bool × Bool) : MeasurableSet (shearMap i '' cone i.1) :=
  (shearMap i).measurableEmbedding.measurableSet_image' (cone_measurable i.1)

end ThomGame.Analysis.IntegerTorus
