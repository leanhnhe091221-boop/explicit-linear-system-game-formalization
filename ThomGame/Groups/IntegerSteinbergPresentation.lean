module

public import ThomGame.Groups.IntegralShearIntegerRoots

/-!
# The actual rank-three Steinberg presentation over the integers

The generators and three relation families are exactly (St1)--(St3)
in Ershov--Jaikin, Section 6. Property (T) is not assumed or asserted here.
-/

@[expose] public section
namespace ThomGame.IntegerSteinberg

open Compressor
open scoped commutatorElement

abbrev Generator := Root × ℤ

inductive Relation
  | additive (r : Root) (m n : ℤ)
  | separated (p : {p : Root × Root // Compressor.separated p.1 p.2}) (m n : ℤ)
  | adjacent (r : Root) (m n : ℤ)

def relator : Relation → FreeGroup Generator
  | .additive r m n => FreeGroup.of (r, m + n) * (FreeGroup.of (r, m) * FreeGroup.of (r, n))⁻¹
  | .separated p m n => ⁅FreeGroup.of (p.val.1, m), FreeGroup.of (p.val.2, n)⁆
  | .adjacent r m n => ⁅FreeGroup.of (r, m), FreeGroup.of (right r, n)⁆ * (FreeGroup.of (across r, m * n))⁻¹

def relators : Set (FreeGroup Generator) := Set.range relator

def St3Z := PresentedGroup relators
  deriving Group

def of (r : Root) (m : ℤ) : St3Z := PresentedGroup.of (r, m)

structure Model (G : Type*) [Group G] where
  x : Root → ℤ → G
  additive : ∀ r m n, x r (m + n) = x r m * x r n
  separated : ∀ r s, Compressor.separated r s → ∀ m n, Commute (x r m) (x s n)
  adjacent : ∀ r m n, ⁅x r m, x (right r) n⁆ = x (across r) (m * n)

namespace Model

variable {G : Type*} [Group G] (M : Model G)

theorem eval_relator (r : Relation) : FreeGroup.lift (fun g : Generator => M.x g.1 g.2) (relator r) = 1 := by
  cases r with
  | additive r m n => simp [relator, M.additive]
  | separated p m n => simpa [relator] using (M.separated p.val.1 p.val.2 p.property m n).commutator_eq
  | adjacent r m n => simp [relator, M.adjacent]

def toHom : St3Z →* G := PresentedGroup.toGroup (f := fun g : Generator => M.x g.1 g.2) (by
  intro w hw
  obtain ⟨r, rfl⟩ := hw
  exact M.eval_relator r)

@[simp] theorem toHom_of (r : Root) (m : ℤ) : M.toHom (of r m) = M.x r m := PresentedGroup.toGroup.of _

theorem x_zero (r : Root) : M.x r 0 = 1 := by
  have h : M.x r 0 * 1 = M.x r 0 * M.x r 0 := by
    simpa only [mul_one, zero_add] using M.additive r 0 0
  exact (mul_left_cancel h).symm

def rootHom (r : Root) : Multiplicative ℤ →* G where
  toFun m := M.x r m.toAdd
  map_one' := M.x_zero r
  map_mul' m n := M.additive r m.toAdd n.toAdd

theorem x_eq_zpow (r : Root) (m : ℤ) : M.x r m = M.x r 1 ^ m := by
  have h := map_zpow (M.rootHom r) (Multiplicative.ofAdd 1) m
  change M.x r (m • (1 : ℤ)) = M.x r 1 ^ m at h
  simpa [zsmul_eq_mul] using h

theorem adjacent_indices (i j k : Axis) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (m n : ℤ) :
    ⁅M.x ⟨(i, j), hij⟩ m, M.x ⟨(j, k), hjk⟩ n⁆ = M.x ⟨(i, k), hik⟩ (m * n) := by
  obtain ⟨hr, ha⟩ := PrimeFiveRankThreeCover.path_indices i j k hij hik.symm hjk.symm
  simpa only [hr, ha] using M.adjacent ⟨(i, j), hij⟩ m n

end Model

set_option backward.isDefEq.respectTransparency false in
theorem of_additive (r : Root) (m n : ℤ) : of r (m + n) = of r m * of r n := by
  have h : (PresentedGroup.mk relators : FreeGroup Generator →* St3Z) (relator (.additive r m n)) = 1 :=
    PresentedGroup.one_of_mem (rels := relators) ⟨Relation.additive r m n, rfl⟩
  simpa only [relator, map_mul, map_inv, mul_inv_eq_one, of, PresentedGroup.of] using h

set_option backward.isDefEq.respectTransparency false in
theorem of_commute (r s : Root) (hrs : separated r s) (m n : ℤ) : Commute (of r m) (of s n) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have h : (PresentedGroup.mk relators : FreeGroup Generator →* St3Z)
      (relator (.separated ⟨(r, s), hrs⟩ m n)) = 1 :=
    PresentedGroup.one_of_mem (rels := relators) ⟨Relation.separated ⟨(r, s), hrs⟩ m n, rfl⟩
  simpa only [relator, map_commutatorElement, of, PresentedGroup.of] using h

set_option backward.isDefEq.respectTransparency false in
theorem of_adjacent (r : Root) (m n : ℤ) : ⁅of r m, of (right r) n⁆ = of (across r) (m * n) := by
  have h : (PresentedGroup.mk relators : FreeGroup Generator →* St3Z) (relator (.adjacent r m n)) = 1 :=
    PresentedGroup.one_of_mem (rels := relators) ⟨Relation.adjacent r m n, rfl⟩
  simpa only [relator, map_mul, map_inv, map_commutatorElement, mul_inv_eq_one, of, PresentedGroup.of] using h

def canonicalModel : Model St3Z where
  x := of
  additive := of_additive
  separated := of_commute
  adjacent := of_adjacent

theorem of_eq_zpow (r : Root) (m : ℤ) : of r m = of r 1 ^ m := canonicalModel.x_eq_zpow r m

theorem unitRootElements_generate : Subgroup.closure (Set.range (fun r : Root => of r 1)) = ⊤ := by
  apply top_unique
  intro x _
  apply PresentedGroup.generated_by relators (Subgroup.closure (Set.range (fun r : Root => of r 1))) _ x
  rintro ⟨r, m⟩
  change of r m ∈ _
  rw [of_eq_zpow]
  have hunit : of r 1 ∈ Subgroup.closure (Set.range (fun s : Root => of s 1)) :=
    Subgroup.subset_closure ⟨r, rfl⟩
  exact Subgroup.zpow_mem _ hunit m

def shearModel : Model IntegralShear.ShearGroup where
  x := IntegralShear.rootElement
  additive := IntegralShear.rootElement_add
  separated := IntegralShear.rootElement_commute
  adjacent := IntegralShear.rootElement_commutator

def toShear : St3Z →* IntegralShear.ShearGroup := shearModel.toHom

@[simp] theorem toShear_of (r : Root) (m : ℤ) : toShear (of r m) = IntegralShear.rootElement r m :=
  shearModel.toHom_of r m

theorem toShear_surjective : Function.Surjective toShear := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← IntegralShear.rootElements_generate]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨r, rfl⟩
  exact ⟨of r 1, by simp⟩

end ThomGame.IntegerSteinberg
