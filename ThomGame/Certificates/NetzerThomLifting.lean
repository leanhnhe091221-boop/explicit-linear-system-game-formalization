module

public import ThomGame.Certificates.NetzerThomRealCertificate
public import ThomGame.Analysis.FiniteUCPSOSWords

@[expose] public section
namespace ThomGame.Certificates.NetzerThom
open ThomGame.Analysis
open scoped BigOperators
noncomputable section

theorem list_sum_flatMap {α β : Type*} (l : List α) (w : α → List β) (F : β → ℝ) :
    ((l.flatMap w).map F).sum = (l.map (fun a => ((w a).map F).sum)).sum := by
  rw [List.map_flatMap]
  simp only [List.flatMap, List.sum_flatten, List.map_map, Function.comp_def]

theorem list_sum_sub {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem list_abs_sum_le {α : Type*} (l : List α) (a b : α → ℝ)
    (h : ∀ i ∈ l, |a i| ≤ b i) : |(l.map a).sum| ≤ (l.map b).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (h i (by simp))
        (ih (fun j hj => h j (by simp [hj]))))

theorem gramPartition_sum (F : ℕ × ℕ → ℝ) :
    (residualClasses.map (fun c => (c.pairs.map F).sum)).sum =
      ((List.range 121).map (fun i => ((List.range 121).map (fun j => F (i,j))).sum)).sum := by
  rw [← list_sum_flatMap]
  have hh := (gramPairs_partition.map F).sum_eq
  simpa only [list_sum_flatMap, List.map_map, Function.comp_def] using hh

theorem targetPartition_sum (F : ℕ → ℝ) :
    (residualClasses.map (fun c => (c.terms.map F).sum)).sum = ((List.range 182).map F).sum := by
  rw [← list_sum_flatMap]
  exact (targetIndices_partition.map F).sum_eq

theorem list_range_sum_fin (n : ℕ) (F : ℕ → ℝ) :
    ((List.range n).map F).sum = ∑ i : Fin n, F i := by
  rw [← Finset.sum_range]
  have he : (List.range n).toFinset = Finset.range n := by ext i; simp
  simpa only [he] using (List.sum_toFinset F (List.nodup_range (n := n))).symm

theorem finite_class_lifting (t : ℕ → ℝ) (g : ℕ × ℕ → ℝ) (r : ResidualClass → ℝ)
    {err : ℝ} (herr : 0 ≤ err)
    (ht : ∀ c ∈ residualClasses, ∀ i ∈ c.terms, |t i - r c| ≤ err)
    (hg : ∀ c ∈ residualClasses, ∀ ij ∈ c.pairs, |g ij - r c| ≤ err) :
    |((List.range 182).map (fun i => targetReal i * t i)).sum -
      ((List.range 121).map (fun i => ((List.range 121).map
        (fun j => gramReal (i,j) * g (i,j))).sum)).sum -
      (residualClasses.map (fun c => residualReal c * r c)).sum| ≤ 20600 * err := by
  let T (c : ResidualClass) := (c.terms.map (fun i => targetReal i * t i)).sum
  let G (c : ResidualClass) := (c.pairs.map (fun ij => gramReal ij * g ij)).sum
  let R (c : ResidualClass) := residualReal c * r c
  let MT (c : ResidualClass) := (c.terms.map (fun i => |targetReal i|)).sum
  let MG (c : ResidualClass) := (c.pairs.map (fun ij => |gramReal ij|)).sum
  have hc (c : ResidualClass) (hc : c ∈ residualClasses) :
      |T c - G c - R c| ≤ (MT c + MG c) * err := by
    have hat := finiteSOS_coefficient_transfer_list c.terms targetReal t (fun _ => r c) (ht c hc)
    have hag := finiteSOS_coefficient_transfer_list c.pairs gramReal g (fun _ => r c) (hg c hc)
    rw [List.sum_map_mul_right] at hat hag
    have he : T c - G c - R c =
        ((c.terms.map (fun i => targetReal i * t i)).sum - (c.terms.map targetReal).sum * r c) -
        ((c.pairs.map (fun ij => gramReal ij * g ij)).sum - (c.pairs.map gramReal).sum * r c) := by
      dsimp only [T,G,R]
      rw [residualReal_formula]
      ring
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add hat hag).trans_eq (by dsimp only [MT,MG]; ring))
  have hh := list_abs_sum_le residualClasses (fun c => T c - G c - R c)
    (fun c => (MT c + MG c) * err) hc
  simp only [list_sum_sub, List.sum_map_mul_right, List.sum_map_add] at hh
  have hm : (residualClasses.map MT).sum + (residualClasses.map MG).sum ≤ 20600 := by
    have h1 := targetReal_class_mass
    have h2 := gramReal_class_mass
    change (residualClasses.map MT).sum ≤ 600 at h1
    change (residualClasses.map MG).sum ≤ 20000 at h2
    linarith
  have hfinal := hh.trans (mul_le_mul_of_nonneg_right hm herr)
  dsimp only [T,G,R] at hfinal
  rw [targetPartition_sum, gramPartition_sum] at hfinal
  exact hfinal

variable {d : ℕ} [NeZero d]

theorem matrix_certificate_lifting (f : MatrixAssignment Compressor.Root d)
    {δ : ℝ} (hδ : 0 ≤ δ) (hf : IsApproxRepresentation IntegralShear.relators δ f)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    |((List.range 182).map (fun i => targetReal i *
        finiteSOSQuadratic (f (FreeGroup.mk (ntWord (targetTerms.getD i ([],0)).1))) X)).sum -
      ((List.range 121).map (fun i => ((List.range 121).map (fun j => gramReal (i,j) *
        finiteSOSQuadratic (f (FreeGroup.mk (gramWord (i,j)))) X)).sum)).sum -
      (residualClasses.map (fun c => residualReal c *
        finiteSOSQuadratic (f (FreeGroup.mk (ntWord c.representative))) X)).sum| ≤ 10000000 * δ := by
  have ht := finite_class_lifting
    (fun i => finiteSOSQuadratic (f (FreeGroup.mk (ntWord (targetTerms.getD i ([],0)).1))) X)
    (fun ij => finiteSOSQuadratic (f (FreeGroup.mk (gramWord ij))) X)
    (fun c => finiteSOSQuadratic (f (FreeGroup.mk (ntWord c.representative))) X)
    (err := 480 * δ) (by positivity)
    (fun c hc i hi => by
      simpa only [Nat.cast_ofNat, show (2 : ℝ) * 240 = 480 by norm_num] using
        finiteSOS_relator_quadratic_transfer (residualClasses_wordSound c hc |>.target i hi) f hδ hf X hX)
    (fun c hc ij hij => by
      simpa only [Nat.cast_ofNat, show (2 : ℝ) * 240 = 480 by norm_num] using
        finiteSOS_relator_quadratic_transfer (residualClasses_wordSound c hc |>.gram ij hij) f hδ hf X hX)
  exact ht.trans (by nlinarith)

theorem matrix_certificate_gram_nonneg (f : MatrixAssignment Compressor.Root d) (X : CMatrix d) :
    0 ≤ ((List.range 121).map (fun i => ((List.range 121).map (fun j => gramReal (i,j) *
      finiteSOSQuadratic (f (FreeGroup.mk (gramWord (i,j)))) X)).sum)).sum := by
  let U (i : Fin 121) := f (FreeGroup.mk (ntWord (basisWords.getD i [])))
  have hgram (i j : Fin 121) : f (FreeGroup.mk (gramWord (i,j))) = (U i)⁻¹ * U j := by
    simp only [gramWord, ← FreeGroup.mul_mk, Word.inverse, ← FreeGroup.inv_mk, map_mul, map_inv, U]
  have hh := finiteSOSQuadratic_gram_nonneg
    (fun (i : Fin 121) (k : Fin 112) => (rootCoefficient i k : ℝ)) U X
  have hcast (i j : Fin 121) : (gramEntry i j : ℝ) =
      ∑ k : Fin 112, (rootCoefficient i k : ℝ) * (rootCoefficient j k : ℝ) := by
    rw [gramEntry_formula]
    push_cast
    rfl
  have he : ((List.range 121).map (fun i => ((List.range 121).map (fun j => gramReal (i,j) *
      finiteSOSQuadratic (f (FreeGroup.mk (gramWord (i,j)))) X)).sum)).sum =
      (∑ i : Fin 121, ∑ j : Fin 121,
        (∑ k : Fin 112, (rootCoefficient i k : ℝ) * (rootCoefficient j k : ℝ)) *
          finiteSOSQuadratic ((U i)⁻¹ * U j) X) / denominator := by
    simp only [list_range_sum_fin, gramReal]
    simp_rw [div_mul_eq_mul_div, hgram, hcast]
    simp only [Finset.sum_div]
  rw [he]
  exact div_nonneg hh denominator_pos.le

theorem matrix_certificate_residual (f : MatrixAssignment Compressor.Root d) (X : CMatrix d)
    {D : ℝ} (hD : 0 ≤ D)
    (hcomm : ∀ r : Compressor.Root, finiteNoDriftComm (f (FreeGroup.of r)) X ^ 2 ≤ D) :
    -(9 / 100 : ℝ) * D ≤
      (residualClasses.map (fun c => residualReal c *
        finiteSOSQuadratic (f (FreeGroup.mk (ntWord c.representative))) X)).sum := by
  have hh := finiteSOS_matrix_residual_bound_list residualClasses residualReal
    (fun c => ntWord c.representative) (fun r => f (FreeGroup.of r)) X hD
    residualReal_sum residualReal_mass
    (fun c hc => by
      simpa only [ntWord, shearEncodedWord, List.length_map] using residualClass_word_length hc)
    (fun _ _ r _ _ => hcomm r)
  simpa only [Word.eval, assignment_eq_lift, show (4 : ℝ) * (9 / 400) = 9 / 100 by norm_num,
    neg_mul] using hh

end
end ThomGame.Certificates.NetzerThom
