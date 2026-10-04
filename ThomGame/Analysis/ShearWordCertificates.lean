module

public import ThomGame.Analysis.ShearSignedRelatorArea
public import ThomGame.Analysis.WordAreaCertificates

/-! Finite certified elementary rewriting rules for the six shear generators. -/

@[expose] public section
namespace ThomGame.Analysis

open Compressor

theorem mk_shearSigned (r : Root) (a : Bool) :
    FreeGroup.mk [(r,a)] = shearSigned r a := by
  cases a <;> rfl

theorem wordRelatorArea_of_equality {S : Type*} {rels : Set (FreeGroup S)}
    {u v : Word S} {N : ℕ}
    (h : RelatorEquality rels (FreeGroup.mk u) (FreeGroup.mk v) N) :
    WordRelatorArea rels (Word.equation u v) N := by
  simpa only [RelatorEquality, WordRelatorArea, Word.equation, Word.inverse,
    ← FreeGroup.mul_mk, ← FreeGroup.inv_mk] using h

structure ShearRelatorCertificate (N : ℕ) where
  word : Word Root
  area : WordRelatorArea IntegralShear.relators word N

def shearSeparatedCertificate (r s : Root) (hrs : separated r s) (a b : Bool) :
    ShearRelatorCertificate 3 where
  word := Word.equation ([(r,a)] ++ [(s,b)]) ([(s,b)] ++ [(r,a)])
  area := by
    apply wordRelatorArea_of_equality
    simp only [← FreeGroup.mul_mk, mk_shearSigned]
    exact (shear_signed_separated_area r s hrs a b).mono (by decide)

def shearRootCertificate (r : Root) (a b : Bool) : ShearRelatorCertificate 3 where
  word := Word.equation ([(r,a)] ++ [(right r,b)])
    ([(across r,a == b)] ++ [(right r,b)] ++ [(r,a)])
  area := by
    apply wordRelatorArea_of_equality
    simp only [← FreeGroup.mul_mk, mk_shearSigned]
    exact shear_signed_root_area r a b

def shearElementaryCertificates : List (ShearRelatorCertificate 3) :=
  (roots.flatMap fun r => roots.flatMap fun s =>
    if hrs : separated r s then
      [true,false].flatMap fun a => [true,false].map fun b =>
        shearSeparatedCertificate r s hrs a b
    else []) ++
  roots.flatMap fun r => [true,false].flatMap fun a => [true,false].map fun b =>
    shearRootCertificate r a b

def ShearRelatorCertificate.rules {N : ℕ} (C : ShearRelatorCertificate N) :
    List (CertifiedWordRule IntegralShear.relators N) :=
  [false,true].flatMap fun reverse => (List.range C.word.length).flatMap fun rotation =>
    (List.range (C.word.length+1)).map fun split =>
      CertifiedWordRule.fromRelator C.word C.area reverse rotation split

def shearElementaryRules : List (CertifiedWordRule IntegralShear.relators 3) :=
  shearElementaryCertificates.flatMap ShearRelatorCertificate.rules

end ThomGame.Analysis
