module

public import ThomGame.Analysis.ShearRankOneCertificates
public import ThomGame.Certificates.NetzerThomResidualData

/-! A proof-producing checker for the finite word-class witnesses. The search
program is untrusted: every path is checked against actual defining relators. -/

@[expose] public section
namespace ThomGame.Certificates.NetzerThom
open ThomGame.Analysis

def ntLetter (a : ℕ) : ℕ :=
  if a = 4 then 6 else if a = 5 then 7 else if a = 6 then 4 else if a = 7 then 5 else a

def ntWord (w : List ℕ) : Word Compressor.Root := shearEncodedWord (w.map ntLetter)

def shortCertificate (i : ℕ) : ShearRelatorCertificate 60 :=
  shearShortCertificates.getD i shearRankOneCertificate0

structure WordPathStep where
  certificate : ℕ
  reverse : Bool
  rotation : ℕ
  split : ℕ
  pre : List ℕ
  post : List ℕ
  next : List ℕ
  deriving DecidableEq

def WordPathStep.rule (s : WordPathStep) :=
  let C := shortCertificate s.certificate
  CertifiedWordRule.fromRelator C.word C.area s.reverse s.rotation s.split

/-- Paths run backwards along the stored, certified rewrite edge. -/
def wordPathCheck : Word Compressor.Root → List ℕ → List WordPathStep → Bool
  | w, target, [] => decide (FreeGroup.mk w =
      FreeGroup.mk (shearEncodedWord target))
  | w, target, s :: ss =>
      decide (FreeGroup.mk (shearEncodedWord s.next) =
        FreeGroup.mk (shearEncodedWord s.pre) * FreeGroup.mk s.rule.lhs *
          FreeGroup.mk (shearEncodedWord s.post)) &&
      decide (FreeGroup.mk w =
        FreeGroup.mk (shearEncodedWord s.pre) * FreeGroup.mk s.rule.rhs *
          FreeGroup.mk (shearEncodedWord s.post)) &&
      wordPathCheck (shearEncodedWord s.next) target ss

theorem wordPathCheck_sound (w : Word Compressor.Root) (target : List ℕ) (ss : List WordPathStep)
    (h : wordPathCheck w target ss = true) :
    RelatorEquality IntegralShear.relators (FreeGroup.mk w)
      (FreeGroup.mk (shearEncodedWord target)) (60 * ss.length) := by
  induction ss generalizing w with
  | nil =>
      simp only [wordPathCheck, decide_eq_true_eq] at h
      exact RelatorEquality.of_eq h
  | cons s ss ih =>
      simp only [wordPathCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      have he := (s.rule.contextual_sound (shearEncodedWord s.pre)
        (shearEncodedWord s.post) _ _ h.1.1 h.1.2).symm
      have ht := he.trans (ih (shearEncodedWord s.next) h.2)
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm 60] using ht

structure WordClassPaths where
  gram : List (List WordPathStep)
  target : List (List WordPathStep)

def gramWord (ij : ℕ × ℕ) : Word Compressor.Root :=
  Word.inverse (ntWord (basisWords.getD ij.1 [])) ++ ntWord (basisWords.getD ij.2 [])

def gramEncodedWord (ij : ℕ × ℕ) : List ℕ :=
  ((basisWords.getD ij.1 []).reverse.map (fun a => ntLetter a ^^^ 1)) ++
    (basisWords.getD ij.2 []).map ntLetter

def checkedPath (w : Word Compressor.Root) (target : List ℕ) (p : List WordPathStep) : Bool :=
  decide (p.length ≤ 4) && wordPathCheck w target p

def wordClassCheck (c : ResidualClass) (p : WordClassPaths) : Bool :=
  decide (p.gram.length = c.pairs.length) &&
  decide (p.target.length = c.terms.length) &&
  (c.pairs.zip p.gram).all (fun e =>
    checkedPath (gramWord e.1) (c.representative.map ntLetter) e.2) &&
  (c.terms.zip p.target).all (fun e =>
    checkedPath (ntWord (targetTerms.getD e.1 ([],0)).1)
      (c.representative.map ntLetter) e.2)

theorem checkedPath_sound {w : Word Compressor.Root} {v : List ℕ} {p : List WordPathStep}
    (h : checkedPath w v p = true) :
    RelatorEquality IntegralShear.relators (FreeGroup.mk w)
      (FreeGroup.mk (shearEncodedWord v)) 240 := by
  simp only [checkedPath, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (wordPathCheck_sound w v p h.2).mono (by omega)

end ThomGame.Certificates.NetzerThom
