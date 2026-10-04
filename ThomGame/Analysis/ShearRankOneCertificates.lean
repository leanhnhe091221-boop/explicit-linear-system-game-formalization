module

public import ThomGame.Analysis.ShearWeylCertificates

/-! Weyl variants and rank-one length-four identities with area at most sixty. -/

@[expose] public section
namespace ThomGame.Analysis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shearWeylCertificate0 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [0, 5, 0]) (shearEncodedWord [5, 0, 5])
  area := by
    apply wordRelatorArea_of_equality
    exact shearWeyl0

def shearWeylCertificate1 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [1, 4, 1]) (shearEncodedWord [4, 1, 4])
  area := by
    apply wordRelatorArea_of_equality
    have h := shearWeyl0.inv
    convert h using 1 <;> decide +kernel

def shearWeylCertificate2 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [2, 9, 2]) (shearEncodedWord [9, 2, 9])
  area := by
    apply wordRelatorArea_of_equality
    exact shearWeyl1

def shearWeylCertificate3 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [3, 8, 3]) (shearEncodedWord [8, 3, 8])
  area := by
    apply wordRelatorArea_of_equality
    have h := shearWeyl1.inv
    convert h using 1 <;> decide +kernel

def shearWeylCertificate4 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [4, 1, 4]) (shearEncodedWord [1, 4, 1])
  area := by
    apply wordRelatorArea_of_equality
    exact shearWeyl2

def shearWeylCertificate5 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [5, 0, 5]) (shearEncodedWord [0, 5, 0])
  area := by
    apply wordRelatorArea_of_equality
    have h := shearWeyl2.inv
    convert h using 1 <;> decide +kernel

def shearWeylCertificate6 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [6, 11, 6]) (shearEncodedWord [11, 6, 11])
  area := by
    apply wordRelatorArea_of_equality
    exact shearWeyl3

def shearWeylCertificate7 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [7, 10, 7]) (shearEncodedWord [10, 7, 10])
  area := by
    apply wordRelatorArea_of_equality
    have h := shearWeyl3.inv
    convert h using 1 <;> decide +kernel

def shearWeylCertificate8 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [8, 3, 8]) (shearEncodedWord [3, 8, 3])
  area := by
    apply wordRelatorArea_of_equality
    exact shearWeyl4

def shearWeylCertificate9 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [9, 2, 9]) (shearEncodedWord [2, 9, 2])
  area := by
    apply wordRelatorArea_of_equality
    have h := shearWeyl4.inv
    convert h using 1 <;> decide +kernel

def shearWeylCertificate10 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [10, 7, 10]) (shearEncodedWord [7, 10, 7])
  area := by
    apply wordRelatorArea_of_equality
    exact shearWeyl5

def shearWeylCertificate11 : ShearRelatorCertificate 30 where
  word := Word.equation (shearEncodedWord [11, 6, 11]) (shearEncodedWord [6, 11, 6])
  area := by
    apply wordRelatorArea_of_equality
    have h := shearWeyl5.inv
    convert h using 1 <;> decide +kernel

def shearRankOneCertificate0 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [0, 4, 4, 1]) (shearEncodedWord [4, 1, 1, 5])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate0
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 2 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [0, 4, 4, 1]))
        (FreeGroup.mk (shearEncodedWord [4, 1, 5, 0, 4, 1])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [4, 4, 1]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate0
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 1 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [4, 1, 5, 0, 4, 1]))
        (FreeGroup.mk (shearEncodedWord [4, 1, 1, 5])) 30 :=
      R1.contextual_sound (shearEncodedWord [4, 1])
        (shearEncodedWord [0, 4, 1]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def shearRankOneCertificate1 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [1, 5, 5, 0]) (shearEncodedWord [5, 0, 0, 4])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate0
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area true 5 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [1, 5, 5, 0]))
        (FreeGroup.mk (shearEncodedWord [5, 0, 4, 1, 5, 0])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [5, 5, 0]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate0
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area true 4 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [5, 0, 4, 1, 5, 0]))
        (FreeGroup.mk (shearEncodedWord [5, 0, 0, 4])) 30 :=
      R1.contextual_sound (shearEncodedWord [5, 0])
        (shearEncodedWord [1, 5, 0]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def shearRankOneCertificate2 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [2, 8, 8, 3]) (shearEncodedWord [8, 3, 3, 9])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate2
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 2 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [2, 8, 8, 3]))
        (FreeGroup.mk (shearEncodedWord [8, 3, 9, 2, 8, 3])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [8, 8, 3]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate2
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 1 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [8, 3, 9, 2, 8, 3]))
        (FreeGroup.mk (shearEncodedWord [8, 3, 3, 9])) 30 :=
      R1.contextual_sound (shearEncodedWord [8, 3])
        (shearEncodedWord [2, 8, 3]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def shearRankOneCertificate3 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [3, 9, 9, 2]) (shearEncodedWord [9, 2, 2, 8])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate2
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area true 5 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [3, 9, 9, 2]))
        (FreeGroup.mk (shearEncodedWord [9, 2, 8, 3, 9, 2])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [9, 9, 2]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate2
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area true 4 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [9, 2, 8, 3, 9, 2]))
        (FreeGroup.mk (shearEncodedWord [9, 2, 2, 8])) 30 :=
      R1.contextual_sound (shearEncodedWord [9, 2])
        (shearEncodedWord [3, 9, 2]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def shearRankOneCertificate4 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [4, 0, 0, 5]) (shearEncodedWord [0, 5, 5, 1])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate0
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 5 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [4, 0, 0, 5]))
        (FreeGroup.mk (shearEncodedWord [0, 5, 1, 4, 0, 5])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [0, 0, 5]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate0
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 4 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [0, 5, 1, 4, 0, 5]))
        (FreeGroup.mk (shearEncodedWord [0, 5, 5, 1])) 30 :=
      R1.contextual_sound (shearEncodedWord [0, 5])
        (shearEncodedWord [4, 0, 5]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def shearRankOneCertificate5 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [5, 1, 1, 4]) (shearEncodedWord [1, 4, 4, 0])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate0
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area true 2 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [5, 1, 1, 4]))
        (FreeGroup.mk (shearEncodedWord [1, 4, 0, 5, 1, 4])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [1, 1, 4]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate0
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area true 1 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [1, 4, 0, 5, 1, 4]))
        (FreeGroup.mk (shearEncodedWord [1, 4, 4, 0])) 30 :=
      R1.contextual_sound (shearEncodedWord [1, 4])
        (shearEncodedWord [5, 1, 4]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def shearRankOneCertificate6 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [6, 10, 10, 7]) (shearEncodedWord [10, 7, 7, 11])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate6
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 2 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [6, 10, 10, 7]))
        (FreeGroup.mk (shearEncodedWord [10, 7, 11, 6, 10, 7])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [10, 10, 7]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate6
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 1 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [10, 7, 11, 6, 10, 7]))
        (FreeGroup.mk (shearEncodedWord [10, 7, 7, 11])) 30 :=
      R1.contextual_sound (shearEncodedWord [10, 7])
        (shearEncodedWord [6, 10, 7]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def shearRankOneCertificate7 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [7, 11, 11, 6]) (shearEncodedWord [11, 6, 6, 10])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate6
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area true 5 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [7, 11, 11, 6]))
        (FreeGroup.mk (shearEncodedWord [11, 6, 10, 7, 11, 6])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [11, 11, 6]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate6
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area true 4 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [11, 6, 10, 7, 11, 6]))
        (FreeGroup.mk (shearEncodedWord [11, 6, 6, 10])) 30 :=
      R1.contextual_sound (shearEncodedWord [11, 6])
        (shearEncodedWord [7, 11, 6]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def shearRankOneCertificate8 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [8, 2, 2, 9]) (shearEncodedWord [2, 9, 9, 3])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate2
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 5 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [8, 2, 2, 9]))
        (FreeGroup.mk (shearEncodedWord [2, 9, 3, 8, 2, 9])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [2, 2, 9]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate2
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 4 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [2, 9, 3, 8, 2, 9]))
        (FreeGroup.mk (shearEncodedWord [2, 9, 9, 3])) 30 :=
      R1.contextual_sound (shearEncodedWord [2, 9])
        (shearEncodedWord [8, 2, 9]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def shearRankOneCertificate9 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [9, 3, 3, 8]) (shearEncodedWord [3, 8, 8, 2])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate2
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area true 2 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [9, 3, 3, 8]))
        (FreeGroup.mk (shearEncodedWord [3, 8, 2, 9, 3, 8])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [3, 3, 8]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate2
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area true 1 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [3, 8, 2, 9, 3, 8]))
        (FreeGroup.mk (shearEncodedWord [3, 8, 8, 2])) 30 :=
      R1.contextual_sound (shearEncodedWord [3, 8])
        (shearEncodedWord [9, 3, 8]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def shearRankOneCertificate10 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [10, 6, 6, 11]) (shearEncodedWord [6, 11, 11, 7])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate6
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 5 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [10, 6, 6, 11]))
        (FreeGroup.mk (shearEncodedWord [6, 11, 7, 10, 6, 11])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [6, 6, 11]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate6
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 4 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [6, 11, 7, 10, 6, 11]))
        (FreeGroup.mk (shearEncodedWord [6, 11, 11, 7])) 30 :=
      R1.contextual_sound (shearEncodedWord [6, 11])
        (shearEncodedWord [10, 6, 11]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def shearRankOneCertificate11 : ShearRelatorCertificate 60 where
  word := Word.equation (shearEncodedWord [11, 7, 7, 10]) (shearEncodedWord [7, 10, 10, 6])
  area := by
    apply wordRelatorArea_of_equality
    let C0 := shearWeylCertificate6
    let R0 := CertifiedWordRule.fromRelator C0.word C0.area true 2 1
    have h0 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [11, 7, 7, 10]))
        (FreeGroup.mk (shearEncodedWord [7, 10, 6, 11, 7, 10])) 30 :=
      R0.contextual_sound (shearEncodedWord [])
        (shearEncodedWord [7, 7, 10]) _ _ (by decide +kernel) (by decide +kernel)
    let C1 := shearWeylCertificate6
    let R1 := CertifiedWordRule.fromRelator C1.word C1.area true 1 1
    have h1 : RelatorEquality IntegralShear.relators
        (FreeGroup.mk (shearEncodedWord [7, 10, 6, 11, 7, 10]))
        (FreeGroup.mk (shearEncodedWord [7, 10, 10, 6])) 30 :=
      R1.contextual_sound (shearEncodedWord [7, 10])
        (shearEncodedWord [11, 7, 10]) _ _ (by decide +kernel) (by decide +kernel)
    exact h0.trans h1

def ShearRelatorCertificate.weaken {M N : ℕ}
    (C : ShearRelatorCertificate M) (hMN : M ≤ N) : ShearRelatorCertificate N where
  word := C.word
  area := by
    obtain ⟨n, hn, hp⟩ := C.area
    exact ⟨n, hn.trans hMN, hp⟩

def shearShortCertificates : List (ShearRelatorCertificate 60) :=
  (shearElementaryCertificates.map (fun C => C.weaken (by decide))) ++
  ([shearWeylCertificate0, shearWeylCertificate1, shearWeylCertificate2, shearWeylCertificate3, shearWeylCertificate4, shearWeylCertificate5, shearWeylCertificate6, shearWeylCertificate7, shearWeylCertificate8, shearWeylCertificate9, shearWeylCertificate10, shearWeylCertificate11].map
    (fun C => C.weaken (by decide))) ++
  [shearRankOneCertificate0, shearRankOneCertificate1, shearRankOneCertificate2, shearRankOneCertificate3, shearRankOneCertificate4, shearRankOneCertificate5, shearRankOneCertificate6, shearRankOneCertificate7, shearRankOneCertificate8, shearRankOneCertificate9, shearRankOneCertificate10, shearRankOneCertificate11]

def shearShortRules : List (CertifiedWordRule IntegralShear.relators 60) :=
  shearShortCertificates.flatMap ShearRelatorCertificate.rules

end ThomGame.Analysis
