# Checking only the nonlocal-game separation

**English** · [中文](minimal-separation-check.zh.md) · [Back to the project README](../README.md)

The goal is to verify that a finite two-player, one-round nonlocal game exists,
with nonempty question and answer sets and a `0/1` winning predicate, such that
`omegaQcPOVM = 1` and `omegaQPOVM < 1`. Here q allows arbitrary finite local
dimensions and general POVMs; qc allows commuting-operator strategies, including
infinite-dimensional ones.

Manually inspect only the definitions and final statements below, and let Lean
check the construction and proof dependencies. This reduces the reading needed;
it does not remove the computational dependencies of the proof.

## Shortest verification path

Run these commands from the `formalization-clean` root:

```powershell
lake --fail-fast build ThomGame.Construction.NonlocalGameSeparation
lake env lean scripts/CheckSeparation.lean
```

For a new environment, first follow the [project README](../README.md) to install
the pinned Lean toolchain and obtain dependencies. `lake exe cache get` obtains
the mathlib cache. This target does not require building the project's additional
numerical corollaries.

The [check script](../scripts/CheckSeparation.lean) prints the core definitions
below and its two final statements, omitting proof terms, then recursively audits
their axiom dependencies. On success, the final message is:

```text
Separation check passed: explicit statements, nonempty binary game, and standard axioms only.
```

For an existing run, see the [binary-payoff theorem check log (2026-10-04)](binary-separation-check-20261004.log).

## Definitions to inspect manually

Read the named definitions; the later proofs in these files can be skipped.

| Object | Source | Mathematical meaning |
| --- | --- | --- |
| Game and expected score | [FiniteGame.lean](../ThomGame/Quantum/FiniteGame.lean): `FiniteGame`, `answerScore`, `success` | Four finite sets; a nonnegative joint question distribution of total mass 1; payoff in `[0,1]`; `success` sums the product of question probability, payoff, and answer probability |
| Correlation array | [Correlation.lean](../ThomGame/Quantum/Correlation.lean): `CorrelationTable` | `X → Y → A → B → ℝ`, representing the probability of answers `a,b` given questions `x,y` |
| POVM | [POVM.lean](../ThomGame/Quantum/POVM.lean): `POVM` | Bounded positive operators whose sum is the identity |
| Finite-dimensional spaces | [FiniteStrategy.lean](../ThomGame/Quantum/FiniteStrategy.lean): `LocalSpace`, `BipartiteSpace` | `LocalSpace d = ℂ^d`, `BipartiteSpace d e = ℂ^d ⊗ ℂ^e` |
| Finite-dimensional quantum strategy and Born rule | [FinitePOVMStrategy.lean](../ThomGame/Quantum/FinitePOVMStrategy.lean): `FinitePOVMStrategy`, `correlation` | Arbitrary positive finite local dimensions; a unit vector; a POVM for each local question; `Re ⟨ψ, (E ⊗ F) ψ⟩` |
| Commuting strategy and Born rule | [CommutingPOVMStrategy.lean](../ThomGame/Quantum/CommutingPOVMStrategy.lean): `CommutingPOVMStrategy`, `correlation` | A complete complex Hilbert space; a unit vector; POVMs; commutation of all effects across players; `Re ⟨ψ, E F ψ⟩` |
| All allowed correlations | [POVMGameValue.lean](../ThomGame/Quantum/POVMGameValue.lean): `povmQuantumCorrelations`, `povmCommutingCorrelations` | q is the range of all finite-dimensional strategies; qc existentially quantifies over Hilbert spaces and all commuting strategies on them |
| Values | [GameValue.lean](../ThomGame/Quantum/GameValue.lean): `value`; [POVMGameValue.lean](../ThomGame/Quantum/POVMGameValue.lean): `omegaQPOVM`, `omegaQcPOVM` | `value K = sSup (success '' K)`; q and qc use the respective correlation sets above |

Unfolding these definitions gives

$$
\operatorname{score}_G(p)=\sum_{x,y,a,b}\pi(x,y)V(x,y,a,b)p(a,b\mid x,y),
\qquad
\omega_t(G)=\sup_{p\in C_t}\operatorname{score}_G(p).
$$

The q correlations satisfy
$p(a,b\mid x,y)=\operatorname{Re}\langle\psi,(E_a^x\otimes F_b^y)\psi\rangle$,
and the qc correlations satisfy
$p(a,b\mid x,y)=\operatorname{Re}\langle\psi,E_a^xF_b^y\psi\rangle$.
`alice` depends only on `x`, `bob` only on `y`, and the shared state is independent
of the questions. The qc model neither requires measurements for different
questions of the same player to commute nor imposes finite dimensionality.

For an external comparison with the pure-state, POVM convention, see
[Karamlou, MFCS 2025, Sections 2.2–2.3](https://drops.dagstuhl.de/storage/00lipics/lipics-vol345-mfcs2025/html/LIPIcs.MFCS.2025.61/LIPIcs.MFCS.2025.61.html).
That paper additionally assumes full support of the question distribution in its
discussion of perfect strategies; this project allows arbitrary joint
distributions, including question pairs of zero weight.

## Correspondence with common conventions

- **Positivity:** `0 ≤ effect a` uses mathlib's usual positive-operator order on
  bounded operators. `POVM.isPositive`, `POVM.selfAdjoint`, and
  `POVM.quadratic_nonneg` expose self-adjointness and nonnegative quadratic forms.
  For further detail, see `ContinuousLinearMap.IsPositive` in mathlib's
  `Analysis/InnerProductSpace/Positive.lean`.
- **Arbitrary finite-dimensional spaces:** Each strategy carries its own local
  dimensions; there is no uniform bound.
  [`FinitePOVMStrategy.exists_coordinates`](../ThomGame/Quantum/FinitePOVMCoordinates.lean)
  proves that POVM/unit-vector strategies on arbitrary finite-dimensional complex
  local Hilbert spaces have coordinate-model representatives with the same Born
  probabilities. The script also audits this theorem; its proof need not be read.
- **Pure-state convention:** States are unit vectors. If starting from density
  matrices, the usual purification argument explains the correspondence with
  finite-dimensional strategies. This minimal path does not separately formalize
  or verify a mixed-state purification theorem.
- **Hilbert-space universe:** The qc definition quantifies over `H : Type`,
  without a finite-dimensionality restriction. This is not a claim that transport
  across every Lean universe has been formally proved.
- **Nonempty sets and binary winning predicates:** `FiniteGame` allows `[0,1]`
  payoffs. Both public existence theorems in
  [NonlocalGameSeparation.lean](../ThomGame/Construction/NonlocalGameSeparation.lean)
  explicitly conclude
  `∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1`.
  The script's `SeparationCheck.binary_separation` additionally makes nonemptiness
  of all four sets explicit. The public theorems themselves therefore cover the
  usual Boolean winning-predicate convention.

## Final statement and proof verification

In the `ThomGame.Quantum` namespace, the public POVM theorem states:

```lean
theorem exists_finiteGame_povm_quantum_commuting_separation :
    ∃ (X Y A B : Type) (_ : Fintype X) (_ : Fintype Y)
      (_ : Fintype A) (_ : Fintype B) (G : FiniteGame X Y A B),
      (∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1) ∧
      G.omegaQcPOVM = 1 ∧ G.omegaQPOVM < 1
```

The same file's `exists_finiteGame_quantum_commuting_separation` includes the same
binary-payoff condition and uses the projective-measurement values `omegaQc` and
`omegaQ`. Neither public theorem has additional assumptions. Nonemptiness of the
four sets is explicitly added and proved in the strengthened script statement
below.

`SeparationCheck.separation` explicitly restates the existence claim, including
the binary-payoff condition, and uses the project's proved
`ThomGame.Quantum.exists_finiteGame_povm_quantum_commuting_separation` as its proof.
This checks the expected type rather than only looking up a name.

`SeparationCheck.binary_separation` uses the same concrete witness to add
nonemptiness of all four sets. It still has no additional assumptions. Read its
statement; the proof can be skipped.

The recursive axiom audit allows only `propext`, `Classical.choice`, and
`Quot.sound`. Any other axiom dependency, including `sorryAx`, makes the script
fail. This checks the final statements and their actual proof dependencies;
unrelated theorems need not be audited for this single goal.

The reader confirms that the definitions express the intended mathematics; Lean
checks that the stated type has a valid proof. An axiom audit does not decide the
mathematical meaning of the definitions. This distinction is explained in the
[official Lean documentation on proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

The two commands normally rely on the pinned Lean/mathlib versions and their
build artifacts. The build command can reuse existing compiled artifacts; when
running the script, Lean loads existing `.olean` files rather than rechecking all
imported dependencies from source on every import. To rebuild the project proof
dependencies of this conclusion from source, run the same commands in a fresh source copy without the
project's `.lake/build`. For independent kernel checking of dependency caches as
well, the official documentation describes stronger routes such as
`lean4checker`; these are outside the minimal path above.

The original `omegaQ`/`omegaQc` values use projective measurements and remain
available in the public existence theorem. This path directly inspects the
general POVM definitions and conclusion, so measurement-dilation proofs need not
be read first.
