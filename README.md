# Finite nonlocal-game separation in Lean

**English** | [简体中文](README.zh.md)

This Lean 4 / mathlib project proves that there exists a finite two-player nonlocal game with a **binary winning predicate** and

$$
\omega_q(G)<1=\omega_{qc}(G).
$$

The quantum value allows arbitrary finite local dimensions; the commuting value allows infinite-dimensional Hilbert spaces. The public existence theorems include the binary-payoff condition and have no additional hypotheses.

The existence proof is by **explicit construction**: both theorems use the explicitly defined `ThomGame.Construction.paperGame` as their witness. To inspect that game, follow the [construction roadmap](#where-to-find-the-explicit-game-construction) below.

> [!IMPORTANT]
> **To verify only this conclusion, start with the minimal chain below.**
> Read the game, measurement, strategy, and value definitions; inspect the existential statement; then run the two verification commands. The construction and intermediate proofs do not need to be read manually.

## Start here: the minimal verification chain

**Game → POVMs → strategies and Born probabilities → correlation sets → values → existence theorem → Lean check.**

From the repository root, with the pinned toolchain and dependencies available:

```sh
lake --fail-fast build ThomGame.Construction.NonlocalGameSeparation
lake env lean scripts/CheckSeparation.lean
```

For a new checkout, see [setup](#setup-and-full-project-checks). The [detailed English guide](validation/minimal-separation-check.md) and [中文指南](validation/minimal-separation-check.zh.md) explain the same minimal route.

### 1. Inspect the definitions

Use the general POVM version for this route. Its definitions directly state the measurement model and Born rule.

| Step | Read | What to confirm |
| --- | --- | --- |
| Game and score | [FiniteGame](ThomGame/Quantum/FiniteGame.lean#L13), lines 13–31 | Four finite alphabets; a nonnegative question distribution of total mass one; payoff in `[0,1]`; expected score is the weighted sum over questions and answers. |
| Correlation table | [CorrelationTable](ThomGame/Quantum/Correlation.lean#L15) | A real array indexed by both questions and both answers. |
| Measurement | [POVM](ThomGame/Quantum/POVM.lean#L19), lines 19–26 | Bounded positive operators whose sum is the identity. |
| Finite-dimensional strategy | [Local spaces](ThomGame/Quantum/FiniteStrategy.lean#L13), lines 13–14; [FinitePOVMStrategy](ThomGame/Quantum/FinitePOVMStrategy.lean#L17), lines 17–39 | Arbitrary positive local dimensions, a unit vector in their tensor product, local POVMs, and the tensor-product Born rule. |
| Commuting strategy | [CommutingPOVMStrategy](ThomGame/Quantum/CommutingPOVMStrategy.lean#L18), lines 18–35 | A complete complex Hilbert space, a unit vector, POVMs, cross-player commutation, and the corresponding Born rule. |
| Allowed correlations | [POVM correlation sets](ThomGame/Quantum/POVMGameValue.lean#L17), lines 17–28 | All correlations arising from the respective strategy classes. |
| Values | [value](ThomGame/Quantum/GameValue.lean#L15); [omegaQPOVM and omegaQcPOVM](ThomGame/Quantum/POVMGameValue.lean#L75), lines 75–79 | The supremum of expected scores over each allowed correlation set. |

The score and values are

$$
\operatorname{score}_G(p)=\sum_{x,y,a,b}\pi(x,y)V(x,y,a,b)p(a,b\mid x,y),
\qquad \omega_t(G)=\sup_{p\in C_t}\operatorname{score}_G(p).
$$

The state is independent of the questions; each player's measurement depends only on that player's question. Local dimensions have no fixed upper bound. The commuting model imposes no finite-dimensionality requirement and requires only cross-player commutation. The guide explains the pure-state convention and the verified passage from arbitrary finite-dimensional Hilbert spaces to coordinates.

### 2. Inspect the final statement

The public theorem in the `ThomGame.Quantum` namespace is [exists_finiteGame_povm_quantum_commuting_separation](ThomGame/Construction/NonlocalGameSeparation.lean#L28):

```lean
∃ (X Y A B : Type) (_ : Fintype X) (_ : Fintype Y)
  (_ : Fintype A) (_ : Fintype B) (G : FiniteGame X Y A B),
  (∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1) ∧
  G.omegaQcPOVM = 1 ∧ G.omegaQPOVM < 1
```

The binary condition is part of the **proved conclusion**. The same file contains [exists_finiteGame_quantum_commuting_separation](ThomGame/Construction/NonlocalGameSeparation.lean#L13), using the projective-measurement values `omegaQ` and `omegaQc`.

[CheckSeparation.lean](scripts/CheckSeparation.lean) explicitly checks the public POVM statement. Its `SeparationCheck.binary_separation` also proves that all four alphabets can be nonempty.

### 3. Check the result

The script prints the actual core definitions and final statements, suppresses expanded proof terms, and recursively checks their axiom dependencies. It also checks the finite-dimensional coordinate-coverage theorem. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; any other axiom, including `sorryAx`, causes failure.

The expected final message is:

```text
Separation check passed: explicit statements, nonempty binary game, and standard axioms only.
```

**Recorded result: passed on 2026-10-04, after adding binary payoff to both public theorems.** See the [focused check](validation/binary-separation-check-20261004.log), [theorem-module build](validation/binary-separation-target-build-20261004.log), and [main-theorem check](validation/binary-separation-main-check-20261004.log).

Human review establishes that the definitions express the intended mathematics; Lean checks the formal claims. The commands reuse existing `.olean` files. To rebuild this conclusion's project proof dependencies from source, use a fresh source copy without the project's `.lake/build` and run the same commands. The [guide](validation/minimal-separation-check.md) states the precise verification scope.

## Where to find the explicit game construction

The witness is a linear-system game: Alice receives a row and returns three bits; Bob receives a column occurring in that row and returns one bit. They win when Alice's bits satisfy the row equation and her bit for Bob's column agrees with his answer.

1. [PaperGame.lean: `paperGame`](ThomGame/Construction/PaperGame.lean#L15) defines the actual game as `paperSystem.incidenceGame`, with its concrete question and answer types. The same file's `paperGame_weight` and `paperGame_payoff` state its question distribution and winning condition.
2. [IncidenceGame.lean](ThomGame/Quantum/IncidenceGame.lean#L29) defines `incidenceWeight`, `incidencePayoff`, and `incidenceGame`: uniform sampling of row–column incidences, the binary winning predicate, and their assembly into a `FiniteGame`.
3. [PaperOrderedSystem.lean: `paperSystem`](ThomGame/Construction/PaperOrderedSystem.lean#L12) gives the concrete sparse system with each row's columns in increasing order, and identifies its matrix and right-hand side with `A` and `b`.
4. [MatrixData.lean](ThomGame/Construction/MatrixData.lean#L18) defines `A` and `b`; `sourceTriples` and `A_eq_one_iff` specify the matrix entries, while `b_formula` specifies the right-hand side. For the underlying construction, continue to [Numbering.lean: `numberedSystem`](ThomGame/Construction/Numbering.lean#L108) and [Wheel.lean: `wheelFamily` and `system`](ThomGame/Construction/Wheel.lean#L70).

## Setup and full-project checks

Install elan and Git, then run from the repository root:

```sh
lake exe cache get
```

The project pins Lean to `v4.35.0-rc3` and mathlib to commit `16efc2c756299924184fe015f6384ad6538d42c7`. See [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and [lake-manifest.json](lake-manifest.json). Mathlib is the only direct Lean package dependency. Certificates are embedded in the Lean sources; building does not require the manuscript PDFs, external data generators, or Python.

For checks beyond the minimal separation route:

```sh
lake --fail-fast build
lake env lean scripts/CheckSeparation.lean
lake env lean scripts/CheckMain.lean
lake env lean scripts/CheckPOVM.lean
lake env lean scripts/CheckCorollaries.lean
lake env lean scripts/AuditAxioms.lean
```

The [validation index (Chinese)](validation/README.md) distinguishes the latest binary-separation checks from earlier full-project audits and source-hash snapshots.

## Further results

- [PaperPOVMGap.lean](ThomGame/Construction/PaperPOVMGap.lean): `ThomGame.Construction.paper_main_results_povm` combines the concrete construction's central-element results with `ωq = ωqa < 1 = ωqc` under general POVMs.
- [PaperValueCorollaries.lean](ThomGame/Construction/PaperValueCorollaries.lean): `paper_classical_value_corollary` gives the exact classical value, allowing shared randomness; `paper_quantum_gap_corollary` gives explicit bounds for the POVM quantum gap:

$$
\omega_c=1-\frac{1}{4251456},\qquad
0<2^{-2^{50003}}\le 1-\omega_q=\omega_{qc}-\omega_q\le\frac{1}{4251456}.
$$

The [proof-source notes (Chinese)](validation/corollaries-proof-sources.md) document the numerical corollaries. These additional results are separate from the minimal reading and verification route above.

## Repository map

| Location | Purpose |
| --- | --- |
| [ThomGame/Quantum](ThomGame/Quantum) | Game, measurement, strategy, correlation, and value definitions. |
| [NonlocalGameSeparation.lean](ThomGame/Construction/NonlocalGameSeparation.lean) | The two public existence theorems with binary payoff. |
| [ThomGame.lean](ThomGame.lean) | Full-project import entry. |
| [scripts](scripts) | Focused checks and the full-project axiom audit. |
| [validation](validation) | Detailed verification guides, logs, and dated historical records. |
