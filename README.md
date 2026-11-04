# A symmetric counterexample to the two-bent decomposition conjecture

[![Lean](https://github.com/s1lverfish/2-bent-decomposition-counterexample-formalization/actions/workflows/lean.yml/badge.svg)](https://github.com/s1lverfish/2-bent-decomposition-counterexample-formalization/actions/workflows/lean.yml)

Lean formalization accompanying the mathematical work *An infinite family of counterexamples to the bent sum decomposition conjecture*, by András Viczián, Máté Kepes and Anita Kercsó-Molnár.

For every natural $k\ge3$, put $n=2^k$. The symmetric Boolean function

$$F_n=1+\sigma_2+\sigma_4+\cdots+\sigma_{n/2}$$

has **exact algebraic degree $n/2$** and cannot be an XOR of **at most two arbitrary bent Boolean functions on the same $n$ variables**. Here $\sigma_j$ denotes the elementary symmetric squarefree polynomial of degree $j$ over $\mathbb F_2$.

The proof covers every $k\ge3$, with no finite cutoff or restriction on the possible bent summands.

## Main theorem

See [`full_infinite_family`](BentDecomposition/Main.lean) in namespace `BentDecompositions.Family`:

```lean
theorem full_infinite_family (k : ℕ) (hk : 3 ≤ k) :
    DegreeLE (Fn (2^k)) (2^k/2) ∧
    ¬ DegreeLE (Fn (2^k)) (2^k/2-1) ∧
    ¬ SumAtMostTwo (Fn (2^k))
```

The first two clauses express exact degree: a representation of degree at most $n/2$ exists, and none of degree at most $n/2-1$ exists. `SumAtMostTwo` explicitly includes zero, one and two summands. Nonzero and nonbentness are proved separately.

## Build

Install [Lean via Elan](https://lean-lang.org/install/). The repository selects its own toolchain; do not change the pins to match a globally installed version.

```sh
git clone https://github.com/s1lverfish/2-bent-decomposition-counterexample-formalization.git
cd 2-bent-decomposition-counterexample-formalization
lake exe cache get
lake build
python3 scripts/check_axioms.py
```

`lake exe cache get` fetches the pinned mathlib dependencies and their compiled cache. The theorem is checked by `lake build`; downloading cache files is not itself a proof check. The project uses **Lean 4.35.0** and **mathlib v4.35.0** (exact Git revisions, including transitive dependencies, are recorded in `lake-manifest.json`). Dependencies and generated build artifacts are not committed.

## VS Code

Open the **repository root folder** in VS Code and enable the recommended **Lean 4** extension (`leanprover.lean4`). Open `BentDecomposition/Main.lean`. Lean checks the file automatically; the Infoview displays goals at the cursor. On macOS, use **Cmd+Shift+Enter** to toggle Infoview. If imported objects are missing, run `lake build` once in the integrated terminal.

For individual source checking:

```sh
lake env lean BentDecomposition/Main.lean
```

## Organization

- [`BentDecomposition/`](BentDecomposition/): the complete general-dimensional proof.
- [`BentDecomposition.lean`](BentDecomposition.lean): root import for the full development.
- [`docs/PAPER_MAP.md`](docs/PAPER_MAP.md): mathematical definitions and correspondence with the paper.
- [`Audit.lean`](Audit.lean) and [`scripts/check_axioms.py`](scripts/check_axioms.py): axiom reports and admission checks.
- [`.github/workflows/lean.yml`](.github/workflows/lean.yml): reproducible build and audit on pushes and pull requests.
- [`PROVENANCE.json`](PROVENANCE.json): source migration from the original research development.

The final theorems use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. No `sorry`, additional mathematical axioms, `native_decide`, or external solver oracle is used. The audit checks these conditions in addition to the actual build. Verification trusts Lean's kernel and the pinned Lean/mathlib distribution.

The formalization was developed with AI assistance and separately reviewed against the mathematical statement in the original research workspace. This repository is a standalone extraction: module paths and visibility were modernized, while the mathematical statements and proof arguments were retained (with minor linter cleanups). The ordinary Lean build, rather than a claim about the development process, supplies reproducible verification.

## Explicit three-bent decomposition of F₈

[`BentDecomposition/ThreeSummands.lean`](BentDecomposition/ThreeSummands.lean)
formalizes the manuscript's explicit permutations P,Q, the Boolean offset r,
and the three summands b₀,b₁,b₂. The internal four-coordinate encoding is
x₁+2x₂+4x₃+8x₄, agreeing with the coordinate-vector table. Both permutations
are proved bijective; all three summands are proved bent and their XOR is F₈.
Together with the existing lower bound, `F8_exactly_three` establishes the
minimum number of bent summands is exactly three.

```sh
lake build BentDecomposition.ThreeSummands
lake build
python3 scripts/check_axioms.py
```

The namespace is `BentDecompositions.Family.ThreeSummands`. Finite checks use
ordinary `decide` and are checked by Lean's kernel. No admissions, extra
mathematical axioms, `native_decide` or external solver are used. Checking
this explicit witness can take longer than the symbolic family theorem.
