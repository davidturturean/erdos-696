# Erdős Problem #696

> **Normal orders of the chain functions $h(n)$ and $H(n)$**
>
> David Turturean, MIT — `davidct@mit.edu` — April 2026

A complete proof and Lean 4 formalization of [Erdős Problem #696](https://www.erdosproblems.com/696).

## Result

For every $\varepsilon > 0$, almost all $n$ satisfy
$$
h(n) = \left(\tfrac{1}{2} + o(1)\right) \log_* n,\qquad
H(n) = \left(1 + o(1)\right) \log_* n,\qquad
\frac{H(n)}{h(n)} \longrightarrow 2.
$$
In particular, Erdős's conjectured $H(n)/h(n) \to \infty$ is **false** on a density-one set.

Here:
- $h(n)$ = largest $\ell$ such that primes $p_1 < \cdots < p_\ell$ all divide $n$ with $p_{i+1} \equiv 1 \pmod{p_i}$.
- $H(n)$ = largest $u$ such that integers $d_1 < \cdots < d_u$ all divide $n$ with $d_{i+1} \equiv 1 \pmod{d_i}$.
- $\log_* n$ = iterated logarithm.

## Repository contents

```
.
├── Erdos696.lean              # Lean root (imports the whole library)
├── Erdos696/                  # Lean 4 formalization (~19,200 LOC, 0 sorries)
│   ├── Main.lean              # Main theorem `erdos_696`
│   ├── AnalyticInputs.lean    # Cited NT axioms (Siegel-Walfisz, Brun-Titchmarsh, Mertens)
│   ├── Defs.lean              # Definitions of h, H, logStar, almostAll
│   ├── CompositeSuccessor.lean    # Paper §6.2 Lemma 6.2 (Composite Successor)
│   ├── SubsetProduct.lean         # Paper §5 Lemma 6.1 (Subset Product Successor)
│   ├── Tower.lean                 # Paper §1.2 — exponential tower function
│   ├── UpperBoundH.lean           # Paper §3 — upper bound for H(n)
│   ├── UpperBoundLittleH.lean     # Paper §4 — upper bound for h(n)
│   ├── LowerBoundH.lean           # Paper §7 — lower bound for H(n) (largest file)
│   ├── LowerBoundLittleH.lean     # Paper §5 — lower bound for h(n)
│   └── PmodelManualHelpers.lean   # Independent prime-divisibility model bridges
├── paper/
│   ├── erdos_696_paper.tex    # LaTeX manuscript
│   └── erdos_696_paper.pdf    # Compiled PDF
├── problem_statement.md       # Verbatim problem from erdosproblems.com
├── lakefile.toml              # Lean build config
├── lake-manifest.json
├── lean-toolchain             # Pinned to leanprover/lean4:v4.28.0
└── LICENSE                    # Apache-2.0
```

## Building the Lean formalization

Requires [`elan`](https://github.com/leanprover/elan) (Lean version manager). Lean toolchain is auto-fetched from `lean-toolchain`.

```bash
# Fetch Mathlib's pre-built oleans (saves ~30 min)
lake exe cache get

# Compile the project (~10 min after cache)
lake build
```

## Building the paper

```bash
cd paper
latexmk -pdf erdos_696_paper.tex
```

A pre-built PDF is committed at `paper/erdos_696_paper.pdf`.

## Axioms used

The formalization is `0 sorries` and depends on **3 classical analytic NT axioms** (Mathlib v4.28.0 gaps), all standard textbook results:

| Axiom | Paper Lemma | Reference |
|---|---|---|
| `siegel_walfisz` | Lemma 2.1 | Davenport, *Multiplicative Number Theory*, Ch. 22 |
| `brun_titchmarsh` | Lemma 2.2 | Iwaniec-Kowalski, *Analytic Number Theory*, Thm. 6.6 |
| `mertens` | Lemma 2.3 | Hardy-Wright, *Introduction to the Theory of Numbers*, Thm. 427 |

Two additional cited inputs are formally proved here:
- `chebyshev_theta` (Lemma 2.4) — derived from `Mathlib.NumberTheory.Chebyshev`.
- `crt_transfer` (Lemma 2.7) — proved by elementary CRT counting.

Verify the dependency chain:
```bash
lean --print-axioms Erdos696.Main.erdos_696
```

## How it was made

This work was assembled with substantial AI assistance. See the *Acknowledgement of AI assistance* section in [`paper/erdos_696_paper.tex`](paper/erdos_696_paper.tex) for full disclosure.

## Citation

```bibtex
@misc{turturean2026erdos696,
  author = {David Turturean},
  title = {Normal orders of the Erd\H{o}s chain functions $h(n)$ and $H(n)$},
  year = {2026},
  howpublished = {GitHub: \url{https://github.com/davidturturean/erdos-696}},
}
```

See also [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0. See [`LICENSE`](LICENSE).
