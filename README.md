# Erdős Problem #696

> **Normal orders of the chain functions $h(n)$ and $H(n)$**
>
> David Turturean, MIT — `davidct@mit.edu` — April 2026

A complete proof and Lean 4 formalization of [Erdős Problem #696](https://www.erdosproblems.com/696).

## Result

For every `ε > 0`, almost all `n` satisfy

$$h(n) = \left(\frac{1}{2} + o(1)\right) \log_* n$$

$$H(n) = (1 + o(1)) \log_* n$$

$$\frac{H(n)}{h(n)} \to 2$$

In particular, Erdős's conjectured `H(n)/h(n) → ∞` is **false** on a density-one set.

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

The formalization is `0 sorries` and depends on **3 classical analytic NT axioms** (Mathlib v4.28.0 gaps).  All three are standard textbook results admitted without proof here only because Mathlib does not yet package them.

### Axiom audit (verbatim against published references)

| Axiom | Paper § | Reference |
|---|---|---|
| `siegel_walfisz` | Lemma 2.1 | Davenport, *Multiplicative Number Theory*, GTM 74, 2nd ed. (rev. Montgomery, 1980; ISBN 978-1-4757-5927-3), **Ch. 22 eq. (4)** (verified directly) |
| `brun_titchmarsh` | Lemma 2.2 | Iwaniec-Kowalski, *Analytic Number Theory*, AMS Colloquium Publ. 53, **Theorem 6.6** |
| `mertens` | Lemma 2.3 | F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, **J. reine angew. Math. 78 (1874), 46–62** (verified directly against Göttingen GDZ PPN243919689_0078); also Hardy-Wright, *Introduction to the Theory of Numbers*, 6th ed., **Theorem 427** (weaker `o(1)` form) |

#### 1. `siegel_walfisz` — Davenport §22 eq. (4)

> *Let `N` be any positive constant.  Then there exists a positive number `C₃(N)`, depending only on `N`, such that if `q ≤ (log x)^N` then*
> $$\psi(x; q, a) \;=\; \frac{x}{\varphi(q)} \;+\; O\!\bigl\{x \exp\bigl[-C_3(N)(\log x)^{1/2}\bigr]\bigr\}$$
> *uniformly in `q`, for every `(a, q) = 1`.*

**Lean form** (π-version, by partial summation as in Davenport p.133):
```lean
∀ A > 0, ∃ c > 0, ∃ C > 0, ∀ t ≥ 2, ∀ q ≥ 1, q ≤ (log t)^A,
  ∀ a coprime to q,
    |π(t; q, a) - Li(t)/φ(q)| ≤ C · t · exp(-c · √(log t))
```

#### 2. `brun_titchmarsh` — Iwaniec-Kowalski Theorem 6.6

> *For `(a, q) = 1` and `1 ≤ q < y`,*
> $$\pi(x + y; q, a) - \pi(x; q, a) \;<\; \frac{2y}{\varphi(q) \log(y/q)} + O\!\Bigl(\frac{y}{q \log^2(y/q)}\Bigr)$$
> *where the implied constant is absolute.*

**Lean form** (specialization to `x = 0`, error absorbed into one constant):
```lean
∃ C_BT > 0, ∀ q ≥ 1, ∀ a coprime to q, ∀ t ≥ 2q,
  π(t; q, a) ≤ C_BT · t / (φ(q) · log(t/q))
```

#### 3. `mertens` — Mertens' second theorem (1874)

**Verified directly** against Mertens' 1874 paper (Göttingen GDZ digitized scan, PPN243919689_0078, pp. 46–62):

- p. 54 eq. (17): Mertens computes the constant `𝔆 − H = lim_{G→∞} {∑_{q=2}^{G} 1/q − log log G} = 0.2614972128` (matches modern Meissel–Mertens constant `M ≈ 0.2614972128…`).
- p. 56: Mertens proves the explicit bound `|ε|, |ε'| ≤ (2+C)/log(G+1) + 1/(G·log G)`, asymptotically `O(1/log G)`.

> *There is an absolute constant `M ∈ ℝ` (the Meissel–Mertens constant, `M ≈ 0.2614972128…`) such that, for all `t ≥ 2`,*
> $$\sum_{p \le t,\, p\text{ prime}} \frac{1}{p} \;=\; \log\log t + M + O\!\bigl(1/\log t\bigr).$$

**Note on Hardy-Wright:** Hardy-Wright Theorem 427 (verified directly here against the 2008 OUP edition) states only the weaker `o(1)` form. The explicit `O(1/log t)` rate is from Mertens' original 1874 paper, not from HW Thm 427.

**Lean form**:
```lean
∃ M : ℝ, ∃ C > 0, ∀ t ≥ 2,
  |∑_{p ≤ ⌊t⌋, p prime} 1/p - log log t - M| ≤ C / log t
```

### Two additional cited inputs are *formally proved* here (not axioms)

- **`chebyshev_theta`** (Lemma 2.4) — derived from `Mathlib.NumberTheory.Chebyshev.theta_le_log4_mul_x` (`Cθ := log 4`).
- **`crt_transfer`** (Lemma 2.7) — proved by elementary CRT counting (~150 LOC).

### Verifying the dependency chain

```bash
lean --print-axioms Erdos696.Main.erdos_696
```
should report exactly the three axioms above (plus Lean's built-in `Classical.choice`, `propext`, `Quot.sound`).

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
