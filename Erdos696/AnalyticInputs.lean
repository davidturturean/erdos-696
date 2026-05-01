/-
# Analytic-number-theory inputs

This file collects the classical analytic NT statements used unconditionally
throughout the paper.  They correspond to Lemmas 2.1–2.4 + 2.7 in
`erdos_696_paper.tex`.

**Axioms (3 — Mathlib v4.28.0 gaps, all classical NT textbook results):**
* `siegel_walfisz` (Lemma 2.1) — Davenport, *Multiplicative Number Theory*, Ch. 22.
* `brun_titchmarsh` (Lemma 2.2) — Iwaniec–Kowalski, *Analytic Number Theory*, Thm. 6.6.
* `mertens` (Lemma 2.3) — Hardy–Wright, Thm. 427.

**Theorems (2 — proved here from Mathlib):**
* `chebyshev_theta` (Lemma 2.4) — proved from `Chebyshev.theta_le_log4_mul_x`.
* `crt_transfer` (Lemma 2.7) — proved by elementary CRT counting.

The `_count` variants (e.g. `siegelWalfisz_count`) state the prime-counting
form; logarithmic-density forms used in the paper proofs are derived in
their respective sections.
-/

import Erdos696.Defs
import Mathlib.NumberTheory.Chebyshev

namespace Erdos696

open scoped BigOperators
open Real
open MeasureTheory

/-- The prime-counting function in arithmetic progressions:
`piMod t q a = #{p ≤ t : p prime, p ≡ a (mod q)}`. -/
noncomputable def piMod (t : ℝ) (q a : ℕ) : ℕ :=
  Nat.card {p : ℕ | p ≤ ⌊t⌋₊ ∧ p.Prime ∧ p % q = a % q}

/-- The logarithmic integral `Li(t) = ∫₂^t dt / log t`.  We adopt the
standard convention `Li(t) := ∫_{2}^{t} 1 / log u du`. -/
noncomputable def li (t : ℝ) : ℝ :=
  ∫ u in (2 : ℝ)..t, 1 / Real.log u

/--
**Siegel–Walfisz theorem** (Lemma 2.1 in the paper, classical reference
Davenport, *Multiplicative Number Theory*, 2nd ed., GTM 74, §22).

**Textbook statement (Davenport §22, eq. (4) — ψ form):**
> Let `N` be any positive constant.  Then there exists a positive number
> `C₃(N)`, depending only on `N`, such that if `q ≤ (log x)^N` then
>     ψ(x; q, a) = x/φ(q) + O{x exp[−C₃(N)(log x)^{1/2}]}
> uniformly in `q`, for every `(a, q) = 1`.

The π-form (this axiom) follows by partial summation (Davenport p.133):
the main term `x/φ(q)` becomes `Li(x)/φ(q)` and the error term keeps the
same exp(−c √log) shape.  The exp(−c √log x) bound is the strongest
unconditional rate currently known, due to a Siegel-type analysis of
exceptional zeros of Dirichlet `L`-functions.

This is unconditional (does not assume GRH). -/
axiom siegel_walfisz :
    ∀ A : ℝ, 0 < A →
    ∃ c : ℝ, 0 < c ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ, 2 ≤ t →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log t) ^ A →
            ∀ a : ℕ, Nat.Coprime a q →
              |((piMod t q a : ℝ)) - li t / (q.totient : ℝ)| ≤
                C * t * Real.exp (-c * Real.sqrt (Real.log t))

/--
**Brun–Titchmarsh inequality** (Lemma 2.2 in the paper, classical
reference Iwaniec–Kowalski, *Analytic Number Theory*, AMS Colloquium
Publications Vol. 53, 2004, Theorem 6.6).

**Textbook statement (Iwaniec–Kowalski Thm. 6.6 — interval form):**
> For `(a, q) = 1` and `1 ≤ q < y`,
>     π(x + y; q, a) − π(x; q, a) < (2y) / (φ(q) log(y/q)) + O(y / (q log²(y/q)))
> where the implied constant is absolute.

This axiom records the consequence with `x = 0` and `y = t`:
`π(t; q, a) ≤ C_BT · t / (φ(q) log(t/q))` (the additive `O(...)` term
is absorbed into the constant `C_BT` for `t ≥ 2q`, where `log(t/q) ≥ log 2`).

Proved unconditionally via Selberg's `Λ²`-sieve (IK §6.5–6.8). -/
axiom brun_titchmarsh :
    ∃ CBT : ℝ, 0 < CBT ∧
      ∀ q : ℕ, 1 ≤ q →
        ∀ a : ℕ, Nat.Coprime a q →
          ∀ t : ℝ, (2 * q : ℝ) ≤ t →
            ((piMod t q a : ℝ)) ≤
              CBT * t / ((q.totient : ℝ) * Real.log (t / q))

/--
**Mertens' theorem with explicit error** (Lemma 2.3 in the paper,
classical reference Hardy–Wright, *An Introduction to the Theory of
Numbers*, 6th ed. (revised by Heath-Brown and Silverman), OUP 2008,
Theorem 427; also Tenenbaum, *Introduction to Analytic and Probabilistic
Number Theory*, 3rd ed., Ch. I.1, Theorem 11).

**Textbook statement:**
> There is an absolute constant `M ∈ ℝ` (Mertens' constant,
> `M ≈ 0.2614972…`) such that, for all `t ≥ 2`,
>     ∑_{p ≤ t, p prime} 1/p = log log t + M + O(1/log t).

The leading term `log log t` matches the heuristic 1/p prime density and
the explicit `O(1/log t)` error rate is a consequence of Mertens' first
theorem `∑_{p ≤ t} (log p)/p = log t + O(1)` plus Abel partial summation.
Proof outline: combine `chebyshev_theta` (Lemma 2.4, formally proved
below) with partial summation; the residual constant `M` is computable
to arbitrary precision.

Proven unconditionally; predates the Prime Number Theorem. -/
axiom mertens :
    ∃ M : ℝ, ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 2 ≤ t →
        |(∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊),
              (1 : ℝ) / (p : ℝ)) - Real.log (Real.log t) - M| ≤
          C / Real.log t

/--
**Chebyshev bound on `θ(x)`** (Lemma 2.4 in the paper; Hardy–Wright,
Thm. 414).

There is an absolute constant `C_θ > 0` such that, for all `t ≥ 2`,
`∑_{p ≤ t, p prime} log p ≤ C_θ · t`.

Proven from `Mathlib.NumberTheory.Chebyshev.theta_le_log4_mul_x`, which
provides `θ x ≤ log 4 · x` for all `x ≥ 0`.  We take `C_θ := log 4`. -/
theorem chebyshev_theta :
    ∃ Cθ : ℝ, 0 < Cθ ∧
      ∀ t : ℝ, 2 ≤ t →
        (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊),
            Real.log (p : ℝ)) ≤ Cθ * t := by
  refine ⟨Real.log 4, Real.log_pos (by norm_num), ?_⟩
  intro t ht
  have h := Chebyshev.theta_le_log4_mul_x (by linarith : (0:ℝ) ≤ t)
  have hbridge :
      (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), Real.log (p : ℝ)) =
      Chebyshev.theta t := by
    rw [Chebyshev.theta_eq_sum_Icc]
    congr 1
  rw [hbridge]
  exact h

/-! ### CRT transfer (Lemma 2.7) -/

/-- The product `M = ∏_{p ≤ P, p prime} p`, used in `crt_transfer`. -/
def primorial (P : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.Iic P)).prod (fun p => p)

/--
**CRT transfer principle** (Lemma 2.7 in the paper; elementary CRT density transfer).

If an event `E` depends only on the residue `n mod M` (where `M = primorial P`),
then the density of `n ≤ x` for which `E(n)` holds equals the periodic average
`A/M` (where `A = #{r ∈ [0, M) : E r}`) up to additive error `M/x`.

**Proof outline:**
- Set `M := primorial P ≥ 2`.
- Set `A := #{r ∈ [0, M) : E r}`, `p_prod := A/M ∈ [0, 1]`.
- For `x ≥ 1`, let `X := ⌊x⌋ ≥ 1`.  Decompose `X = qM + s` where `0 ≤ s < M`.
- By periodicity, `count(X) = q·A + count(s)` where `count(s) := #{n ∈ [0, s] : E n}`.
- `count(s) ≤ s + 1 ≤ M`.
- `count(X) - X·p_prod = count(s) - s·A/M ∈ [-(M-1), M]`.
- For `x ∈ [X, X+1)`: `count(X) - x·p_prod ∈ (-(M-1) - 1, M] = (-M, M]`.
- So `|count(X) - x·p_prod| ≤ M`, dividing by `x` gives the claim.
-/
theorem crt_transfer :
    ∀ (P : ℕ), 2 ≤ P →
    ∀ (E : ℕ → Prop) [DecidablePred E],
      (∀ n n' : ℕ, n % primorial P = n' % primorial P → (E n ↔ E n')) →
    ∃ p_prod : ℝ,
      ∀ x : ℝ, 1 ≤ x →
        |((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ E n} : ℝ)) / x - p_prod| ≤
          (primorial P : ℝ) / x := by
  intro P hP E _ hperiodic
  classical
  set M : ℕ := primorial P with hM_def
  have hM_pos : 0 < M := by
    rw [hM_def]
    apply Finset.prod_pos
    intro p hp
    rw [Finset.mem_filter] at hp
    exact hp.2.pos
  have hM_ge_1 : 1 ≤ M := hM_pos
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  -- A := count of E over [0, M) (the periodic average count).
  set A : ℕ := ((Finset.range M).filter E).card with hA_def
  have hA_le_M : A ≤ M := by
    rw [hA_def]
    exact (Finset.card_filter_le _ _).trans (by simp [Finset.card_range])
  have hA_real_le_M : (A : ℝ) ≤ (M : ℝ) := by exact_mod_cast hA_le_M
  have hA_real_nonneg : (0 : ℝ) ≤ (A : ℝ) := by exact_mod_cast Nat.zero_le _
  -- p_prod := A / M, the long-run density.
  refine ⟨(A : ℝ) / (M : ℝ), ?_⟩
  intro x hx
  set X : ℕ := ⌊x⌋₊ with hX_def
  have hX_real_le : (X : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hX_real_lt : x < (X : ℝ) + 1 := Nat.lt_floor_add_one x
  have hX_ge_1 : 1 ≤ X := by
    rw [hX_def]
    exact Nat.one_le_iff_ne_zero.mpr fun h => by
      have := Nat.lt_floor_add_one x
      simp [h] at this
      linarith
  have hX_real_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX_ge_1
  have hX_real_ge_1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX_ge_1
  have hx_pos : 0 < x := by linarith
  -- Convert Nat.card {n ≤ X ∧ E n} to a Finset count.
  have h_card_eq :
      (Nat.card {n : ℕ | n ≤ X ∧ E n} : ℝ) =
        (((Finset.Iic X).filter E).card : ℝ) := by
    have hset : {n : ℕ | n ≤ X ∧ E n} = ↑((Finset.Iic X).filter E) := by
      ext n
      simp [Finset.mem_Iic]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  set count_X : ℕ := ((Finset.Iic X).filter E).card with hcount_X_def
  rw [h_card_eq]
  show |(count_X : ℝ) / x - (A : ℝ) / (M : ℝ)| ≤ (M : ℝ) / x
  -- Divmod decomposition: X = qM + s.
  set q : ℕ := X / M with hq_def
  set s : ℕ := X % M with hs_def
  have hX_eq : X = q * M + s := by
    rw [hq_def, hs_def, Nat.mul_comm]; exact (Nat.div_add_mod X M).symm
  have hs_lt : s < M := Nat.mod_lt _ hM_pos
  have hs_le_M_minus_1 : s ≤ M - 1 := Nat.le_sub_one_of_lt hs_lt
  -- count_partial(s) := #{n ∈ [0, s] : E n}.
  set cs : ℕ := ((Finset.Iic s).filter E).card with hcs_def
  have hcs_le : cs ≤ s + 1 := by
    rw [hcs_def]
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Iic]
  have hcs_le_M : cs ≤ M := by linarith
  have hcs_real_nonneg : (0 : ℝ) ≤ (cs : ℝ) := by exact_mod_cast Nat.zero_le _
  have hcs_real_le_M : (cs : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcs_le_M
  -- Key periodicity claim: count_X = q·A + cs.
  have h_count_decomp : count_X = q * A + cs := by
    -- Partition Finset.Iic X into [0, M-1], [M, 2M-1], ..., [(q-1)M, qM-1], [qM, qM+s].
    -- Each [jM, (j+1)M-1] has E-count = A by periodicity.  Last has count cs.
    rw [hcount_X_def]
    -- Use Finset.Iic X = ⋃ (j ∈ range (q+1)), [jM, jM+s] ∩ Iic X.  Ugh, complicated.
    -- Cleaner: induction on q.  Or use Finset.range (X+1).
    -- Let's bijection: split [0, X] = [0, qM-1] ⊔ [qM, qM+s].
    -- |[0, qM-1] ∩ E| via periodicity = q · A.
    -- |[qM, qM+s] ∩ E| via shift by qM = |[0, s] ∩ E| = cs.
    -- Use Finset.disjoint_filter and Finset.card_union_eq.
    have h_split : ((Finset.Iic X).filter E) =
        ((Finset.Iio (q * M)).filter E) ∪ ((Finset.Icc (q * M) X).filter E) := by
      apply Finset.ext
      intro n
      simp [Finset.mem_filter, Finset.mem_union, Finset.mem_Iio, Finset.mem_Icc,
            Finset.mem_Iic]
      constructor
      · rintro ⟨hn_le_X, hEn⟩
        by_cases h : n < q * M
        · left; exact ⟨h, hEn⟩
        · right; exact ⟨⟨Nat.le_of_not_lt h, hn_le_X⟩, hEn⟩
      · rintro (⟨hn_lt, hEn⟩ | ⟨⟨_, hn_le_X⟩, hEn⟩)
        · refine ⟨?_, hEn⟩
          have : n < q * M + s := lt_of_lt_of_le hn_lt (Nat.le_add_right _ _)
          linarith [hX_eq]
        · exact ⟨hn_le_X, hEn⟩
    have h_disjoint : Disjoint ((Finset.Iio (q * M)).filter E)
        ((Finset.Icc (q * M) X).filter E) := by
      apply Finset.disjoint_left.mpr
      intro n hn1 hn2
      simp [Finset.mem_filter, Finset.mem_Iio] at hn1
      simp [Finset.mem_filter, Finset.mem_Icc] at hn2
      omega
    rw [h_split]
    rw [Finset.card_union_of_disjoint h_disjoint]
    -- Now count in [0, qM-1] = q · A and count in [qM, X] = cs.
    -- **h_lower (induction on q):** ((Finset.Iio (q*M)).filter E).card = q * A.
    have h_lower : ∀ q' : ℕ, ((Finset.Iio (q' * M)).filter E).card = q' * A := by
      intro q'
      induction q' with
      | zero =>
        simp
      | succ q'' ih =>
        have h_split2 : Finset.Iio ((q'' + 1) * M) =
            Finset.Iio (q'' * M) ∪ Finset.Ico (q'' * M) ((q'' + 1) * M) := by
          have h_succ : (q'' + 1) * M = q'' * M + M := by ring
          ext n
          simp [Finset.mem_Iio, Finset.mem_Ico, Finset.mem_union, h_succ]
          omega
        have h_disj2 : Disjoint ((Finset.Iio (q'' * M)).filter E)
            ((Finset.Ico (q'' * M) ((q'' + 1) * M)).filter E) := by
          apply Finset.disjoint_left.mpr
          intro n hn1 hn2
          simp [Finset.mem_filter, Finset.mem_Iio] at hn1
          simp [Finset.mem_filter, Finset.mem_Ico] at hn2
          omega
        rw [h_split2, Finset.filter_union, Finset.card_union_of_disjoint h_disj2, ih]
        -- Need: ((Finset.Ico (q''*M) ((q''+1)*M)).filter E).card = A.
        -- Bijection r ↦ q''*M + r maps [0, M) to [q''*M, (q''+1)*M).
        have h_chunk : ((Finset.Ico (q'' * M) ((q'' + 1) * M)).filter E).card = A := by
          have h_succ' : (q'' + 1) * M = q'' * M + M := by ring
          have h_image : Finset.Ico (q'' * M) ((q'' + 1) * M) =
              (Finset.range M).image (fun r => q'' * M + r) := by
            ext n
            simp [Finset.mem_Ico, Finset.mem_image, Finset.mem_range, h_succ']
            constructor
            · intro ⟨hge, hlt⟩
              refine ⟨n - q'' * M, ?_, ?_⟩ <;> omega
            · intro ⟨r, hr, hr_eq⟩
              omega
          rw [h_image, Finset.filter_image]
          rw [Finset.card_image_of_injOn (fun a _ b _ hab => by omega)]
          rw [hA_def]
          congr 1
          apply Finset.filter_congr
          intro n hn
          rw [Finset.mem_range] at hn
          exact hperiodic (q'' * M + n) n
            (by rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hn])
        rw [h_chunk]
        ring
    -- **h_upper (shift bijection):** ((Finset.Icc (q*M) X).filter E).card = cs.
    have h_upper : ((Finset.Icc (q * M) X).filter E).card = cs := by
      -- Icc (q*M) X has elements [q*M, q*M + s] (since X = q*M + s).
      -- Bijection r ↦ q*M + r maps [0, s] to [q*M, q*M+s].
      have h_image : Finset.Icc (q * M) X = (Finset.Iic s).image (fun r => q * M + r) := by
        ext n
        simp [Finset.mem_Icc, Finset.mem_image, Finset.mem_Iic]
        constructor
        · intro ⟨hge, hle⟩
          refine ⟨n - q * M, ?_, ?_⟩ <;>
          · have hX : X = q * M + s := hX_eq
            omega
        · intro ⟨r, hr, hr_eq⟩
          have hX : X = q * M + s := hX_eq
          omega
      rw [h_image, Finset.filter_image]
      rw [Finset.card_image_of_injOn (fun a _ b _ hab => by omega)]
      rw [hcs_def]
      congr 1
      apply Finset.filter_congr
      intro n hn
      rw [Finset.mem_Iic] at hn
      have hn_lt_M : n < M := lt_of_le_of_lt hn hs_lt
      exact hperiodic (q * M + n) n
        (by rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hn_lt_M])
    rw [h_lower q, h_upper]
  -- Now bound: |count_X - x·p_prod| ≤ M.
  have h_count_X_real : (count_X : ℝ) = (q : ℝ) * (A : ℝ) + (cs : ℝ) := by
    rw [h_count_decomp]; push_cast; ring
  have hX_eq_real : (X : ℝ) = (q : ℝ) * (M : ℝ) + (s : ℝ) := by
    exact_mod_cast hX_eq
  have hs_real_lt : (s : ℝ) < (M : ℝ) := by exact_mod_cast hs_lt
  have hs_real_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.zero_le _
  -- |count_X - X · p_prod| = |cs - s · A/M| ≤ M.
  have h_diff_X : (count_X : ℝ) - (X : ℝ) * ((A : ℝ) / (M : ℝ)) =
      (cs : ℝ) - (s : ℝ) * ((A : ℝ) / (M : ℝ)) := by
    rw [h_count_X_real, hX_eq_real]
    field_simp
    ring
  have h_bound_aX : |(cs : ℝ) - (s : ℝ) * ((A : ℝ) / (M : ℝ))| ≤ (M : ℝ) := by
    rw [abs_le]
    constructor
    · -- -M ≤ cs - s·A/M.  cs ≥ 0, s·A/M ≤ s ≤ M-1 < M, so cs - s·A/M ≥ -s·A/M ≥ -(M-1) ≥ -M.
      have h1 : (s : ℝ) * ((A : ℝ) / (M : ℝ)) ≤ (s : ℝ) :=
        mul_le_of_le_one_right hs_real_nonneg
          (div_le_one_of_le₀ hA_real_le_M hM_real_pos.le)
      linarith
    · -- cs - s·A/M ≤ cs ≤ M.
      have h1 : 0 ≤ (s : ℝ) * ((A : ℝ) / (M : ℝ)) :=
        mul_nonneg hs_real_nonneg (div_nonneg hA_real_nonneg hM_real_pos.le)
      linarith
  -- Now |count_X - x·p_prod| ≤ M + p_prod ≤ M + 1.  Need ≤ M.  Use refined bound.
  -- count_X - x·p_prod = (count_X - X·p_prod) - (x - X)·p_prod
  -- = a(X) - (x-X)·p_prod  where a(X) := count_X - X·p_prod ∈ [-(M-1), M].
  -- Worst: a(X) = M, (x-X) = 0 (x = X): bound M.
  -- Worst: a(X) = -(M-1), (x-X) = 1: bound M-1 + 1 = M.
  -- So |count_X - x·p_prod| ≤ M.
  have h_diff_x : (count_X : ℝ) - x * ((A : ℝ) / (M : ℝ)) =
      ((count_X : ℝ) - (X : ℝ) * ((A : ℝ) / (M : ℝ))) -
        (x - (X : ℝ)) * ((A : ℝ) / (M : ℝ)) := by ring
  -- Bound count_X - x·p_prod ∈ (-M, M].
  have h_p_prod_le_one : (A : ℝ) / (M : ℝ) ≤ 1 :=
    div_le_one_of_le₀ hA_real_le_M hM_real_pos.le
  have h_p_prod_nonneg : 0 ≤ (A : ℝ) / (M : ℝ) :=
    div_nonneg hA_real_nonneg hM_real_pos.le
  have h_xX_nonneg : 0 ≤ x - (X : ℝ) := by linarith
  have h_xX_lt_one : x - (X : ℝ) < 1 := by linarith
  -- Refined bound: |count_X - x·p_prod| ≤ M.
  -- a(X) - (x-X)·p_prod where a(X) ∈ [-(M-1), M] (strict on left), (x-X)·p_prod ∈ [0, 1).
  -- So count_X - x·p_prod ∈ (-(M-1) - 1, M] = (-M, M].
  have h_aX_lower : -(M : ℝ) + 1 ≤ (count_X : ℝ) - (X : ℝ) * ((A : ℝ) / (M : ℝ)) := by
    rw [h_diff_X]
    -- cs - s·A/M ≥ 0 - (M-1)·1 = -(M-1) = -M + 1.
    have h1 : (s : ℝ) * ((A : ℝ) / (M : ℝ)) ≤ (M : ℝ) - 1 := by
      have hs_le : (s : ℝ) ≤ (M : ℝ) - 1 := by exact_mod_cast hs_le_M_minus_1
      calc (s : ℝ) * ((A : ℝ) / (M : ℝ))
          ≤ (s : ℝ) * 1 := mul_le_mul_of_nonneg_left h_p_prod_le_one hs_real_nonneg
        _ = (s : ℝ) := mul_one _
        _ ≤ (M : ℝ) - 1 := hs_le
    linarith
  have h_aX_upper : (count_X : ℝ) - (X : ℝ) * ((A : ℝ) / (M : ℝ)) ≤ (M : ℝ) := by
    rw [h_diff_X]; exact (abs_le.mp h_bound_aX).2
  -- |count_X - x·p_prod| ≤ M:
  have h_diff_x_bound : |(count_X : ℝ) - x * ((A : ℝ) / (M : ℝ))| ≤ (M : ℝ) := by
    rw [h_diff_x, abs_le]
    refine ⟨?_, ?_⟩
    · -- count_X - x·p_prod = a(X) - (x-X)·p_prod ≥ (-M+1) - 1·1 = -M.
      have h_xXp_le : (x - (X : ℝ)) * ((A : ℝ) / (M : ℝ)) ≤ 1 := by
        calc (x - (X : ℝ)) * ((A : ℝ) / (M : ℝ))
            ≤ 1 * 1 := mul_le_mul (le_of_lt h_xX_lt_one) h_p_prod_le_one
              h_p_prod_nonneg (by norm_num)
          _ = 1 := mul_one _
      linarith
    · -- count_X - x·p_prod = a(X) - (x-X)·p_prod ≤ M - 0 = M.
      have h_xXp_nonneg : 0 ≤ (x - (X : ℝ)) * ((A : ℝ) / (M : ℝ)) :=
        mul_nonneg h_xX_nonneg h_p_prod_nonneg
      linarith
  -- Divide by x: |count_X/x - p_prod| ≤ M/x.
  rw [show |(count_X : ℝ) / x - (A : ℝ) / (M : ℝ)| =
        |((count_X : ℝ) - x * ((A : ℝ) / (M : ℝ))) / x| from by
    congr 1
    field_simp]
  rw [abs_div, abs_of_pos hx_pos]
  exact div_le_div_of_nonneg_right h_diff_x_bound hx_pos.le

/-! ### Derived helpers: AP-reciprocal-prime sums (paper §2, §4 partial-summation bridges)

These are derived lemmas obtained from `siegel_walfisz` / `brun_titchmarsh`
via partial summation (Abel's summation formula).  Paper §2 eq:SW-reciprocal
and paper §4 eq:Sp-bound.  They are NOT new axioms. -/

private noncomputable def apCoeffMod (q a n : ℕ) : ℝ :=
  if n.Prime ∧ n % q = a % q then 1 else 0

private lemma apCoeffMod_sum_eq_piMod (t : ℝ) (q a : ℕ) :
    (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apCoeffMod q a k) = (piMod t q a : ℝ) := by
  rw [piMod]
  simp only [apCoeffMod, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one]
  norm_num
  rw [← Nat.subtype_card ({x ∈ Finset.Icc 0 ⌊t⌋₊ | Nat.Prime x ∧ x % q = a % q})]
  intro x
  simp

private lemma sum_filter_eq_Ioc_indicator_real {q a : ℕ} {X Y : ℝ}
    (hXnonneg : 0 ≤ X) (hYnonneg : 0 ≤ Y) :
    (∑ p ∈ Finset.filter
        (fun p => p.Prime ∧ p % q = a % q ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ Y)
        (Finset.Iic ⌊Y⌋₊), (1 : ℝ) / (p : ℝ))
      = ∑ p ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊,
          ((1 : ℝ) / (p : ℝ)) * (if p.Prime ∧ p % q = a % q then (1 : ℝ) else 0) := by
  conv_rhs =>
    enter [2, p]
    rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
    constructor
    · rintro ⟨hp_floorY, hpprime, hpmod, hXp, _hpY⟩
      exact ⟨⟨(Nat.floor_lt hXnonneg).2 hXp, hp_floorY⟩, hpprime, hpmod⟩
    · rintro ⟨⟨hfloorX, hp_floorY⟩, hpprime, hpmod⟩
      exact ⟨hp_floorY, hpprime, hpmod,
        (Nat.floor_lt hXnonneg).1 hfloorX,
        (Nat.cast_le.mpr hp_floorY).trans (Nat.floor_le hYnonneg)⟩
  · intro p hp
    rfl

private lemma abel_AP_formula (q a : ℕ) {X Y : ℝ} (hX_pos : 0 < X) (hXY : X ≤ Y) :
    ∑ k ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, ((1 : ℝ) / (k : ℝ)) * apCoeffMod q a k =
      ((1 : ℝ) / Y) * (piMod Y q a : ℝ)
        - ((1 : ℝ) / X) * (piMod X q a : ℝ)
        - ∫ t in Set.Ioc X Y,
            deriv (fun u : ℝ => (1 : ℝ) / u) t * (piMod t q a : ℝ) := by
  have hX_nonneg : (0 : ℝ) ≤ X := hX_pos.le
  have hf_diff : ∀ t ∈ Set.Icc X Y,
      DifferentiableAt ℝ (fun u : ℝ => (1 : ℝ) / u) t := by
    intro t ht
    have htpos : 0 < t := hX_pos.trans_le ht.1
    simpa [one_div] using
      (differentiableAt_id : DifferentiableAt ℝ (fun u : ℝ => u) t).inv (ne_of_gt htpos)
  have hf_int : IntegrableOn (deriv (fun u : ℝ => (1 : ℝ) / u)) (Set.Icc X Y) := by
    have hcont : ContinuousOn (fun u : ℝ => - (u ^ 2)⁻¹) (Set.Icc X Y) := by
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀
      · exact (continuousOn_id.pow 2)
      · intro u hu hzero
        have hu_pos : 0 < u := hX_pos.trans_le hu.1
        exact (ne_of_gt hu_pos) (sq_eq_zero_iff.mp hzero)
    simpa [one_div, deriv_inv'] using hcont.integrableOn_Icc
  simpa [apCoeffMod_sum_eq_piMod] using
    (sum_mul_eq_sub_sub_integral_mul (c := apCoeffMod q a)
      (f := fun u : ℝ => (1 : ℝ) / u) hX_nonneg hXY hf_diff hf_int)

private lemma abel_AP_formula_interval (q a : ℕ) {X Y : ℝ} (hX_pos : 0 < X)
    (hXY : X ≤ Y) :
    ∑ k ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, ((1 : ℝ) / (k : ℝ)) * apCoeffMod q a k =
      ((1 : ℝ) / Y) * (piMod Y q a : ℝ)
        - ((1 : ℝ) / X) * (piMod X q a : ℝ)
        + ∫ t in X..Y, (piMod t q a : ℝ) / t ^ 2 := by
  have habel := abel_AP_formula q a hX_pos hXY
  have hint_eq :
      -∫ t in Set.Ioc X Y,
          deriv (fun u : ℝ => (1 : ℝ) / u) t * (piMod t q a : ℝ)
        = ∫ t in X..Y, (piMod t q a : ℝ) / t ^ 2 := by
    rw [← intervalIntegral.integral_of_le hXY, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht_pos : 0 < t := by
      have ht' : t ∈ Set.Icc X Y := by
        simpa [Set.uIcc_of_le hXY] using ht
      exact hX_pos.trans_le ht'.1
    simp [deriv_inv', div_eq_mul_inv, mul_comm]
  linarith

private lemma invLog_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun u : ℝ => (Real.log u)⁻¹) (Set.Icc a b) := by
  have hlog_cont : ContinuousOn (fun u : ℝ => Real.log u) (Set.Icc a b) := by
    exact Real.continuousOn_log.comp continuousOn_id (by
      intro u hu
      exact ne_of_gt ((lt_trans (by norm_num) ha).trans_le hu.1))
  exact hlog_cont.inv₀ (by
    intro u hu hzero
    have hlog_pos : 0 < Real.log u := Real.log_pos (ha.trans_le hu.1)
    exact (ne_of_gt hlog_pos) hzero)

private lemma invLog_continuousAt {t : ℝ} (ht : 1 < t) :
    ContinuousAt (fun u : ℝ => (Real.log u)⁻¹) t := by
  exact (Real.continuousAt_log (ne_of_gt (lt_trans (by norm_num) ht))).inv₀
    (ne_of_gt (Real.log_pos ht))

private lemma li_hasDerivAt {t : ℝ} (ht : 2 < t) :
    HasDerivAt li ((Real.log t)⁻¹) t := by
  unfold li
  have hcont_Icc : ContinuousOn (fun u : ℝ => (Real.log u)⁻¹) (Set.Icc (2 : ℝ) t) :=
    invLog_continuousOn (by norm_num)
  have hint : IntervalIntegrable (fun u : ℝ => (Real.log u)⁻¹) volume (2 : ℝ) t := by
    have hcont_u : ContinuousOn (fun u : ℝ => (Real.log u)⁻¹) (Set.uIcc (2 : ℝ) t) := by
      simpa [Set.uIcc_of_le ht.le] using hcont_Icc
    exact hcont_u.intervalIntegrable
  have ht1 : t ∈ Set.Ioi (1 : ℝ) := lt_trans (by norm_num) ht
  have hsm : StronglyMeasurableAtFilter (fun u : ℝ => (Real.log u)⁻¹) (nhds t) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun x hx => invLog_continuousAt hx) t ht1
  have hct : ContinuousAt (fun u : ℝ => (Real.log u)⁻¹) t := invLog_continuousAt ht1
  simpa [one_div] using intervalIntegral.integral_hasDerivAt_right hint hsm hct

private lemma li_continuousOn {X Y : ℝ} (hX : 3 ≤ X) :
    ContinuousOn li (Set.Icc X Y) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  exact (li_hasDerivAt (by linarith [ht.1])).continuousAt

private lemma li_div_continuousOn {X Y : ℝ} (hX : 3 ≤ X) :
    ContinuousOn (fun t : ℝ => li t / t) (Set.Icc X Y) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  have ht2 : 2 < t := by linarith [ht.1]
  have ht0 : t ≠ 0 := by positivity
  exact ((li_hasDerivAt ht2).div (hasDerivAt_id t) ht0).continuousAt

private lemma one_div_mul_log_continuousOn {X Y : ℝ} (hX : 3 ≤ X) :
    ContinuousOn (fun t : ℝ => 1 / (t * Real.log t)) (Set.Icc X Y) := by
  have hlog_cont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc X Y) := by
    exact Real.continuousOn_log.comp continuousOn_id (by
      intro t ht
      exact ne_of_gt (by linarith [hX, ht.1]))
  have hden : ∀ t ∈ Set.Icc X Y, t * Real.log t ≠ 0 := by
    intro t ht hzero
    exact mul_ne_zero (ne_of_gt (by linarith [hX, ht.1]))
      (ne_of_gt (Real.log_pos (by linarith [hX, ht.1]))) hzero
  exact continuousOn_const.div (continuousOn_id.mul hlog_cont) hden

private lemma li_div_sq_continuousOn {X Y : ℝ} (hX : 3 ≤ X) :
    ContinuousOn (fun t : ℝ => li t / t ^ 2) (Set.Icc X Y) := by
  have hli : ContinuousOn li (Set.Icc X Y) := li_continuousOn hX
  have hden2 : ∀ t ∈ Set.Icc X Y, t ^ 2 ≠ 0 := by
    intro t ht hzero
    exact (ne_of_gt (by linarith [hX, ht.1])) (sq_eq_zero_iff.mp hzero)
  exact hli.div (continuousOn_id.pow 2) hden2

private lemma main_kernel_continuousOn {X Y : ℝ} (hX : 3 ≤ X) :
    ContinuousOn (fun t : ℝ => 1 / (t * Real.log t) - li t / t ^ 2) (Set.Icc X Y) := by
  exact (one_div_mul_log_continuousOn hX).sub (li_div_sq_continuousOn hX)

private lemma li_div_hasDerivAt {t : ℝ} (ht : 2 < t) :
    HasDerivAt (fun u : ℝ => li u / u)
      (1 / (t * Real.log t) - li t / t ^ 2) t := by
  have ht0 : t ≠ 0 := by positivity
  have hlog_ne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  convert (li_hasDerivAt ht).div (hasDerivAt_id t) ht0 using 1
  simp only [id_eq]
  field_simp [ht0, hlog_ne]

private lemma intervalIntegrable_of_continuousOn_Icc {f : ℝ → ℝ} {X Y : ℝ}
    (hXY : X ≤ Y) (hf : ContinuousOn f (Set.Icc X Y)) :
    IntervalIntegrable f volume X Y := by
  have hfu : ContinuousOn f (Set.uIcc X Y) := by
    simpa [Set.uIcc_of_le hXY] using hf
  exact hfu.intervalIntegrable

private lemma li_partial_summation_main {X Y : ℝ} (hX : 3 ≤ X) (hXY : X ≤ Y) :
    (li Y / Y - li X / X) + ∫ t in X..Y, li t / t ^ 2 =
      ∫ t in X..Y, 1 / (t * Real.log t) := by
  have hFcont : ContinuousOn (fun t : ℝ => li t / t) (Set.Icc X Y) :=
    li_div_continuousOn hX
  have hderiv : ∀ t ∈ Set.Ioo X Y,
      HasDerivAt (fun u : ℝ => li u / u) (1 / (t * Real.log t) - li t / t ^ 2) t := by
    intro t ht
    exact li_div_hasDerivAt (by linarith [hX, ht.1])
  have hkcont : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t) - li t / t ^ 2)
      (Set.Icc X Y) := main_kernel_continuousOn hX
  have hkint : IntervalIntegrable
      (fun t : ℝ => 1 / (t * Real.log t) - li t / t ^ 2) volume X Y :=
    intervalIntegrable_of_continuousOn_Icc hXY hkcont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hXY hFcont hderiv hkint
  have h1int : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t)) volume X Y :=
    intervalIntegrable_of_continuousOn_Icc hXY (one_div_mul_log_continuousOn hX)
  have h2int : IntervalIntegrable (fun t : ℝ => li t / t ^ 2) volume X Y :=
    intervalIntegrable_of_continuousOn_Icc hXY (li_div_sq_continuousOn hX)
  have h_int_sub : (∫ t in X..Y, (1 / (t * Real.log t) - li t / t ^ 2)) =
      (∫ t in X..Y, 1 / (t * Real.log t)) - ∫ t in X..Y, li t / t ^ 2 := by
    rw [intervalIntegral.integral_sub h1int h2int]
  rw [h_int_sub] at hFTC
  linarith

private lemma piMod_div_sq_integrableOn_Icc (q a : ℕ) {X Y : ℝ} (hX_pos : 0 < X) :
    IntegrableOn (fun t : ℝ => (piMod t q a : ℝ) / t ^ 2) (Set.Icc X Y) := by
  have hX_nonneg : 0 ≤ X := hX_pos.le
  have hg_cont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc X Y) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht hzero
      have ht_pos : 0 < t := hX_pos.trans_le ht.1
      exact (ne_of_gt ht_pos) (sq_eq_zero_iff.mp hzero)
  have hg_int_on : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc X Y) :=
    hg_cont.integrableOn_Icc
  have hmul := integrableOn_mul_sum_Icc (c := apCoeffMod q a) (a := X) (b := Y) (m := 0)
    hX_nonneg hg_int_on
  convert hmul using 1
  ext t
  rw [apCoeffMod_sum_eq_piMod]
  simp [div_eq_mul_inv, mul_comm]

private lemma piMod_div_sq_intervalIntegrable (q a : ℕ) {X Y : ℝ} (hX_pos : 0 < X)
    (hXY : X ≤ Y) :
    IntervalIntegrable (fun t : ℝ => (piMod t q a : ℝ) / t ^ 2) volume X Y :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hXY).2
    (piMod_div_sq_integrableOn_Icc q a hX_pos)

private lemma tail_antideriv {c t : ℝ} (hc : 0 < c) (ht : 1 < t) :
    HasDerivAt
      (fun u : ℝ => -(2 / c) * (Real.sqrt (Real.log u) + 1 / c) *
        Real.exp (-c * Real.sqrt (Real.log u)))
      (Real.exp (-c * Real.sqrt (Real.log t)) / t) t := by
  have ht_pos : 0 < t := lt_trans (by norm_num) ht
  have hlog_pos : 0 < Real.log t := Real.log_pos ht
  have hsqrt_ne : Real.sqrt (Real.log t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlog_pos)
  have hlog_ne : Real.log t ≠ 0 := ne_of_gt hlog_pos
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hsqrt_deriv : HasDerivAt (fun u : ℝ => Real.sqrt (Real.log u))
      (t⁻¹ / (2 * Real.sqrt (Real.log t))) t := by
    exact (Real.hasDerivAt_log ht_ne).sqrt hlog_ne
  have hexp_deriv : HasDerivAt (fun u : ℝ => Real.exp (-c * Real.sqrt (Real.log u)))
      (Real.exp (-c * Real.sqrt (Real.log t)) *
        (-(c * (t⁻¹ / (2 * Real.sqrt (Real.log t)))))) t := by
    convert (Real.hasDerivAt_exp (-c * Real.sqrt (Real.log t))).comp t
      ((hasDerivAt_const t (-c)).mul hsqrt_deriv) using 1
    · ring_nf
  have hprod := ((hasDerivAt_const t (-(2 / c))).mul
    ((hsqrt_deriv.add (hasDerivAt_const t (1 / c))).mul hexp_deriv))
  convert hprod using 1
  · funext u
    simp only [Pi.add_apply, Pi.mul_apply]
    ring_nf
  · simp only [Pi.add_apply, Pi.mul_apply]
    field_simp [hc_ne, ht_ne, hsqrt_ne]
    ring_nf

private lemma tailKernel_continuousOn {c X Y : ℝ} (hX : 1 < X) :
    ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
      (Set.Icc X Y) := by
  have hlog_cont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc X Y) := by
    exact Real.continuousOn_log.comp continuousOn_id (by
      intro t ht
      exact ne_of_gt (lt_trans (by norm_num) (hX.trans_le ht.1)))
  have hsqrt_cont : ContinuousOn (fun t : ℝ => Real.sqrt (Real.log t)) (Set.Icc X Y) :=
    hlog_cont.sqrt
  have hnegc : ContinuousOn (fun t : ℝ => -c * Real.sqrt (Real.log t)) (Set.Icc X Y) :=
    continuousOn_const.mul hsqrt_cont
  have hexp_cont : ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)))
      (Set.Icc X Y) := by
    simpa [Function.comp_def] using Real.continuous_exp.comp_continuousOn hnegc
  exact hexp_cont.div continuousOn_id (by
    intro t ht
    exact ne_of_gt ((lt_trans (by norm_num) hX).trans_le ht.1))

private lemma tailAntideriv_continuousOn {c X Y : ℝ} (hX : 1 < X) :
    ContinuousOn
      (fun u : ℝ => -(2 / c) * (Real.sqrt (Real.log u) + 1 / c) *
        Real.exp (-c * Real.sqrt (Real.log u))) (Set.Icc X Y) := by
  have hlog_cont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc X Y) := by
    exact Real.continuousOn_log.comp continuousOn_id (by
      intro t ht
      exact ne_of_gt (lt_trans (by norm_num) (hX.trans_le ht.1)))
  have hsqrt_cont : ContinuousOn (fun t : ℝ => Real.sqrt (Real.log t)) (Set.Icc X Y) :=
    hlog_cont.sqrt
  have hnegc : ContinuousOn (fun t : ℝ => -c * Real.sqrt (Real.log t)) (Set.Icc X Y) :=
    continuousOn_const.mul hsqrt_cont
  have hexp_cont : ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)))
      (Set.Icc X Y) := by
    simpa [Function.comp_def] using Real.continuous_exp.comp_continuousOn hnegc
  exact (continuousOn_const.mul (hsqrt_cont.add continuousOn_const)).mul hexp_cont

private lemma tail_integral_le_exp {c X Y : ℝ} (hc : 0 < c) (hX3 : 3 ≤ X)
    (hXY : X ≤ Y) :
    (∫ t in X..Y, Real.exp (-c * Real.sqrt (Real.log t)) / t) ≤
      (6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
  let F : ℝ → ℝ := fun u => -(2 / c) * (Real.sqrt (Real.log u) + 1 / c) *
        Real.exp (-c * Real.sqrt (Real.log u))
  let K : ℝ → ℝ := fun t => Real.exp (-c * Real.sqrt (Real.log t)) / t
  have hX1 : 1 < X := by linarith
  have hFcont : ContinuousOn F (Set.Icc X Y) := tailAntideriv_continuousOn (c := c) hX1
  have hderiv : ∀ t ∈ Set.Ioo X Y, HasDerivAt F (K t) t := by
    intro t ht
    exact tail_antideriv hc (hX1.trans ht.1)
  have hKint : IntervalIntegrable K volume X Y := by
    have hKcont : ContinuousOn K (Set.Icc X Y) := tailKernel_continuousOn (c := c) hX1
    have hKu : ContinuousOn K (Set.uIcc X Y) := by
      simpa [Set.uIcc_of_le hXY] using hKcont
    exact hKu.intervalIntegrable
  have heq : (∫ t in X..Y, K t) = F Y - F X :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hXY hFcont hderiv hKint
  have hY3 : 3 ≤ Y := hX3.trans hXY
  have hFY_nonpos : F Y ≤ 0 := by
    dsimp [F]
    have hsum_pos : 0 < Real.sqrt (Real.log Y) + 1 / c := by
      have : 0 < 1 / c := by positivity
      have hsqrt_nonneg : 0 ≤ Real.sqrt (Real.log Y) := Real.sqrt_nonneg _
      linarith
    have hexp_pos : 0 < Real.exp (-c * Real.sqrt (Real.log Y)) := Real.exp_pos _
    have hcoef_pos : 0 < 2 / c := by positivity
    nlinarith [mul_pos (mul_pos hcoef_pos hsum_pos) hexp_pos]
  rw [heq]
  calc
    F Y - F X ≤ -F X := by linarith
    _ = (2 / c) * (Real.sqrt (Real.log X) + 1 / c) *
        Real.exp (-c * Real.sqrt (Real.log X)) := by
          dsimp [F]
          ring
    _ ≤ (6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
      let u := Real.sqrt (Real.log X)
      have hu_nonneg : 0 ≤ u := by dsimp [u]; exact Real.sqrt_nonneg _
      have hc_ne : c ≠ 0 := ne_of_gt hc
      have hcu_nonneg : 0 ≤ (c / 2) * u := by positivity
      have hinvc_nonneg : 0 ≤ 1 / c := by positivity
      have htwodivc_nonneg : 0 ≤ 2 / c := by positivity
      have hy_le_exp : (c / 2) * u ≤ Real.exp ((c / 2) * u) := by
        have h1 := Real.add_one_le_exp ((c / 2) * u)
        linarith
      have hu_le : u ≤ (2 / c) * Real.exp ((c / 2) * u) := by
        calc
          u = (2 / c) * ((c / 2) * u) := by field_simp [hc_ne]
          _ ≤ (2 / c) * Real.exp ((c / 2) * u) := by
            exact mul_le_mul_of_nonneg_left hy_le_exp htwodivc_nonneg
      have hone_le : 1 / c ≤ (1 / c) * Real.exp ((c / 2) * u) := by
        have h1exp : 1 ≤ Real.exp ((c / 2) * u) := Real.one_le_exp hcu_nonneg
        simpa using mul_le_mul_of_nonneg_left h1exp hinvc_nonneg
      have hsum_le : u + 1 / c ≤ (3 / c) * Real.exp ((c / 2) * u) := by
        calc
          u + 1 / c ≤ (2 / c) * Real.exp ((c / 2) * u) +
              (1 / c) * Real.exp ((c / 2) * u) := add_le_add hu_le hone_le
          _ = (3 / c) * Real.exp ((c / 2) * u) := by ring
      have hexp_nonneg : 0 ≤ Real.exp (-c * u) := Real.exp_nonneg _
      calc
        (2 / c) * (Real.sqrt (Real.log X) + 1 / c) *
            Real.exp (-c * Real.sqrt (Real.log X))
            = (2 / c) * (u + 1 / c) * Real.exp (-c * u) := rfl
        _ ≤ (2 / c) * ((3 / c) * Real.exp ((c / 2) * u)) * Real.exp (-c * u) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum_le htwodivc_nonneg) hexp_nonneg
        _ = (6 / c ^ 2) * (Real.exp ((c / 2) * u) * Real.exp (-c * u)) := by
          field_simp [hc_ne]
          ring
        _ = (6 / c ^ 2) * Real.exp (-(c / 2) * u) := by
          rw [← Real.exp_add]
          ring_nf
        _ = (6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := rfl

private lemma sw_log_power_mono {A X t : ℝ} {q : ℕ} (hA : 0 < A) (hX3 : 3 ≤ X)
    (hXt : X ≤ t) (hqX : (q : ℝ) ≤ (Real.log X) ^ A) :
    (q : ℝ) ≤ (Real.log t) ^ A := by
  have hXpos : 0 < X := by linarith
  have hlogX_nonneg : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogt_nonneg : 0 ≤ Real.log t := Real.log_nonneg (by linarith [hXt])
  have hlog_le : Real.log X ≤ Real.log t := Real.log_le_log hXpos hXt
  have hpow_le : (Real.log X) ^ A ≤ (Real.log t) ^ A := by
    exact (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hA.le)
      hlogX_nonneg hlogt_nonneg hlog_le
  exact hqX.trans hpow_le

private lemma sw_exp_decay_le_half {c X t : ℝ} (hc : 0 < c) (hX3 : 3 ≤ X)
    (hXt : X ≤ t) :
    Real.exp (-c * Real.sqrt (Real.log t)) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
  apply Real.exp_le_exp.mpr
  have hXpos : 0 < X := by linarith
  have hlog_le : Real.log X ≤ Real.log t := Real.log_le_log hXpos hXt
  have hsqrt_le : Real.sqrt (Real.log X) ≤ Real.sqrt (Real.log t) :=
    Real.sqrt_le_sqrt hlog_le
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Real.log X) := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hsqrt_le hc.le]

private lemma sw_reciprocal_decomposition (q a : ℕ) {X Y : ℝ} (hX3 : 3 ≤ X)
    (hXY : X ≤ Y) :
    (∑ p ∈ Finset.filter
        (fun p => p.Prime ∧ p % q = a % q ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ Y)
        (Finset.Iic ⌊Y⌋₊), (1 : ℝ) / (p : ℝ))
      - (1 / (q.totient : ℝ)) * ∫ t in X..Y, 1 / (t * Real.log t)
      =
        (1 / Y) * ((piMod Y q a : ℝ) - li Y / (q.totient : ℝ))
          - (1 / X) * ((piMod X q a : ℝ) - li X / (q.totient : ℝ))
          + ∫ t in X..Y,
              ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2 := by
  have hX_pos : 0 < X := by linarith
  have hX_nonneg : 0 ≤ X := hX_pos.le
  have hY_nonneg : 0 ≤ Y := hX_nonneg.trans hXY
  have hsum_indicator := sum_filter_eq_Ioc_indicator_real (q := q) (a := a)
    (X := X) (Y := Y) hX_nonneg hY_nonneg
  have hsum :
      (∑ p ∈ Finset.filter
          (fun p => p.Prime ∧ p % q = a % q ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ Y)
          (Finset.Iic ⌊Y⌋₊), (1 : ℝ) / (p : ℝ))
        = ∑ p ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊,
            ((1 : ℝ) / (p : ℝ)) * apCoeffMod q a p := by
    simpa [apCoeffMod] using hsum_indicator
  have habel := abel_AP_formula_interval q a hX_pos hXY
  have hmain := li_partial_summation_main hX3 hXY
  have hpi_int : IntervalIntegrable (fun t : ℝ => (piMod t q a : ℝ) / t ^ 2)
      volume X Y := piMod_div_sq_intervalIntegrable q a hX_pos hXY
  have hli_int : IntervalIntegrable (fun t : ℝ => li t / t ^ 2) volume X Y :=
    intervalIntegrable_of_continuousOn_Icc hXY (li_div_sq_continuousOn hX3)
  have herror_int :
      (∫ t in X..Y, ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2)
        = (∫ t in X..Y, (piMod t q a : ℝ) / t ^ 2)
          - (1 / (q.totient : ℝ)) * ∫ t in X..Y, li t / t ^ 2 := by
    calc
      (∫ t in X..Y, ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2)
          = ∫ t in X..Y,
              (piMod t q a : ℝ) / t ^ 2 - (1 / (q.totient : ℝ)) * (li t / t ^ 2) := by
            apply intervalIntegral.integral_congr
            intro t _ht
            ring_nf
      _ = (∫ t in X..Y, (piMod t q a : ℝ) / t ^ 2)
          - ∫ t in X..Y, (1 / (q.totient : ℝ)) * (li t / t ^ 2) := by
            rw [intervalIntegral.integral_sub hpi_int (hli_int.const_mul _)]
      _ = (∫ t in X..Y, (piMod t q a : ℝ) / t ^ 2)
          - (1 / (q.totient : ℝ)) * ∫ t in X..Y, li t / t ^ 2 := by
            rw [intervalIntegral.integral_const_mul]
  rw [hsum, habel, ← hmain, herror_int]
  ring_nf

private lemma sw_integral_error_bound {A c C X Y : ℝ} {q a : ℕ}
    (hA : 0 < A) (hc : 0 < c) (hC : 0 < C)
    (hSW : ∀ t : ℝ, 2 ≤ t →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log t) ^ A →
        ∀ a : ℕ, Nat.Coprime a q →
          |((piMod t q a : ℝ)) - li t / (q.totient : ℝ)| ≤
            C * t * Real.exp (-c * Real.sqrt (Real.log t)))
    (hX3 : 3 ≤ X) (hXY : X ≤ Y) (hq1 : 1 ≤ q)
    (hqX : (q : ℝ) ≤ (Real.log X) ^ A) (ha : Nat.Coprime a q) :
    |∫ t in X..Y, ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2|
      ≤ C * (6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
  have hX1 : 1 < X := by linarith
  have hkernel_cont :
      ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
        (Set.Icc X Y) := tailKernel_continuousOn (c := c) hX1
  have hkernel_u :
      ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
        (Set.uIcc X Y) := by
    simpa [Set.uIcc_of_le hXY] using hkernel_cont
  have hkernel_int :
      IntervalIntegrable (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
        volume X Y := hkernel_u.intervalIntegrable
  have hbound_int :
      IntervalIntegrable (fun t : ℝ => C * Real.exp (-c * Real.sqrt (Real.log t)) / t)
        volume X Y := by
    simpa [div_eq_mul_inv, mul_assoc] using hkernel_int.const_mul C
  have hpoint :
      ∀ᵐ t ∂volume, t ∈ Set.Ioc X Y →
        ‖((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2‖ ≤
          C * Real.exp (-c * Real.sqrt (Real.log t)) / t := by
    filter_upwards with t ht
    have hXt : X ≤ t := ht.1.le
    have ht2 : 2 ≤ t := by linarith
    have htpos : 0 < t := by linarith
    have hqt : (q : ℝ) ≤ (Real.log t) ^ A :=
      sw_log_power_mono hA hX3 hXt hqX
    have hsw := hSW t ht2 q hq1 hqt a ha
    have hdiv := div_le_div_of_nonneg_right hsw (by positivity : 0 ≤ t ^ 2)
    have hleft_eq : |↑(piMod t q a) - li t / ↑q.totient| / t ^ 2 =
        ‖((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2‖ := by
      rw [Real.norm_eq_abs]
      calc
        |↑(piMod t q a) - li t / ↑q.totient| / t ^ 2 =
            |↑(piMod t q a) - li t / ↑q.totient| / |t ^ 2| := by
              rw [abs_of_pos (sq_pos_of_pos htpos)]
        _ = |(↑(piMod t q a) - li t / ↑q.totient) / t ^ 2| := by
              rw [abs_div]
    have hright_eq : C * t * Real.exp (-c * Real.sqrt (Real.log t)) / t ^ 2 =
        C * Real.exp (-c * Real.sqrt (Real.log t)) / t := by
      field_simp [ne_of_gt htpos]
    rw [hleft_eq] at hdiv
    rw [hright_eq] at hdiv
    exact hdiv
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ t in X..Y, ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2‖
        ≤ ∫ t in X..Y, C * Real.exp (-c * Real.sqrt (Real.log t)) / t :=
          intervalIntegral.norm_integral_le_of_norm_le hXY hpoint hbound_int
    _ = C * ∫ t in X..Y, Real.exp (-c * Real.sqrt (Real.log t)) / t := by
          simp [div_eq_mul_inv, mul_assoc]
    _ ≤ C * ((6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X))) := by
          exact mul_le_mul_of_nonneg_left (tail_integral_le_exp hc hX3 hXY) hC.le
    _ = C * (6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
          ring

private lemma sw_boundary_error_bound {A c C X t : ℝ} {q a : ℕ}
    (hA : 0 < A) (hc : 0 < c) (hC : 0 < C)
    (hSW : ∀ t : ℝ, 2 ≤ t →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log t) ^ A →
        ∀ a : ℕ, Nat.Coprime a q →
          |((piMod t q a : ℝ)) - li t / (q.totient : ℝ)| ≤
            C * t * Real.exp (-c * Real.sqrt (Real.log t)))
    (hX3 : 3 ≤ X) (hXt : X ≤ t) (hq1 : 1 ≤ q)
    (hqX : (q : ℝ) ≤ (Real.log X) ^ A) (ha : Nat.Coprime a q) :
    |(1 / t) * ((piMod t q a : ℝ) - li t / (q.totient : ℝ))|
      ≤ C * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
  have ht2 : 2 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have hqt : (q : ℝ) ≤ (Real.log t) ^ A :=
    sw_log_power_mono hA hX3 hXt hqX
  have hsw := hSW t ht2 q hq1 hqt a ha
  have hdiv := div_le_div_of_nonneg_right hsw htpos.le
  have hleft_eq :
      |(1 / t) * ((piMod t q a : ℝ) - li t / (q.totient : ℝ))|
        = |↑(piMod t q a) - li t / ↑q.totient| / t := by
    rw [abs_mul, abs_of_pos (one_div_pos.mpr htpos), div_eq_mul_inv]
    ring
  have hright_eq : C * t * Real.exp (-c * Real.sqrt (Real.log t)) / t =
      C * Real.exp (-c * Real.sqrt (Real.log t)) := by
    field_simp [ne_of_gt htpos]
  rw [← hleft_eq] at hdiv
  rw [hright_eq] at hdiv
  exact hdiv.trans (mul_le_mul_of_nonneg_left (sw_exp_decay_le_half hc hX3 hXt) hC.le)

/-- **Paper §2 eq:SW-reciprocal — exact paper statement.**

For every `A₀ > 0` there exist `c₀ > 0` (and an implied constant) such that,
for all `3 ≤ X ≤ Y`, every `q ≤ (log X)^{A₀}` with `(a, q) = 1`,
`∑_{X < p ≤ Y, p ≡ a mod q, p prime} 1/p
   = (1/φ(q)) · ∫_X^Y dt/(t log t) + O_{A₀}(exp(-c₀ √(log X)))`.

Proof: partial summation on `π(t; q, a)` + `siegel_walfisz`. -/
theorem sw_reciprocal_AP :
    ∀ A₀ : ℝ, 0 < A₀ →
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ X Y : ℝ, 3 ≤ X → X ≤ Y →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ A₀ →
            ∀ a : ℕ, Nat.Coprime a q →
              |(∑ p ∈ Finset.filter
                  (fun p => p.Prime ∧ p % q = a % q ∧
                    X < (p : ℝ) ∧ (p : ℝ) ≤ Y)
                  (Finset.Iic ⌊Y⌋₊),
                (1 : ℝ) / (p : ℝ))
                - (1 / (q.totient : ℝ)) * ∫ t in X..Y, 1 / (t * Real.log t)|
              ≤ C * Real.exp (-c₀ * Real.sqrt (Real.log X)) := by
  classical
  intro A₀ hA₀
  rcases siegel_walfisz A₀ hA₀ with ⟨c, hc, Csw, hCsw, hSW⟩
  let c₀ : ℝ := c / 2
  let C : ℝ := Csw * (2 + 6 / c ^ 2)
  refine ⟨c₀, ?_, C, ?_, ?_⟩
  · dsimp [c₀]
    positivity
  · dsimp [C]
    positivity
  · intro X Y hX3 hXY q hq1 hqX a ha
    have hdecomp := sw_reciprocal_decomposition q a hX3 hXY
    rw [hdecomp]
    set E : ℝ := Real.exp (-(c / 2) * Real.sqrt (Real.log X))
    set u : ℝ := (1 / Y) * ((piMod Y q a : ℝ) - li Y / (q.totient : ℝ))
    set v : ℝ := (1 / X) * ((piMod X q a : ℝ) - li X / (q.totient : ℝ))
    set w : ℝ := ∫ t in X..Y, ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2
    change |u - v + w| ≤ C * E
    have hu : |u| ≤ Csw * E := by
      dsimp [u, E]
      exact sw_boundary_error_bound hA₀ hc hCsw hSW hX3 hXY hq1 hqX ha
    have hv : |v| ≤ Csw * E := by
      dsimp [v, E]
      exact sw_boundary_error_bound hA₀ hc hCsw hSW hX3 le_rfl hq1 hqX ha
    have hw : |w| ≤ Csw * (6 / c ^ 2) * E := by
      dsimp [w, E]
      exact sw_integral_error_bound hA₀ hc hCsw hSW hX3 hXY hq1 hqX ha
    have htri : |u - v + w| ≤ |u| + |v| + |w| := by
      have h1 : |u - v| ≤ |u| + |v| := by
        simpa [sub_eq_add_neg] using abs_add_le u (-v)
      have h2 : |u - v + w| ≤ |u - v| + |w| := abs_add_le (u - v) w
      nlinarith
    calc
      |u - v + w| ≤ |u| + |v| + |w| := htri
      _ ≤ Csw * E + Csw * E + Csw * (6 / c ^ 2) * E := by
        nlinarith [hu, hv, hw]
      _ = C * E := by
        dsimp [C]
        ring


private noncomputable def apCoeff (p n : ℕ) : ℝ :=
  if n.Prime ∧ n % p = 1 % p then 1 else 0

private lemma apCoeff_sum_eq_piMod (t : ℝ) (p : ℕ) :
    (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apCoeff p k) = (piMod t p 1 : ℝ) := by
  rw [piMod]
  simp only [apCoeff, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one]
  norm_num
  rw [← Nat.subtype_card ({x ∈ Finset.Icc 0 ⌊t⌋₊ | Nat.Prime x ∧ x % p = 1 % p})]
  intro x
  simp

private lemma sum_filter_eq_Ioc_indicator {p N : ℕ} {Q : ℝ} (hQnonneg : 0 ≤ Q)
    (hp1 : 1 % p = 1) :
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (N : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ))
      = ∑ q ∈ Finset.Ioc N ⌊Q⌋₊,
          ((1 : ℝ) / (q : ℝ)) * (if q.Prime ∧ q % p = 1 % p then (1 : ℝ) else 0) := by
  conv_rhs =>
    enter [2, q]
    rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext q
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
    constructor
    · rintro ⟨hqfloor, hprime, hmod, hNreal, _hqQ⟩
      have hNq : N < q := by exact_mod_cast hNreal
      have hmod' : q % p = 1 % p := by simpa [hp1] using hmod
      exact ⟨⟨hNq, hqfloor⟩, hprime, hmod'⟩
    · rintro ⟨⟨hNq, hqfloor⟩, hprime, hmod⟩
      have hmod' : q % p = 1 := by simpa [hp1] using hmod
      exact ⟨hqfloor, hprime, hmod', by exact_mod_cast hNq,
        (Nat.cast_le.mpr hqfloor).trans (Nat.floor_le hQnonneg)⟩
  · intro q hq
    rfl

private lemma low_AP_sum_le_inv {p : ℕ} (hp : p.Prime) :
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (2 * p : ℝ))
        (Finset.Iic (2 * p)), (1 : ℝ) / (q : ℝ)) ≤ 1 / (p : ℝ) := by
  classical
  let s := Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (2 * p : ℝ))
        (Finset.Iic (2 * p))
  have hs_card : s.card ≤ 1 := by
    calc
      s.card = Nat.card s := (Nat.card_eq_finsetCard s).symm
      _ ≤ Nat.card Unit := by
        refine Nat.card_le_card_of_injective (fun _ : s => ()) ?_
        intro x y _
        ext
        have hxmem := x.2
        have hymem := y.2
        simp only [s, Finset.mem_filter, Finset.mem_Iic] at hxmem hymem
        have hxle2 : x.1 ≤ 2 * p := hxmem.1
        have hyle2 : y.1 ≤ 2 * p := hymem.1
        have hxmod : x.1 % p = 1 := hxmem.2.2.1
        have hymod : y.1 % p = 1 := hymem.2.2.1
        have hx_eq : x.1 = p + 1 := by
          have hq_eq : x.1 = p * (x.1 / p) + x.1 % p := (Nat.div_add_mod x.1 p).symm
          have hxle2' : x.1 ≤ p * 2 := by omega
          have hdivle : x.1 / p ≤ 2 := Nat.div_le_of_le_mul hxle2'
          have hxne1 : x.1 ≠ 1 := hxmem.2.1.ne_one
          interval_cases h : x.1 / p <;> simp [hxmod] at hq_eq <;> omega
        have hy_eq : y.1 = p + 1 := by
          have hq_eq : y.1 = p * (y.1 / p) + y.1 % p := (Nat.div_add_mod y.1 p).symm
          have hyle2' : y.1 ≤ p * 2 := by omega
          have hdivle : y.1 / p ≤ 2 := Nat.div_le_of_le_mul hyle2'
          have hyne1 : y.1 ≠ 1 := hymem.2.1.ne_one
          interval_cases h : y.1 / p <;> simp [hymod] at hq_eq <;> omega
        omega
      _ = 1 := by simp
  have hterm : ∀ q ∈ s, (1 : ℝ) / (q : ℝ) ≤ 1 / (p : ℝ) := by
    intro q hq
    have hqmem := hq
    simp only [s, Finset.mem_filter, Finset.mem_Iic] at hqmem
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq_gt : (p : ℝ) < q := hqmem.2.2.2.1
    exact one_div_le_one_div_of_le hp_pos hq_gt.le
  calc
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (2 * p : ℝ))
        (Finset.Iic (2 * p)), (1 : ℝ) / (q : ℝ)) = ∑ q ∈ s, (1 : ℝ) / (q : ℝ) := rfl
    _ ≤ s.card • (1 / (p : ℝ)) := Finset.sum_le_card_nsmul s (fun q => (1 : ℝ) / q) _ hterm
    _ ≤ 1 / (p : ℝ) := by
      rw [nsmul_eq_mul]
      have hinv_nonneg : 0 ≤ 1 / (p : ℝ) := by positivity
      have hcardreal : (s.card : ℝ) ≤ 1 := by exact_mod_cast hs_card
      nlinarith

private lemma abel_high_formula (p : ℕ) (Q : ℝ) (hp : p.Prime)
    (hQ : (((2 * p : ℕ) : ℝ)) ≤ Q) :
    ∑ k ∈ Finset.Ioc (2 * p) ⌊Q⌋₊, ((1 : ℝ) / (k : ℝ)) * apCoeff p k =
      ((1 : ℝ) / Q) * (∑ k ∈ Finset.Icc 0 ⌊Q⌋₊, apCoeff p k)
        - ((1 : ℝ) / (((2 * p : ℕ) : ℝ))) *
            (∑ k ∈ Finset.Icc 0 (2 * p), apCoeff p k)
        - ∫ t in Set.Ioc (((2 * p : ℕ) : ℝ)) Q,
            deriv (fun u : ℝ => (1 : ℝ) / u) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apCoeff p k := by
  have ha_nonneg : (0 : ℝ) ≤ (((2 * p : ℕ) : ℝ)) := by positivity
  have h2p_pos : (0 : ℝ) < (((2 * p : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 2) hp.pos)
  have hf_diff : ∀ t ∈ Set.Icc (((2 * p : ℕ) : ℝ)) Q,
      DifferentiableAt ℝ (fun u : ℝ => (1 : ℝ) / u) t := by
    intro t ht
    have htpos : 0 < t := h2p_pos.trans_le ht.1
    simpa [one_div] using
      (differentiableAt_id : DifferentiableAt ℝ (fun u : ℝ => u) t).inv (ne_of_gt htpos)
  have hf_int : IntegrableOn (deriv (fun u : ℝ => (1 : ℝ) / u))
      (Set.Icc (((2 * p : ℕ) : ℝ)) Q) := by
    have hcont : ContinuousOn (fun u : ℝ => - (u ^ 2)⁻¹)
        (Set.Icc (((2 * p : ℕ) : ℝ)) Q) := by
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀
      · exact (continuousOn_id.pow 2)
      · intro u hu hzero
        have hu_pos : 0 < u := h2p_pos.trans_le hu.1
        exact (ne_of_gt hu_pos) (sq_eq_zero_iff.mp hzero)
    simpa [one_div, deriv_inv'] using hcont.integrableOn_Icc
  have hfloor2p : ⌊(2 * (p : ℝ))⌋₊ = 2 * p := by
    rw [show (2 * (p : ℝ)) = ((2 * p : ℕ) : ℝ) by norm_num]
    exact Nat.floor_natCast (2 * p)
  simpa [hfloor2p] using
    (sum_mul_eq_sub_sub_integral_mul (c := apCoeff p) (f := fun u : ℝ => (1 : ℝ) / u)
      ha_nonneg hQ hf_diff hf_int)

private lemma integral_inv_mul_log_div {p a b : ℝ} (hp : 0 < p) (ha : p < a)
    (hab : a ≤ b) :
    (∫ t in a..b, (t * Real.log (t / p))⁻¹) =
      Real.log (Real.log (b / p)) - Real.log (Real.log (a / p)) := by
  have hf_cont : ContinuousOn (fun u : ℝ => Real.log (Real.log (u / p))) (Set.Icc a b) := by
    apply ContinuousOn.log
    · apply ContinuousOn.log
      · exact continuousOn_id.div_const p
      · intro t ht
        have ht_pos : 0 < t := (lt_trans hp ha).trans_le ht.1
        exact div_ne_zero (ne_of_gt ht_pos) (ne_of_gt hp)
    · intro t ht
      have htp_gt1 : 1 < t / p := (one_lt_div hp).2 (ha.trans_le ht.1)
      exact ne_of_gt (Real.log_pos htp_gt1)
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun u : ℝ => Real.log (Real.log (u / p))) ((t * Real.log (t / p))⁻¹) t := by
    intro t ht
    have ht_pos : 0 < t := (lt_trans hp ha).trans ht.1
    have htp_gt1 : 1 < t / p := (one_lt_div hp).2 (ha.trans ht.1)
    have hlog_ne : Real.log (t / p) ≠ 0 := ne_of_gt (Real.log_pos htp_gt1)
    have hp_ne : p ≠ 0 := ne_of_gt hp
    convert ((Real.hasDerivAt_log hlog_ne).comp t
      (((Real.hasDerivAt_log (div_ne_zero (ne_of_gt ht_pos) hp_ne)).comp t
        ((hasDerivAt_id t).div_const p)))) using 1
    field_simp [hp_ne, hlog_ne]
  have hg_cont : ContinuousOn (fun t : ℝ => (t * Real.log (t / p))⁻¹) (Set.Icc a b) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.mul ((Real.continuousOn_log.comp (continuousOn_id.div_const p))
        (by
          intro t ht
          exact div_ne_zero (ne_of_gt ((lt_trans hp ha).trans_le ht.1)) (ne_of_gt hp)))
    · intro t ht hzero
      have ht_pos : 0 < t := (lt_trans hp ha).trans_le ht.1
      have hlog_pos : 0 < Real.log (t / p) :=
        Real.log_pos ((one_lt_div hp).2 (ha.trans_le ht.1))
      exact mul_ne_zero (ne_of_gt ht_pos) (ne_of_gt hlog_pos) hzero
  have hg_cont_u : ContinuousOn (fun t : ℝ => (t * Real.log (t / p))⁻¹) (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using hg_cont
  have hint : IntervalIntegrable (fun t : ℝ => (t * Real.log (t / p))⁻¹) volume a b :=
    hg_cont_u.intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hf_cont hderiv hint

private lemma high_sum_le_boundary_integral {p : ℕ} {Q : ℝ} (hp : p.Prime)
    (hQ : (((2 * p : ℕ) : ℝ)) ≤ Q) :
    (∑ q ∈ Finset.Ioc (2 * p) ⌊Q⌋₊, ((1 : ℝ) / (q : ℝ)) * apCoeff p q) ≤
      ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ) +
        ∫ t in Set.Ioc (((2 * p : ℕ) : ℝ)) Q, (t ^ 2)⁻¹ * (piMod t p 1 : ℝ) := by
  have habel := abel_high_formula p Q hp hQ
  rw [apCoeff_sum_eq_piMod Q p] at habel
  have hA2_nonneg : 0 ≤ ((1 : ℝ) / (((2 * p : ℕ) : ℝ))) *
      (∑ k ∈ Finset.Icc 0 (2 * p), apCoeff p k) := by
    have hsum_nonneg : 0 ≤ (∑ k ∈ Finset.Icc 0 (2 * p), apCoeff p k) := by
      apply Finset.sum_nonneg
      intro k hk
      unfold apCoeff
      split_ifs <;> norm_num
    positivity
  have hint_eq :
      -∫ t in Set.Ioc (((2 * p : ℕ) : ℝ)) Q,
          deriv (fun u : ℝ => (1 : ℝ) / u) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apCoeff p k
        = ∫ t in Set.Ioc (((2 * p : ℕ) : ℝ)) Q, (t ^ 2)⁻¹ * (piMod t p 1 : ℝ) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change -(deriv (fun u : ℝ => (1 : ℝ) / u) t *
        (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apCoeff p k)) = (t ^ 2)⁻¹ * (piMod t p 1 : ℝ)
    rw [apCoeff_sum_eq_piMod t p]
    simp [one_div, deriv_inv']
  calc
    (∑ q ∈ Finset.Ioc (2 * p) ⌊Q⌋₊, ((1 : ℝ) / (q : ℝ)) * apCoeff p q)
        = ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ) -
          ((1 : ℝ) / (((2 * p : ℕ) : ℝ))) *
            (∑ k ∈ Finset.Icc 0 (2 * p), apCoeff p k) -
          ∫ t in Set.Ioc (((2 * p : ℕ) : ℝ)) Q,
            deriv (fun u : ℝ => (1 : ℝ) / u) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apCoeff p k := habel
    _ ≤ ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ) -
          ∫ t in Set.Ioc (((2 * p : ℕ) : ℝ)) Q,
            deriv (fun u : ℝ => (1 : ℝ) / u) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apCoeff p k := by
          linarith
    _ = ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ) +
        ∫ t in Set.Ioc (((2 * p : ℕ) : ℝ)) Q, (t ^ 2)⁻¹ * (piMod t p 1 : ℝ) := by
          rw [sub_eq_add_neg, hint_eq]

private lemma tail_integral_le {CBT : ℝ} {p : ℕ} {Q : ℝ} (hCBT : 0 < CBT)
    (hp : p.Prime) (hQ : (((2 * p : ℕ) : ℝ)) ≤ Q)
    (hBT : ∀ t : ℝ, (((2 * p : ℕ) : ℝ)) ≤ t →
      (piMod t p 1 : ℝ) ≤ CBT * t / (((p - 1 : ℕ) : ℝ) * Real.log (t / p))) :
    (∫ t in Set.Ioc (((2 * p : ℕ) : ℝ)) Q, (t ^ 2)⁻¹ * (piMod t p 1 : ℝ)) ≤
      (CBT / ((p - 1 : ℕ) : ℝ)) *
        (Real.log (Real.log (Q / p)) - Real.log (Real.log ((((2 * p : ℕ) : ℝ) / p)))) := by
  let a : ℝ := (((2 * p : ℕ) : ℝ))
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ha_nonneg : 0 ≤ a := by positivity
  have ha_pos : 0 < a := by
    dsimp [a]
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 2) hp.pos)
  have ha_gt : (p : ℝ) < a := by
    dsimp [a]
    exact_mod_cast (by nlinarith [hp.pos] : p < 2 * p)
  have hpminus_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hp.one_lt)
  have hg_left_cont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a Q) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht hzero
      have ht_pos : 0 < t := ha_pos.trans_le ht.1
      exact (ne_of_gt ht_pos) (sq_eq_zero_iff.mp hzero)
  have hg_left_int_on : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a Q) :=
    hg_left_cont.integrableOn_Icc
  have hleft_on : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹ * (piMod t p 1 : ℝ)) (Set.Icc a Q) := by
    simpa [apCoeff_sum_eq_piMod] using
      (integrableOn_mul_sum_Icc (c := apCoeff p) (a := a) (b := Q) (m := 0)
        ha_nonneg hg_left_int_on)
  have hleft_int :
      IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹ * (piMod t p 1 : ℝ)) volume a Q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hQ).2 hleft_on
  have hkernel_cont : ContinuousOn (fun t : ℝ => (t * Real.log (t / p))⁻¹) (Set.Icc a Q) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.mul ((Real.continuousOn_log.comp (continuousOn_id.div_const (p : ℝ)))
        (by
          intro t ht
          have ht_pos : 0 < t := ha_pos.trans_le ht.1
          exact div_ne_zero (ne_of_gt ht_pos) (ne_of_gt hp_pos)))
    · intro t ht hzero
      have ht_pos : 0 < t := ha_pos.trans_le ht.1
      have ht_div_ge_two : 2 ≤ t / (p : ℝ) := by
        rw [le_div_iff₀ hp_pos]
        dsimp [a] at ht
        norm_num at ht ⊢
        exact ht.1
      have hlog_pos : 0 < Real.log (t / p) :=
        Real.log_pos (lt_of_lt_of_le (by norm_num) ht_div_ge_two)
      exact mul_ne_zero (ne_of_gt ht_pos) (ne_of_gt hlog_pos) hzero
  have hright_on :
      IntegrableOn (fun t : ℝ => (CBT / ((p - 1 : ℕ) : ℝ)) * (t * Real.log (t / p))⁻¹)
        (Set.Icc a Q) :=
    (continuousOn_const.mul hkernel_cont).integrableOn_Icc
  have hright_int :
      IntervalIntegrable
        (fun t : ℝ => (CBT / ((p - 1 : ℕ) : ℝ)) * (t * Real.log (t / p))⁻¹) volume a Q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hQ).2 hright_on
  rw [← intervalIntegral.integral_of_le hQ]
  have hmono : (∫ t in a..Q, (t ^ 2)⁻¹ * (piMod t p 1 : ℝ)) ≤
      ∫ t in a..Q, (CBT / ((p - 1 : ℕ) : ℝ)) * (t * Real.log (t / p))⁻¹ := by
    apply intervalIntegral.integral_mono_on hQ hleft_int hright_int
    intro t ht
    have ht_ge_a : a ≤ t := ht.1
    have ht_pos : 0 < t := ha_pos.trans_le ht_ge_a
    have hpi := hBT t ht_ge_a
    have ht_div_ge_two : 2 ≤ t / (p : ℝ) := by
      rw [le_div_iff₀ hp_pos]
      dsimp [a] at ht_ge_a
      norm_num at ht_ge_a ⊢
      exact ht_ge_a
    have hlog_pos : 0 < Real.log (t / p) :=
      Real.log_pos (lt_of_lt_of_le (by norm_num) ht_div_ge_two)
    have ht2_pos : 0 < t ^ 2 := sq_pos_of_pos ht_pos
    calc
      (t ^ 2)⁻¹ * (piMod t p 1 : ℝ) ≤
          (t ^ 2)⁻¹ * (CBT * t / (((p - 1 : ℕ) : ℝ) * Real.log (t / p))) := by
        exact mul_le_mul_of_nonneg_left hpi (inv_nonneg.mpr ht2_pos.le)
      _ = (CBT / ((p - 1 : ℕ) : ℝ)) * (t * Real.log (t / p))⁻¹ := by
        field_simp [ne_of_gt ht_pos, ne_of_gt hpminus_pos, ne_of_gt hlog_pos]
  refine hmono.trans_eq ?_
  calc
    (∫ t in a..Q, (CBT / ((p - 1 : ℕ) : ℝ)) * (t * Real.log (t / p))⁻¹)
      = (CBT / ((p - 1 : ℕ) : ℝ)) *
        (Real.log (Real.log (Q / p)) - Real.log (Real.log (a / p))) := by
          rw [intervalIntegral.integral_const_mul]
          rw [integral_inv_mul_log_div hp_pos ha_gt hQ]
    _ = (CBT / ((p - 1 : ℕ) : ℝ)) *
        (Real.log (Real.log (Q / p)) - Real.log (Real.log ((((2 * p : ℕ) : ℝ) / p)))) := by
          rfl

private lemma high_AP_sum_le_explicit {CBT : ℝ} {p : ℕ} {Q : ℝ} (hCBT : 0 < CBT)
    (hp : p.Prime) (hQ : (((2 * p : ℕ) : ℝ)) ≤ Q)
    (hBT : ∀ t : ℝ, (((2 * p : ℕ) : ℝ)) ≤ t →
      (piMod t p 1 : ℝ) ≤ CBT * t / (((p - 1 : ℕ) : ℝ) * Real.log (t / p))) :
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
      CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) +
        (CBT / ((p - 1 : ℕ) : ℝ)) *
          (Real.log (Real.log (Q / p)) -
            Real.log (Real.log ((((2 * p : ℕ) : ℝ) / p)))) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h2p_pos : (0 : ℝ) < (((2 * p : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 2) hp.pos)
  have hQ_pos : 0 < Q := h2p_pos.trans_le hQ
  have hQnonneg : 0 ≤ Q := hQ_pos.le
  have hp1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
  have hBTQ := hBT Q hQ
  have hboundary :
      ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ) ≤
        CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) := by
    have hpminus_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.sub_pos_of_lt hp.one_lt)
    have hQdiv_ge_two : (2 : ℝ) ≤ Q / p := by
      rw [le_div_iff₀ hp_pos]
      norm_num at hQ ⊢
      exact hQ
    have hlog_pos : 0 < Real.log (Q / p) :=
      Real.log_pos (lt_of_lt_of_le (by norm_num) hQdiv_ge_two)
    calc
      ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ) ≤
          (1 / Q) * (CBT * Q / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p))) := by
        exact mul_le_mul_of_nonneg_left hBTQ (by positivity)
      _ = CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) := by
        field_simp [ne_of_gt hQ_pos]
  have hint := tail_integral_le hCBT hp hQ hBT
  calc
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ))
        = ∑ q ∈ Finset.Ioc (2 * p) ⌊Q⌋₊,
          ((1 : ℝ) / (q : ℝ)) * (if q.Prime ∧ q % p = 1 % p then (1 : ℝ) else 0) := by
          simpa using sum_filter_eq_Ioc_indicator (p := p) (N := 2 * p) (Q := Q) hQnonneg hp1
    _ = ∑ q ∈ Finset.Ioc (2 * p) ⌊Q⌋₊, ((1 : ℝ) / (q : ℝ)) * apCoeff p q := by
          rfl
    _ ≤ ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ) +
        ∫ t in Set.Ioc (((2 * p : ℕ) : ℝ)) Q, (t ^ 2)⁻¹ * (piMod t p 1 : ℝ) :=
          high_sum_le_boundary_integral hp hQ
    _ ≤ CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) +
        (CBT / ((p - 1 : ℕ) : ℝ)) *
          (Real.log (Real.log (Q / p)) -
            Real.log (Real.log ((((2 * p : ℕ) : ℝ) / p)))) := by
          nlinarith

private lemma total_AP_sum_le_low_add_high {p : ℕ} {Q : ℝ} :
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
      (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (2 * p : ℝ))
        (Finset.Iic (2 * p)), (1 : ℝ) / (q : ℝ)) +
      (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) := by
  classical
  let s := Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊)
  let slow := Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (2 * p : ℝ))
        (Finset.Iic (2 * p))
  let shigh := Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊)
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun q => q ≤ 2 * p)
    (f := fun q => (1 : ℝ) / (q : ℝ))
  rw [← hsplit]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      simp only [s, Finset.mem_filter, Finset.mem_Iic] at hq ⊢
      exact ⟨hq.2, hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1,
        by exact_mod_cast hq.2⟩
    · intro q hq _hnot
      positivity
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      simp only [s, Finset.mem_filter, Finset.mem_Iic] at hq ⊢
      have hlt : 2 * p < q := Nat.lt_of_not_ge hq.2
      exact ⟨hq.1.1, hq.1.2.1, hq.1.2.2.1, by exact_mod_cast hlt, hq.1.2.2.2.2⟩
    · intro q hq _hnot
      positivity

private lemma explicit_tail_bound {CBT : ℝ} {p : ℕ} (hCBT : 0 < CBT) (hp : p.Prime) :
    let A : ℝ := (p : ℝ) / (Real.log p) ^ 2
    let Q : ℝ := Real.exp (Real.exp A)
    let D : ℝ := |Real.log (Real.log 2)|
    (((2 * p : ℕ) : ℝ)) ≤ Q →
      CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) +
        (CBT / ((p - 1 : ℕ) : ℝ)) *
          (Real.log (Real.log (Q / p)) -
            Real.log (Real.log ((((2 * p : ℕ) : ℝ) / p)))) ≤
      (2 * CBT / Real.log 2 + 2 * CBT * D) * (1 / (p : ℝ)) +
        2 * CBT * (1 / (Real.log p) ^ 2) := by
  intro A Q D hQ
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp_ge : Real.log 2 ≤ Real.log (p : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hlogp_pos : 0 < Real.log (p : ℝ) := lt_of_lt_of_le hlog2_pos hlogp_ge
  have hlogpsq_pos : 0 < (Real.log (p : ℝ)) ^ 2 := sq_pos_of_pos hlogp_pos
  have hpminus_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hp.one_lt)
  have hQ_pos : 0 < Q := by dsimp [Q]; positivity
  have hQdiv_ge_two : (2 : ℝ) ≤ Q / p := by
    rw [le_div_iff₀ hp_pos]
    norm_num at hQ ⊢
    exact hQ
  have hlogQp_ge_log2 : Real.log 2 ≤ Real.log (Q / p) := by
    exact Real.log_le_log (by norm_num) hQdiv_ge_two
  have hterm1 : CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) ≤
      (2 * CBT / Real.log 2) * (1 / (p : ℝ)) := by
    have hLpos : 0 < Real.log (Q / p) := lt_of_lt_of_le hlog2_pos hlogQp_ge_log2
    have hp_le_nat : p ≤ 2 * (p - 1) := by
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have hp_le : (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hp_le_nat
    field_simp [ne_of_gt hp_pos, ne_of_gt hpminus_pos, ne_of_gt hlog2_pos, ne_of_gt hLpos]
    nlinarith [hCBT.le, hp_le, hlogQp_ge_log2]
  have hQdiv_pos : 0 < Q / p := lt_of_lt_of_le (by norm_num) hQdiv_ge_two
  have hp_ge_one : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hQdiv_le_Q : Q / (p : ℝ) ≤ Q := by
    rw [div_le_iff₀ hp_pos]
    nlinarith [mul_le_mul_of_nonneg_left hp_ge_one hQ_pos.le]
  have hlog_le : Real.log (Q / p) ≤ Real.log Q := Real.log_le_log hQdiv_pos hQdiv_le_Q
  have hlogQ : Real.log Q = Real.exp A := by simp [Q]
  have hloglog_le_A : Real.log (Real.log (Q / p)) ≤ A := by
    calc
      Real.log (Real.log (Q / p)) ≤ Real.log (Real.log Q) := by
        exact Real.log_le_log (lt_of_lt_of_le hlog2_pos hlogQp_ge_log2) hlog_le
      _ = A := by simp [hlogQ]
  have h2p_div : (((2 * p : ℕ) : ℝ) / (p : ℝ)) = 2 := by
    rw [show (((2 * p : ℕ) : ℝ)) = 2 * (p : ℝ) by norm_num]
    field_simp [ne_of_gt hp_pos]
  have hB_le : Real.log (Real.log (Q / p)) -
      Real.log (Real.log ((((2 * p : ℕ) : ℝ) / p))) ≤ A + D := by
    rw [h2p_div]
    dsimp [D]
    have hneg_le_abs : -Real.log (Real.log 2) ≤ |Real.log (Real.log 2)| := by
      exact neg_le_abs _
    nlinarith
  have hcoef_nonneg : 0 ≤ CBT / ((p - 1 : ℕ) : ℝ) := div_nonneg hCBT.le hpminus_pos.le
  have hcoef_le : CBT / ((p - 1 : ℕ) : ℝ) ≤ 2 * CBT / (p : ℝ) := by
    have hp_le_nat : p ≤ 2 * (p - 1) := by
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have hp_le : (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hp_le_nat
    field_simp [ne_of_gt hp_pos, ne_of_gt hpminus_pos]
    nlinarith [hCBT.le, hp_le]
  have hAD_nonneg : 0 ≤ A + D := by
    have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
    dsimp [D]
    positivity
  have hterm2 : (CBT / ((p - 1 : ℕ) : ℝ)) *
        (Real.log (Real.log (Q / p)) -
          Real.log (Real.log ((((2 * p : ℕ) : ℝ) / p)))) ≤
      2 * CBT * (1 / (Real.log p) ^ 2) + (2 * CBT * D) * (1 / (p : ℝ)) := by
    calc
      (CBT / ((p - 1 : ℕ) : ℝ)) *
          (Real.log (Real.log (Q / p)) -
            Real.log (Real.log ((((2 * p : ℕ) : ℝ) / p))))
          ≤ (CBT / ((p - 1 : ℕ) : ℝ)) * (A + D) := by
            exact mul_le_mul_of_nonneg_left hB_le hcoef_nonneg
      _ ≤ (2 * CBT / (p : ℝ)) * (A + D) := by
            exact mul_le_mul_of_nonneg_right hcoef_le hAD_nonneg
      _ = 2 * CBT * (1 / (Real.log p) ^ 2) + (2 * CBT * D) * (1 / (p : ℝ)) := by
            dsimp [A]
            field_simp [ne_of_gt hp_pos, ne_of_gt hlogpsq_pos]
  nlinarith [hterm1, hterm2]

private lemma scale_one_div_log {K : ℝ} {p : ℕ} (hK : 0 ≤ K) (hp : p.Prime) :
    K * (1 / (p : ℝ) + 1 / (Real.log p) ^ 2) ≤
      (K / Real.log 2 + K) * (Real.log p / (p : ℝ) + 1 / (Real.log p) ^ 2) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp_ge : Real.log 2 ≤ Real.log (p : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hlogp_pos : 0 < Real.log (p : ℝ) := lt_of_lt_of_le hlog2_pos hlogp_ge
  have hinvlogsq_nonneg : 0 ≤ 1 / (Real.log (p : ℝ)) ^ 2 := by positivity
  have hlogp_div_nonneg : 0 ≤ Real.log (p : ℝ) / (p : ℝ) :=
    div_nonneg hlogp_pos.le hp_pos.le
  have hKdiv_nonneg : 0 ≤ K / Real.log 2 := div_nonneg hK hlog2_pos.le
  have hloginv_coeff : K * (1 / (p : ℝ)) ≤
      (K / Real.log 2) * (Real.log p / (p : ℝ)) := by
    field_simp [ne_of_gt hp_pos, ne_of_gt hlog2_pos]
    nlinarith [mul_le_mul_of_nonneg_left hlogp_ge hK]
  calc
    K * (1 / (p : ℝ) + 1 / (Real.log p) ^ 2)
        = K * (1 / (p : ℝ)) + K * (1 / (Real.log p) ^ 2) := by ring
    _ ≤ (K / Real.log 2) * (Real.log p / (p : ℝ)) + K * (1 / (Real.log p) ^ 2) := by
      exact add_le_add hloginv_coeff le_rfl
    _ ≤ (K / Real.log 2 + K) * (Real.log p / (p : ℝ) + 1 / (Real.log p) ^ 2) := by
      have h_extra1 : 0 ≤ (K / Real.log 2) * (1 / (Real.log p) ^ 2) :=
        mul_nonneg hKdiv_nonneg hinvlogsq_nonneg
      have h_extra2 : 0 ≤ K * (Real.log p / (p : ℝ)) := mul_nonneg hK hlogp_div_nonneg
      nlinarith [h_extra1, h_extra2]

/-- **Paper §4 eq:Sp-bound — exact paper statement.**

For every prime `p ≥ 2`, the bad-prime-pair reciprocal sum
`S(p) := ∑_{p < q ≤ Q(p), q ≡ 1 mod p, q prime} 1/q` satisfies
`S(p) ≤ C · (log p / p + 1/(log p)^2)` for some absolute `C > 0`,
where `Q(p) := exp(exp(p / (log p)^2))`.

Proof: split into ranges `p < q ≤ p²` (trivial bound, paper eq:bad-h-low)
and `p² < q ≤ Q(p)` (Brun–Titchmarsh + partial summation, paper eq:BT-final). -/
theorem bt_reciprocal_AP_tail :
    ∃ C : ℝ, 0 < C ∧
      ∀ p : ℕ, p.Prime → 2 ≤ p →
        (∑ q ∈ Finset.filter
            (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧
              (q : ℝ) ≤ Real.exp (Real.exp ((p : ℝ) / (Real.log p) ^ 2)))
            (Finset.Iic ⌊Real.exp (Real.exp ((p : ℝ) / (Real.log p) ^ 2))⌋₊),
          (1 : ℝ) / (q : ℝ)) ≤
            C * (Real.log p / (p : ℝ) + 1 / (Real.log p) ^ 2) := by
  classical
  rcases brun_titchmarsh with ⟨CBT, hCBT, hBTall⟩
  let D : ℝ := |Real.log (Real.log 2)|
  let K : ℝ := 1 + (2 * CBT / Real.log 2 + 2 * CBT * D) + 2 * CBT
  refine ⟨K / Real.log 2 + K, ?_, ?_⟩
  · have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK_pos : 0 < K := by
      dsimp [K, D]
      positivity
    positivity
  · intro p hp _hp2
    let A : ℝ := (p : ℝ) / (Real.log p) ^ 2
    let Q : ℝ := Real.exp (Real.exp A)
    change
      (∑ q ∈ Finset.filter
          (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
          (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
        (K / Real.log 2 + K) * (Real.log p / (p : ℝ) + 1 / (Real.log p) ^ 2)
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlogp_pos : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast hp.one_lt)
    have hlogterm_nonneg : 0 ≤ 1 / (Real.log (p : ℝ)) ^ 2 := by positivity
    have hinvp_nonneg : 0 ≤ 1 / (p : ℝ) := by positivity
    have hK_nonneg : 0 ≤ K := by
      dsimp [K, D]
      positivity
    have hBTp : ∀ t : ℝ, (((2 * p : ℕ) : ℝ)) ≤ t →
        (piMod t p 1 : ℝ) ≤ CBT * t / (((p - 1 : ℕ) : ℝ) * Real.log (t / p)) := by
      intro t ht
      have ht' : (2 * (p : ℝ)) ≤ t := by
        norm_num at ht ⊢
        exact ht
      simpa [Nat.totient_prime hp] using hBTall p hp.one_le 1 (by simp) t ht'
    have htotal := total_AP_sum_le_low_add_high (p := p) (Q := Q)
    have hlow := low_AP_sum_le_inv hp
    have hscaled : K * (1 / (p : ℝ) + 1 / (Real.log p) ^ 2) ≤
        (K / Real.log 2 + K) * (Real.log p / (p : ℝ) + 1 / (Real.log p) ^ 2) :=
      scale_one_div_log hK_nonneg hp
    by_cases hQ : (((2 * p : ℕ) : ℝ)) ≤ Q
    · have hhigh_exp := high_AP_sum_le_explicit hCBT hp hQ hBTp
      have htail := explicit_tail_bound hCBT hp hQ
      have hhigh_bound :
          (∑ q ∈ Finset.filter
            (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
            (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
            (2 * CBT / Real.log 2 + 2 * CBT * D) * (1 / (p : ℝ)) +
              2 * CBT * (1 / (Real.log p) ^ 2) :=
        hhigh_exp.trans htail
      have hsumK :
          (∑ q ∈ Finset.filter
            (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
            (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
            K * (1 / (p : ℝ) + 1 / (Real.log p) ^ 2) := by
        let B : ℝ := 2 * CBT / Real.log 2 + 2 * CBT * D
        have hpre :
            (∑ q ∈ Finset.filter
              (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
              (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
              (1 + B) * (1 / (p : ℝ)) + 2 * CBT * (1 / (Real.log p) ^ 2) := by
          dsimp [B] at *
          nlinarith [htotal, hlow, hhigh_bound]
        have hB_nonneg : 0 ≤ B := by
          dsimp [B, D]
          positivity
        have htarget :
            (1 + B) * (1 / (p : ℝ)) + 2 * CBT * (1 / (Real.log p) ^ 2) ≤
              K * (1 / (p : ℝ) + 1 / (Real.log p) ^ 2) := by
          have h_extra1 : 0 ≤ (2 * CBT) * (1 / (p : ℝ)) := by positivity
          have h_extra2 : 0 ≤ (1 + B) * (1 / (Real.log p) ^ 2) := by positivity
          dsimp [K, B]
          nlinarith [h_extra1, h_extra2]
        exact hpre.trans htarget
      exact hsumK.trans hscaled
    · have hQlt : Q < (((2 * p : ℕ) : ℝ)) := lt_of_not_ge hQ
      have hQ_pos : 0 < Q := by dsimp [Q]; positivity
      have hhigh_zero :
          (∑ q ∈ Finset.filter
            (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
            (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_Iic] at hq
        have hq_le_Q : (q : ℝ) ≤ Q := (Nat.cast_le.mpr hq.1).trans (Nat.floor_le hQ_pos.le)
        have hlt : (((2 * p : ℕ) : ℝ)) < (q : ℝ) := hq.2.2.2.1
        exact False.elim (by nlinarith)
      have hsumK :
          (∑ q ∈ Finset.filter
            (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
            (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
            K * (1 / (p : ℝ) + 1 / (Real.log p) ^ 2) := by
        have hK_ge_one : 1 ≤ K := by
          have hnonneg : 0 ≤ (2 * CBT / Real.log 2 + 2 * CBT * D) + 2 * CBT := by
            dsimp [D]
            positivity
          dsimp [K, D]
          nlinarith
        rw [hhigh_zero] at htotal
        nlinarith
      exact hsumK.trans hscaled

end Erdos696
