/-
# Fundamental definitions for Erdős Problem #696.

Mirrors §1 and §2 of `erdos_696_paper.tex`.

Definitions provided:

* `Erdos696.IsPrimeChain`        — predicate on a list of primes
                                    `p₁ < ⋯ < pₗ` with `p_{i+1} ≡ 1 (mod p_i)`.
* `Erdos696.IsDivisorChain`      — analogous predicate for divisors.
* `Erdos696.hChain n`            — Erdős's `h(n)` function.
* `Erdos696.HChain n`            — Erdős's `H(n)` function.
* `Erdos696.iteratedLog k x`     — `log^{(k)}(x)` (k-fold natural logarithm).
* `Erdos696.logStar x`           — `log_*(x) = min{k ≥ 0 : log^{(k)}(x) ≤ e}`.
* `Erdos696.tower m`             — `T_m`, the iterated tower
                                    (`T_0 = e`, `T_{m+1} = exp T_m`).
* `Erdos696.Um m`                — `U_m := T_m^3`.
* `Erdos696.almostAll P`         — density-one predicate
                                    `#{n ≤ x : ¬P(n)} = o(x)`.
-/

import Mathlib

namespace Erdos696

open scoped BigOperators
open Real

/-! ### Prime and divisor chains -/

/-- A list of natural numbers `p₁, …, pₗ` is a *prime chain dividing `n`*
if all entries are primes that divide `n`, the list is strictly
increasing, and consecutive entries satisfy `p_{i+1} ≡ 1 (mod p_i)`.

This is the predicate underlying `hChain n` in §1 of the paper. -/
def IsPrimeChain (n : ℕ) (ps : List ℕ) : Prop :=
  (∀ p ∈ ps, p.Prime ∧ p ∣ n) ∧
  ps.Pairwise (· < ·) ∧
  (∀ i : Fin ps.length, ∀ hi : i.val + 1 < ps.length,
      ps.get ⟨i.val + 1, hi⟩ % ps.get i = 1)

/-- A list of natural numbers `d₁, …, dᵤ` is a *divisor chain of `n`* if
every entry divides `n`, the list is strictly increasing, every entry is
at least 1, and consecutive entries satisfy `d_{i+1} ≡ 1 (mod d_i)`.

This is the predicate underlying `HChain n` in §1 of the paper.

We use `Nat.ModEq` (which checks `e % d = 1 % d`) rather than the raw
`e % d = 1`.  These agree when `d ≥ 2` (so the prime-chain definition
is unaffected), but for `d = 1` the paper's vacuous-modulo-1 convention
requires the `ModEq` form: `e ≡ 1 [MOD 1]` is true (everything is congruent
mod 1), while `e % 1 = 1` is false (since `e % 1 = 0`).  Paper §7 (line 1891)
constructs lower-bound chains starting with `d_1 = 1`. -/
def IsDivisorChain (n : ℕ) (ds : List ℕ) : Prop :=
  (∀ d ∈ ds, 1 ≤ d ∧ d ∣ n) ∧
  ds.Pairwise (· < ·) ∧
  (∀ i : Fin ds.length, ∀ hi : i.val + 1 < ds.length,
      Nat.ModEq (ds.get i) (ds.get ⟨i.val + 1, hi⟩) 1)

/-- `h(n)` of the paper: the largest length of a prime chain dividing `n`,
with `hChain 1 = 0` by convention. -/
noncomputable def hChain (n : ℕ) : ℕ :=
  sSup {ℓ | ∃ ps : List ℕ, IsPrimeChain n ps ∧ ps.length = ℓ}

/-- `H(n)` of the paper: the largest length of a divisor chain of `n`,
with `HChain 1 = 0` by paper convention (paper line 88).

Without the `n = 1` special case the singleton chain `[1]` would give
`sSup … = 1`, so we hard-code the paper convention. -/
noncomputable def HChain (n : ℕ) : ℕ :=
  if n = 1 then 0
  else sSup {u | ∃ ds : List ℕ, IsDivisorChain n ds ∧ ds.length = u}

/-! ### Iterated logarithms and the tower -/

/-- The `k`-fold natural logarithm `log^{(k)}(x)`. -/
noncomputable def iteratedLog : ℕ → ℝ → ℝ
  | 0,     x => x
  | k+1,   x => Real.log (iteratedLog k x)

/-- `log_* x = min{k ≥ 0 : log^{(k)} x ≤ e}`.

Defined classically.  We use `Classical.propDecidable` to get a
`Decidable` instance for the existence statement, then use `Nat.find`
to extract the minimum.  If no such `k` exists (e.g. for `x = 0`) we
fall back to `0` for definability; since the iterated logarithm
eventually drops below `e` for any `x ≥ 1`, this fallback is irrelevant
for the regime of interest. -/
noncomputable def logStar (x : ℝ) : ℕ := by
  classical
  exact
    if h : ∃ k : ℕ, iteratedLog k x ≤ Real.exp 1 then Nat.find h else 0

/-- The tower `T_m` of base-`e` exponentials: `T₀ = e`, `T_{m+1} = exp T_m`.
Mirrors equation (2.3) of the paper. -/
noncomputable def tower : ℕ → ℝ
  | 0   => Real.exp 1
  | m+1 => Real.exp (tower m)

/-- The auxiliary scale `U_m := T_m^3` of equation (2.5). -/
noncomputable def Um (m : ℕ) : ℝ := (tower m) ^ 3

/-! ### Almost-all (density-one) predicate -/

/-- A property `P` holds *for almost all `n`* (equivalently, with density one)
if `#{n ≤ x : ¬P(n)} = o(x)` as `x → ∞`.

This is equation (2.2) of the paper.  We express it as a `Filter.Tendsto`
statement in the `Filter.atTop` sense on real `x`. -/
def almostAll (P : ℕ → Prop) : Prop :=
  Filter.Tendsto
    (fun x : ℝ => ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} : ℕ) : ℝ) / x)
    Filter.atTop (nhds 0)

/-! ### Trivial monotonicity lemma -/

/-- Every prime chain dividing `n` is also a divisor chain (with the chain
length unchanged), so `hChain n ≤ HChain n`. -/
lemma hChain_le_HChain (n : ℕ) : hChain n ≤ HChain n := by
  classical
  have prime_to_divisor :
      ∀ {m : ℕ} {ps : List ℕ}, IsPrimeChain m ps → IsDivisorChain m ps := by
    intro m ps hps
    rcases hps with ⟨hprime, hpair, hmod⟩
    refine ⟨fun d hd => ⟨(hprime d hd).1.one_le, (hprime d hd).2⟩, hpair, ?_⟩
    intro i hi
    -- IsPrimeChain has `% = 1` form; IsDivisorChain has `Nat.ModEq` form.
    -- For primes p ≥ 2, `1 % p = 1`, so the two forms agree.
    have hp_mem : ps.get i ∈ ps := List.get_mem _ i
    have hp_one_lt : 1 < ps.get i := (hprime _ hp_mem).1.one_lt
    show ps.get ⟨i.val + 1, hi⟩ % ps.get i = 1 % ps.get i
    rw [Nat.mod_eq_of_lt hp_one_lt]
    exact hmod i hi
  by_cases hn : n = 0
  · subst n
    have prime_chain_len0 :
        ∀ m : ℕ, ∃ ps : List ℕ, IsPrimeChain 0 ps ∧ ps.length = m := by
      let next : ℕ → ℕ := fun p =>
        if hp0 : p = 0 then 2 else Classical.choose (Nat.exists_prime_gt_modEq_one p hp0)
      have next_spec :
          ∀ {p : ℕ}, p.Prime → (next p).Prime ∧ p < next p ∧ next p % p = 1 := by
        intro p hp
        have hp0 : p ≠ 0 := hp.ne_zero
        dsimp [next]
        rw [dif_neg hp0]
        rcases Classical.choose_spec (Nat.exists_prime_gt_modEq_one p hp0) with
          ⟨hq, hpq, hmod⟩
        exact ⟨hq, hpq, by simpa [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using hmod⟩
      let a : ℕ → ℕ := fun k => Nat.rec 2 (fun _ prev => next prev) k
      have a_succ : ∀ k : ℕ, a (k + 1) = next (a k) := by
        intro k
        rfl
      have a_prime : ∀ k : ℕ, (a k).Prime := by
        intro k
        induction k with
        | zero => norm_num [a]
        | succ k ih =>
            rw [a_succ]
            exact (next_spec ih).1
      have a_step : ∀ k : ℕ, a k < a (k + 1) := by
        intro k
        rw [a_succ]
        exact (next_spec (a_prime k)).2.1
      have a_strict : StrictMono a := strictMono_nat_of_lt_succ a_step
      have a_mod : ∀ k : ℕ, a (k + 1) % a k = 1 := by
        intro k
        rw [a_succ]
        exact (next_spec (a_prime k)).2.2
      intro m
      let ps : List ℕ := List.ofFn (fun i : Fin m => a i)
      refine ⟨ps, ?_, by simp [ps]⟩
      constructor
      · intro p hp
        simp [ps, List.mem_ofFn] at hp
        rcases hp with ⟨i, rfl⟩
        exact ⟨a_prime i, dvd_zero _⟩
      constructor
      · simp [ps, List.pairwise_ofFn]
        intro i j hij
        exact a_strict hij
      · intro i hi
        simp [ps, a_mod]
    have hPrimeUnbdd :
        ¬BddAbove {ℓ | ∃ ps : List ℕ, IsPrimeChain 0 ps ∧ ps.length = ℓ} := by
      rintro ⟨B, hB⟩
      rcases prime_chain_len0 (B + 1) with ⟨ps, hps, hlen⟩
      have : B + 1 ≤ B := hB ⟨ps, hps, hlen⟩
      omega
    have hDivUnbdd :
        ¬BddAbove {u | ∃ ds : List ℕ, IsDivisorChain 0 ds ∧ ds.length = u} := by
      rintro ⟨B, hB⟩
      rcases prime_chain_len0 (B + 1) with ⟨ps, hps, hlen⟩
      have : B + 1 ≤ B := hB ⟨ps, prime_to_divisor hps, hlen⟩
      omega
    rw [hChain, HChain, Nat.sSup_of_not_bddAbove hPrimeUnbdd,
      if_neg (by decide : (0 : ℕ) ≠ 1), Nat.sSup_of_not_bddAbove hDivUnbdd]
  · have hlen_le : ∀ {ds : List ℕ}, IsDivisorChain n ds → ds.length ≤ n := by
      intro ds hds
      rcases hds with ⟨hdiv, hpair, _hmod⟩
      have hnodup : ds.Nodup := hpair.nodup
      rw [← List.toFinset_card_of_nodup hnodup]
      have hsub : ds.toFinset ⊆ Finset.Icc 1 n := by
        intro d hd
        rw [List.mem_toFinset] at hd
        simpa [Finset.mem_Icc] using
          (show 1 ≤ d ∧ d ≤ n from
            ⟨(hdiv d hd).1, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (hdiv d hd).2⟩)
      exact (Finset.card_le_card hsub).trans (by simp)
    have hDivBdd :
        BddAbove {u | ∃ ds : List ℕ, IsDivisorChain n ds ∧ ds.length = u} := by
      refine ⟨n, ?_⟩
      intro u hu
      rcases hu with ⟨ds, hds, rfl⟩
      exact hlen_le hds
    -- Case-split on n = 1.  For n = 1, both hChain 1 and HChain 1 are 0:
    -- hChain 1 = 0 because no primes divide 1; HChain 1 = 0 by paper convention.
    by_cases hn1 : n = 1
    · subst hn1
      have hPrime1_empty : ∀ {ps : List ℕ}, IsPrimeChain 1 ps → ps = [] := by
        intro ps hps
        rcases hps with ⟨hprime, _, _⟩
        cases ps with
        | nil => rfl
        | cons p _ =>
          exfalso
          have hp_dvd_1 := (hprime p (by simp)).2
          have hp_eq_1 : p = 1 := Nat.eq_one_of_dvd_one hp_dvd_1
          have hp_prime := (hprime p (by simp)).1
          exact hp_prime.one_lt.ne' hp_eq_1
      have hSetEq : {ℓ : ℕ | ∃ ps, IsPrimeChain 1 ps ∧ ps.length = ℓ} = {0} := by
        ext ℓ
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨ps, hps, rfl⟩
          rw [hPrime1_empty hps]; rfl
        · rintro rfl
          refine ⟨[], ⟨fun _ => by simp, by simp, ?_⟩, rfl⟩
          intro i _; exact i.elim0
      show hChain 1 ≤ HChain 1
      rw [hChain, HChain, hSetEq, csSup_singleton, if_pos rfl]
    · -- n ≥ 2: HChain unfolds to sSup directly via `if_neg hn1`.
      show hChain n ≤ HChain n
      rw [hChain, HChain, if_neg hn1]
      refine csSup_le_csSup' hDivBdd ?_
      intro ℓ hℓ
      rcases hℓ with ⟨ps, hps, rfl⟩
      exact ⟨ps, prime_to_divisor hps, rfl⟩

/-! ### `almostAll` helpers (moved here from Main.lean to break import cycles) -/

/-- `almostAll` is monotone under pointwise implication. -/
lemma almostAll_mono {P Q : ℕ → Prop} (hP : almostAll P) (hPQ : ∀ n, P n → Q n) :
    almostAll Q := by
  classical
  unfold almostAll at hP ⊢
  refine squeeze_zero' ?_ ?_ hP
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hsub : {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ Q n} ⊆ {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} := by
      intro n hn
      exact ⟨hn.1, fun hp => hn.2 (hPQ n hp)⟩
    have hfinite : Set.Finite {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} := by
      exact (Set.finite_Iic ⌊x⌋₊).subset (by
        intro n hn
        exact hn.1)
    have hcard := Nat.card_mono hfinite hsub
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hx.le

/-- The intersection of two density-one properties is density-one. -/
lemma almostAll_and {P Q : ℕ → Prop} (hP : almostAll P) (hQ : almostAll Q) :
    almostAll (fun n => P n ∧ Q n) := by
  classical
  unfold almostAll at hP hQ ⊢
  have hsum : Filter.Tendsto
      (fun x : ℝ => ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} : ℕ) : ℝ) / x +
        ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ Q n} : ℕ) : ℝ) / x)
      Filter.atTop (nhds 0) := by
    simpa using hP.add hQ
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    let sA : Set ℕ := {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ (P n ∧ Q n)}
    let sP : Set ℕ := {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n}
    let sQ : Set ℕ := {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ Q n}
    have hsub : sA ⊆ sP ∪ sQ := by
      intro n hn
      dsimp [sA] at hn
      by_cases hp : P n
      · exact Or.inr ⟨hn.1, fun hq => hn.2 ⟨hp, hq⟩⟩
      · exact Or.inl ⟨hn.1, hp⟩
    have hfiniteP : Set.Finite sP := by
      exact (Set.finite_Iic ⌊x⌋₊).subset (by
        intro n hn
        exact hn.1)
    have hfiniteQ : Set.Finite sQ := by
      exact (Set.finite_Iic ⌊x⌋₊).subset (by
        intro n hn
        exact hn.1)
    have hfiniteU : Set.Finite (sP ∪ sQ) := hfiniteP.union hfiniteQ
    have hcard1 : Nat.card sA ≤ Nat.card ↑(sP ∪ sQ) := Nat.card_mono hfiniteU hsub
    have hcard2 : Nat.card ↑(sP ∪ sQ) ≤ Nat.card sP + Nat.card sQ :=
      Set.card_union_le sP sQ
    have hcard : Nat.card sA ≤ Nat.card sP + Nat.card sQ := hcard1.trans hcard2
    calc
      ((Nat.card sA : ℕ) : ℝ) / x ≤ ((Nat.card sP + Nat.card sQ : ℕ) : ℝ) / x := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hx.le
      _ = ((Nat.card sP : ℕ) : ℝ) / x + ((Nat.card sQ : ℕ) : ℝ) / x := by
        rw [Nat.cast_add, add_div]

end Erdos696
