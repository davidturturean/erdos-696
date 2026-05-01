/-
# Manual scratch file for `stage_h_pmodel_failure_prob` (LBL:1374).

NOT in module index. Builds via `lake env lean Erdos696/PmodelManualHelpers.lean`.
Agents do not see it.

## Paper §5.2 lines 1156-1170 — VERBATIM

> Lines 1156-1160: "The construction up to stage j depends only on selected primes
>   lying below the present search interval, whereas every prime in Q_j(p_j) is
>   > exp(exp y_j) > y_j ≥ p_j. Hence, conditional on the past, the selection
>   events for primes in Q_j(p_j) are still **independent Bernoulli events**
>   with probabilities 1/q."
>
> Lines 1162-1170: "P(stage j fails | past) ≤ ∏_{q ∈ Q_j(p_j)} (1 − 1/q) ≤
>   exp(−∑ 1/q) ≤ exp(−B/8)"

The mechanism is **CRT-based independence of selection events for distinct primes**.
The conditional ≤ on line 1162 is in fact equality `=` for the conditional probability
in the residue model — but the paper writes ≤ since after de-conditioning we get an
upper bound.

## Lemmas

`count_avoid_one_prime` — paper line 1162 marginal (one-prime Bernoulli).
   For prime p | M: count{r ∈ [0, M) : p ∤ r} = (M/p) · (p - 1).

`totient_prod_distinct_primes` — for Q distinct primes, totient(∏Q) = ∏(q-1).
   This is the iterated Mathlib `Nat.totient_mul` over coprime moduli; matches
   paper §5.2 line 1158's "independent Bernoulli with probabilities 1/q" formal
   content.

`count_avoid_primes_eq` — paper line 1162-1170 EXACT (no slack).
   For Q distinct primes with ∏Q | M: count{r ∈ [0, M) : ∀ q ∈ Q, q ∤ r} =
   M · ∏(1 − 1/q). When applied with M = primorial(P), Q ⊆ {primes ≤ P},
   this gives the EXACT residue probability ∏(1−1/q), matching paper line 1162.
-/

import Erdos696.LowerBoundLittleH
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Primorial

namespace Erdos696
namespace PmodelScratch

open Real Finset

/-- Multiples of `p` in `[0, M)` (where `p ∣ M`) are exactly `M / p` in number. -/
lemma count_multiples_of_p_in_range {p M : ℕ} (hp_pos : 0 < p) (hp_dvd : p ∣ M) :
    ((Finset.range M).filter (fun r => p ∣ r)).card = M / p := by
  rcases hp_dvd with ⟨k, hk⟩
  subst hk
  have : (Finset.range (p * k)).filter (fun r => p ∣ r) = (Finset.range k).image (· * p) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hr_lt, hp_dvd_r⟩
      rcases hp_dvd_r with ⟨m, rfl⟩
      refine ⟨m, ?_, by ring⟩
      rcases Nat.lt_or_ge m k with h | h
      · exact h
      · exfalso
        have : p * k ≤ p * m := Nat.mul_le_mul_left p h
        omega
    · rintro ⟨m, hm_lt, rfl⟩
      refine ⟨?_, ⟨m, by ring⟩⟩
      have : m * p < k * p := Nat.mul_lt_mul_of_pos_right hm_lt hp_pos
      linarith [Nat.mul_comm k p]
  rw [this]
  rw [Finset.card_image_of_injective _ (fun a b hab => by
    have : a * p = b * p := hab
    exact Nat.eq_of_mul_eq_mul_right hp_pos this)]
  rw [Finset.card_range]
  rw [Nat.mul_div_cancel_left k hp_pos]

/-- **Paper §5.2 line 1162 marginal (one-prime Bernoulli) — EXACT.**

For `p ∣ M`, the count of `r ∈ [0, M)` with `p ∤ r` is exactly `(M/p) · (p − 1)`.
Equivalently `count / M = (p − 1)/p = 1 − 1/p`. -/
lemma count_avoid_one_prime
    {p M : ℕ} (hp_prime : p.Prime) (hp_dvd : p ∣ M) :
    ((Finset.range M).filter (fun r => ¬ (p : ℕ) ∣ r)).card = (M / p) * (p - 1) := by
  classical
  have hp_pos : 0 < p := hp_prime.pos
  have hsplit : ((Finset.range M).filter (fun r => p ∣ r)).card +
                ((Finset.range M).filter (fun r => ¬ p ∣ r)).card = M := by
    have hbase := Finset.card_filter_add_card_filter_not
      (s := Finset.range M) (p := fun r => p ∣ r)
    rw [Finset.card_range] at hbase
    exact hbase
  rw [count_multiples_of_p_in_range hp_pos hp_dvd] at hsplit
  have hcomp : ((Finset.range M).filter (fun r => ¬ p ∣ r)).card = M - M / p := by omega
  rw [hcomp]
  rcases hp_dvd with ⟨k, hk⟩
  subst hk
  rw [Nat.mul_div_cancel_left k hp_pos]
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hp_pos) with ⟨p', rfl⟩
  simp only [Nat.succ_sub_one, Nat.succ_mul, Nat.add_sub_cancel]
  ring

/-- For a Finset of distinct primes, `totient(∏Q) = ∏(q-1)`.
Iterated Mathlib `Nat.totient_mul` over coprime moduli — paper §5.2 line 1158
"independent Bernoulli with probabilities 1/q" in formal content. -/
lemma totient_prod_distinct_primes :
    ∀ {Q : Finset ℕ}, (∀ q ∈ Q, q.Prime) →
      Nat.totient (∏ q ∈ Q, q) = ∏ q ∈ Q, (q - 1) := by
  classical
  intro Q
  induction Q using Finset.induction_on with
  | empty => intro _; simp
  | insert p P hpP ih =>
    intro hQ_prime
    have hp_prime : p.Prime := hQ_prime p (Finset.mem_insert_self p P)
    have hP_prime : ∀ q ∈ P, q.Prime := fun q hq =>
      hQ_prime q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hpP, Finset.prod_insert hpP]
    have hp_cop : p.Coprime (∏ q ∈ P, q) := by
      apply Nat.Coprime.prod_right
      intro q hqP
      have hq_prime : q.Prime := hP_prime q hqP
      have hpq : p ≠ q := fun heq => hpP (heq ▸ hqP)
      exact (Nat.coprime_primes hp_prime hq_prime).mpr hpq
    rw [Nat.totient_mul hp_cop, Nat.totient_prime hp_prime, ih hP_prime]

/-- Per-block coprime count: in any interval `[i*N, (i+1)*N)` of length `N`,
the count of residues coprime to `N` is exactly `totient(N)`.

Wraps Mathlib's `filter_coprime_Ico_eq_totient`. -/
lemma count_coprime_in_block (N i : ℕ) :
    ((Finset.Ico (i * N) ((i + 1) * N)).filter (fun r => N.Coprime r)).card = N.totient := by
  have h_eq : (i + 1) * N = i * N + N := by ring
  rw [h_eq]
  exact Nat.filter_coprime_Ico_eq_totient N (i * N)

/-- **Paper §5.2 line 1162-1170 EXACT (paper-faithful, no slack).**

For a Finset `Q` of distinct primes whose product divides `M` (e.g.
`M = primorial(P)`, `Q ⊆ {primes ≤ P}`), the count of residues in `[0, M)`
avoiding all `q ∈ Q` is EXACTLY `M · ∏(1 − 1/q)`.

This formalises paper line 1162's conditional probability `∏(1−1/q)`
exactly, with no slack. The proof:
- `[0, M) = ⊔_{i ∈ [0, M/N)} [i·N, (i+1)·N)` (where `N = ∏Q`)
- Each block contributes exactly `totient(N)` coprime residues
  (`count_coprime_in_block`)
- Sum: count = `(M/N) · totient(N) = (M/N) · ∏(q−1) = M · ∏(1−1/q)`. -/
lemma count_avoid_primes_eq
    {Q : Finset ℕ} (hQ_prime : ∀ q ∈ Q, q.Prime)
    {M : ℕ} (hMpos : 0 < M)
    (hprodQ_dvd : (∏ q ∈ Q, q) ∣ M) :
    (((Finset.range M).filter (fun r => ∀ q ∈ Q, ¬ q ∣ r)).card : ℝ) =
      (M : ℝ) * ∏ q ∈ Q, (1 - 1 / (q : ℝ)) := by
  classical
  set N : ℕ := ∏ q ∈ Q, q with hN_def
  have hN_pos : 0 < N := Finset.prod_pos (fun q hq => (hQ_prime q hq).pos)
  have hN_ne : N ≠ 0 := hN_pos.ne'
  -- Step 1: ∀ q ∈ Q, q ∤ r ↔ Coprime N r
  have hequiv : ∀ r, (∀ q ∈ Q, ¬ q ∣ r) ↔ Nat.Coprime N r := by
    intro r
    refine ⟨fun h => ?_, fun h q hq h_div => ?_⟩
    · rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      have hgcd_pos : 1 < Nat.gcd N r := by
        have : 0 < Nat.gcd N r := Nat.gcd_pos_of_pos_left _ hN_pos
        omega
      obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hgcd_pos)
      have hp_N : p ∣ N := hp_dvd.trans (Nat.gcd_dvd_left _ _)
      have hp_r : p ∣ r := hp_dvd.trans (Nat.gcd_dvd_right _ _)
      rcases (Prime.dvd_finset_prod_iff hp_prime.prime _).mp hp_N with ⟨q, hq, hpq⟩
      have hq_prime : q.Prime := hQ_prime q hq
      have hpq_eq : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hpq
      exact h q hq (hpq_eq ▸ hp_r)
    · have hqN : q ∣ N := by rw [hN_def]; exact Finset.dvd_prod_of_mem _ hq
      have hq_gcd : q ∣ Nat.gcd N r := Nat.dvd_gcd hqN h_div
      have hq_one : q ∣ 1 := h ▸ hq_gcd
      have := (hQ_prime q hq).one_lt
      exact absurd hq_one (by intro habs; have := Nat.le_of_dvd (by norm_num) habs; omega)
  -- Step 2: rewrite filter
  have hfilter_eq : (Finset.range M).filter (fun r => ∀ q ∈ Q, ¬ q ∣ r) =
                    (Finset.range M).filter (fun r => Nat.Coprime N r) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, hequiv r]
  rw [hfilter_eq]
  -- Step 3: split [0, M) into k = M/N disjoint blocks of length N
  obtain ⟨k, hk⟩ := hprodQ_dvd
  have hk_pos : 0 < k := by
    by_contra hk_zero
    push_neg at hk_zero
    interval_cases k
    rw [hk] at hMpos
    simp at hMpos
  -- Abstract block-count fact: count = k · totient(N) on range(N · k).
  have hblock_count :
      ∀ kk : ℕ, ((Finset.range (N * kk)).filter (fun r => N.Coprime r)).card =
                kk * N.totient := by
    intro kk
    induction kk with
    | zero => simp
    | succ j ih =>
      have hsplit : Finset.range (N * (j + 1)) =
                    Finset.range (N * j) ∪ Finset.Ico (N * j) (N * (j + 1)) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        constructor
        · intro hx
          rcases Nat.lt_or_ge x (N * j) with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h, hx⟩
        · rintro (h | ⟨_, h⟩)
          · have : N * j ≤ N * (j + 1) := Nat.mul_le_mul_left N (Nat.le_succ j)
            linarith
          · exact h
      rw [hsplit]
      have hdisj : Disjoint (Finset.range (N * j)) (Finset.Ico (N * j) (N * (j + 1))) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_range] at hx
        simp only [Finset.mem_Ico] at hx'
        omega
      rw [Finset.filter_union]
      rw [Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
      rw [ih]
      have hblock : (Finset.Ico (N * j) (N * (j + 1))).filter (fun r => N.Coprime r) =
                    (Finset.Ico (j * N) ((j + 1) * N)).filter (fun r => N.Coprime r) := by
        rw [show N * j = j * N from Nat.mul_comm N j,
            show N * (j + 1) = (j + 1) * N from Nat.mul_comm N (j + 1)]
      rw [hblock, count_coprime_in_block]
      ring
  have hcount_nat :
      ((Finset.range M).filter (fun r => Nat.Coprime N r)).card = k * N.totient := by
    rw [hk]
    exact hblock_count k
  -- Step 4: rewrite count via hcount_nat, then unpack to real form
  have hcount_real : (((Finset.range M).filter (fun r => Nat.Coprime N r)).card : ℝ) =
                     (k : ℝ) * (N.totient : ℝ) := by
    rw [show (k : ℝ) * (N.totient : ℝ) = ((k * N.totient : ℕ) : ℝ) by push_cast; ring]
    exact_mod_cast hcount_nat
  rw [hcount_real]
  -- Goal: (k : ℝ) * (N.totient : ℝ) = (M : ℝ) * ∏(1 - 1/q)
  rw [show N.totient = ∏ q ∈ Q, (q - 1) from totient_prod_distinct_primes hQ_prime]
  rw [show ((∏ q ∈ Q, (q - 1) : ℕ) : ℝ) = ∏ q ∈ Q, ((q : ℝ) - 1) from by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun q hq => ?_
    have hq_prime := hQ_prime q hq
    rw [Nat.cast_sub (hq_prime.pos : 1 ≤ q)]
    push_cast; ring]
  rw [show (∏ q ∈ Q, ((q : ℝ) - 1)) = (N : ℝ) * ∏ q ∈ Q, (1 - 1 / (q : ℝ)) from by
    rw [hN_def, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q hq => ?_
    have hq_prime := hQ_prime q hq
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq_prime.pos
    field_simp]
  -- Goal: (k : ℝ) * ((N : ℝ) * ∏(1-1/q)) = (M : ℝ) * ∏(1-1/q)
  -- Use M = N * k
  rw [hk]
  push_cast
  ring

end PmodelScratch
end Erdos696
