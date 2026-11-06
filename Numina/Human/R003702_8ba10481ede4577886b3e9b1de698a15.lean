import Mathlib

/- A.Y.

Given an increasing infinite sequence of natural numbers $a_{1}, \ldots, a_{n}, \ldots$, where each term is either the arithmetic mean or the geometric mean of its two neighbors. Is it necessarily true that from some point onward, this sequence becomes either an arithmetic or a geometric progression?
 -/

-- we define the sequence that we will use as counter example
def seq (n : ℕ) : ℕ := if Even n then (n / 2 + 2) ^ 2 else (n / 2 + 2) * (n / 2 + 3)

-- the sequence is strictly monotone as for consecutive values they are increasing
lemma l_seq_strictmono : StrictMono seq := by
  apply strictMono_nat_of_lt_succ
  rintro n
  obtain h | h := Nat.even_or_odd n
  . simp [seq, h, Nat.not_even_iff_odd.mpr h.add_one]
    rw [sq]
    apply Nat.mul_lt_mul_of_le_of_lt
    . omega
    . omega
    . omega
  . simp [seq, Nat.not_even_iff_odd.mpr h, h.add_one]
    rw [sq]
    apply Nat.mul_lt_mul_of_lt_of_le
    . obtain ⟨k, hk⟩ := h
      rw [hk]
      omega
    . obtain ⟨k, hk⟩ := h
      rw [hk]
      omega
    . omega

-- for odd n's, n and (n + 2) element's arithmetic average is (n + 1) element
lemma l_seq_odd_arithmean {n : ℕ} (hn : Odd n) : seq n + seq (n + 2) = 2 * seq (n + 1) := by
  simp [seq, Nat.not_even_iff_odd.mpr hn, hn.add_one, Nat.not_even_iff_odd.mpr
    (hn.add_even (show Even 2 by decide))]
  obtain ⟨k, hk⟩ := hn
  rw [hk]
  rw [show (2 * k + 1) / 2 = k by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
  ring

-- for even n's, n and (n + 2) element's geometric average is (n + 1) element
lemma l_seq_even_geommean {n : ℕ} (hn : Even n) : seq n * seq (n + 2) = seq (n + 1) ^ 2 := by
  simp [seq, hn, Nat.not_even_iff_odd.mpr (hn.add_one), hn.add (show Even 2 by decide)]
  obtain ⟨k, hk⟩ := hn
  rw [hk]
  rw [show (k + k) / 2 = k by omega, show (k + k + 1) / 2 = k by omega]
  ring

-- for even n's, n, n + 1, n + 2 are not part of arithmetic sequenece
lemma l_seq_even_not_arith {n : ℕ} (hn : Even n) : (seq (n + 2) : ℤ) - seq (n + 1) ≠ seq (n + 1) - seq n := by
  simp [seq, hn, Nat.not_even_iff_odd.mpr (hn.add_one), hn.add (show Even 2 by decide)]
  obtain ⟨k, hk⟩ := hn
  rw [hk]
  push_cast
  rw [show (k + k : ℤ) / 2 = k by omega, show (k + k + 1 : ℤ) / 2 = k by omega]
  ring_nf
  omega

-- for odd n's, n, n + 1, n + 2 are not part of geometric sequenece
lemma l_seq_odd_not_geom {n : ℕ} (hn : Odd n) : (seq (n + 2) : ℚ) / seq (n + 1) ≠ seq (n + 1) / seq n := by
  simp [seq, Nat.not_even_iff_odd.mpr hn, hn.add_one, Nat.not_even_iff_odd.mpr
    (hn.add_even (show Even 2 by decide))]
  obtain ⟨k, hk⟩ := hn
  rw [hk]
  rw [show (2 * k + 1) / 2 = k by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
  push_cast
  field_simp
  ring_nf
  rintro h
  norm_cast at h
  omega

theorem algebra_208821 : ¬ ∀ (a : ℕ → ℕ), StrictMono a →
    (∀ n, a n + a (n + 2) = 2 * a (n + 1) ∨ (a n * a (n + 2) = a (n + 1) ^ 2)) →
    (∃ N, (∀ n ≥ N, (a (n + 2) : ℤ) - a (n + 1) = a (n + 1) - a n) ∨ (∀ n ≥ N, (a (n + 2) : ℚ) / a (n + 1) = a (n + 1) / a n)) := by
  push_neg
  -- use seq as counterexample
  use seq
  and_intros
  -- seq is strictly monotonic
  . exact l_seq_strictmono
  -- n is even or odd and then elements are arithmetic/geometric mean of adjacents
  . rintro n
    obtain h | h := Nat.even_or_odd n
    . right
      apply l_seq_even_geommean h
    . left
      apply l_seq_odd_arithmean h
  -- for any N, there is 2 * N, 2 * N + 1, 2 * N + 2 or 2 * N + 1, 2 * N + 2, 2 * N + 3 where the triplet are not part of arithmetic or geometric sequence.
  . rintro N
    and_intros
    . use 2 * N
      and_intros
      . omega
      . apply l_seq_even_not_arith
        simp
    . use 2 * N + 1
      and_intros
      . omega
      . apply l_seq_odd_not_geom
        simp