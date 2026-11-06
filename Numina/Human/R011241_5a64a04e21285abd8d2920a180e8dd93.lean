import Mathlib

-- we show a simple lemma which will be used in the proof
lemma lemma_1 (m n: ℕ) (h1: 0 < n) (h2: n < m) (h3: Nat.Prime (m * n)): n = 1 := by
    rw [Nat.prime_mul_iff] at h3
    rcases h3 with h | h
    .
      omega
    .
      have o: n = 0 := by omega
      simp [o] at h
      norm_num at h

/-You are asked to choose two positive integers,
m n and with m>n, so that as many as possible of the expressions
m+n,m−n,m×n and m÷n have values that are prime.
When you do this correctly, how many of these four expressions have values that are prime?
A 0 B 1 C 2 D 3 E 4-/

theorem number_theory_231716: (¬ ∃ m n: ℕ, 0 < n ∧ n < m ∧ Nat.Prime (m + n) ∧ Nat.Prime (m - n) ∧
Nat.Prime (m * n) ∧ Nat.Prime (m / n)) ∧
  ∃ m n: ℕ, 0 < n ∧ n < m ∧ Nat.Prime (m + n) ∧ Nat.Prime (m * n) ∧ Nat.Prime (m / n) := by

  constructor

  -- the first part of the theorem
  .
    by_contra! h
    obtain ⟨m, n, h1, h2, h3, h4, h5, h6⟩ := h
    have i:= lemma_1 m n h1 h2 h5
    simp [i] at *
    have s: m ≠ 2 := by
      by_contra! s
      simp [s] at h4
      norm_num at h4
    have j: Odd m := by
      apply Nat.Prime.odd_of_ne_two
      exact h5
      exact s
    apply Nat.Prime.odd_of_ne_two at h3
    have ne: m + 1 ≠ 2 := by omega
    simp [ne] at h3
    rw [Nat.odd_add_one] at h3
    trivial

  -- the second part of the theorem
  .
    use 2, 1
    norm_num
    