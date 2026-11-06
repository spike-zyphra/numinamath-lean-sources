import Mathlib

theorem algebra_206626 {n : ℕ} (hn : n > 0) (h : Nat.factorial 5 * Nat.factorial 9 = 12 * Nat.factorial n) :
    n = 10 := by
  have h1 : n ≤ 10 := by
    by_contra h2
    push_neg at h2
    have h2' : n ≥ 11 := by omega
    have h3 : Nat.factorial n ≥ Nat.factorial 11 := by
      apply Nat.factorial_le
      linarith
    have h4 : Nat.factorial 5 * Nat.factorial 9 < 12 * Nat.factorial 11 := by
      norm_num [Nat.factorial]
    have h5 : 12 * Nat.factorial 11 ≤ 12 * Nat.factorial n := by
      have h6 : Nat.factorial 11 ≤ Nat.factorial n := h3
      nlinarith
    have h6 : Nat.factorial 5 * Nat.factorial 9 ≥ 12 * Nat.factorial 11 := by
      linarith [h, h5]
    linarith [h4, h6]
  have h2 : n ≥ 10 := by
    by_contra h2
    push_neg at h2
    have h2' : n ≤ 9 := by omega
    have h3 : Nat.factorial n ≤ Nat.factorial 9 := by
      apply Nat.factorial_le
      linarith
    have h4 : Nat.factorial 5 * Nat.factorial 9 > 12 * Nat.factorial 9 := by
      norm_num [Nat.factorial]
    have h5 : 12 * Nat.factorial n ≤ 12 * Nat.factorial 9 := by
      have h6 : Nat.factorial n ≤ Nat.factorial 9 := h3
      nlinarith
    have h6 : Nat.factorial 5 * Nat.factorial 9 ≤ 12 * Nat.factorial 9 := by
      linarith [h, h5]
    linarith [h4, h6]
  have h3 : n = 10 := by
    omega
  exact h3