import Mathlib

open Nat

/- Let $K$ be a positive integer. If the number $10^K - 9$ is written as an integer in standard decimal form, determine the sum of its digits. Show that the sum of the digits is $9(K-1) + 1$.-/
theorem number_theory_637831 (K : ℕ) (hK : K > 0) :
  (Nat.digits 10 (10 ^ K - 9)).sum = 9 * (K - 1) + 1 := by 
  have h1 : ∀ n, n > 0 → (Nat.digits 10 (10 ^ n - 1)).sum = 9 * n := by 
    intro n hn
    induction' n with n ih ih2
    · simp
    · by_cases hn0 : n = 0 
      · simp [hn0]
      have npos : n > 0 := by omega
      have eq1 : (10 ^ (n + 1) - 1) = 9 + 10 * (10 ^ (n) - 1) := by 
        zify
        repeat rw [Nat.cast_sub]
        norm_num
        ring
        exact one_le_pow' n 9
        exact one_le_pow' (n + 1) 9
      rw [eq1, Nat.digits_add]
      simp
      rw [ih npos]
      ring
      linarith
      linarith
      left
      linarith
  induction' hK with d hd1 hd2
  · simp
  · simp at hd1 ⊢ 
    have eq1 : (10 ^ (d + 1) - 9) = 1 + 10 * (10 ^ d - 1) := by
      rw [pow_add]
      simp
      zify
      repeat rw [Nat.cast_sub]
      ring_nf
      norm_num
      exact one_le_pow' d 9
      have aux : 10 ^ d ≥ 1 := by 
        exact one_le_pow' d 9
      linarith
    rw [eq1, digits_add]
    simp
    rw [h1]
    ring
    linarith
    linarith
    linarith
    left
    norm_num