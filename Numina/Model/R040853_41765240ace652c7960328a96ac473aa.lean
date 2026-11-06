import Mathlib

open Finset

lemma lemma_1 (n : ℕ) :
    ∏ i ∈ range (n + 1), (2 ^ (2 ^ i) + 1) = 2 ^ (2 ^ (n + 1)) - 1 := by
  have h1 : ∀ (n : ℕ), ∏ i ∈ range (n + 1), (2 ^ (2 ^ i) + 1) = 2 ^ (2 ^ (n + 1)) - 1 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [prod_range_succ, ih]
      have h2 : (2 ^ (2 ^ (n + 1)) - 1 : ℕ) * (2 ^ (2 ^ (n + 1)) + 1) = (2 ^ (2 ^ (n + 2)) - 1 : ℕ) := by
        have h3 : 2 ^ (2 ^ (n + 2)) = (2 ^ (2 ^ (n + 1)) ) ^ 2 := by
          ring_nf
        rw [h3]
        have h4 : ((2 ^ (2 ^ (n + 1)) : ℕ) - 1) * ((2 ^ (2 ^ (n + 1)) : ℕ) + 1) = (2 ^ (2 ^ (n + 1)) : ℕ) ^ 2 - 1 := by
          cases (2 ^ (2 ^ (n + 1)) : ℕ) with
          | zero =>
            all_goals omega
          | succ m =>
            simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm]
            all_goals ring_nf
            all_goals omega
        nlinarith
      nlinarith [h2]
  specialize h1 n
  simpa using h1


theorem algebra_251130 {n : ℕ} :
    ∏ i ∈ range (n + 1), (2 ^ (2 ^ i) + 1) = 4 ^ (2 ^ n) - 1 := by
  have h3 : ∏ i ∈ range (n + 1), (2 ^ (2 ^ i) + 1) = 2 ^ (2 ^ (n + 1)) - 1 := lemma_1 n
  rw [h3]
  have h4 : 2 ^ (2 ^ (n + 1)) = 4 ^ (2 ^ n) := by
    have h5 : 4 ^ (2 ^ n) = (2 ^ 2) ^ (2 ^ n) := by
      ring_nf
    rw [h5]
    have h6 : (2 ^ 2) ^ (2 ^ n) = 2 ^ (2 * (2 ^ n)) := by
      rw [← pow_mul]
    rw [h6]
    have h7 : 2 * (2 ^ n) = 2 ^ (n + 1 : ℕ) := by
      ring_nf
    rw [h7]
  rw [h4]