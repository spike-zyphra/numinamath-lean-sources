import Mathlib

theorem number_theory_128852 (n : ℕ) : 7 ∣ 3^(12*n + 1) + 2^(6*n + 2) := by 
  have h1 : ∀ (n : ℕ), 3 ^ (12 * n + 1) % 7 = 3 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ k ih =>
      have h2 : 3 ^ (12 * (k + 1) + 1) % 7 = 3 := by
        have h3 : 3 ^ (12 * (k + 1) + 1) = 3 ^ (12 * k + 1) * 3 ^ 12 := by
          ring_nf
        rw [h3]
        have h4 : 3 ^ (12 * k + 1) % 7 = 3 := ih
        have h5 : 3 ^ 12 % 7 = 1 := by
          norm_num
        norm_num [Nat.mul_mod, h4, h5]
      exact h2
  have h2 : ∀ (n : ℕ), 2 ^ (6 * n + 2) % 7 = 4 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ k ih =>
      have h3 : 2 ^ (6 * (k + 1) + 2) % 7 = 4 := by
        have h4 : 2 ^ (6 * (k + 1) + 2) = 2 ^ (6 * k + 2) * 2 ^ 6 := by
          ring_nf
        rw [h4]
        have h5 : 2 ^ (6 * k + 2) % 7 = 4 := ih
        have h6 : 2 ^ 6 % 7 = 1 := by
          norm_num
        norm_num [Nat.mul_mod, h5, h6]
      exact h3
  have h3 := h1 n
  have h4 := h2 n
  omega