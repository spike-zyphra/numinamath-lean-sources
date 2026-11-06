import Mathlib

theorem number_theory_286335 (a : ℕ) (ha : Odd a) (n : ℕ) (hn : Even n) :
    a ^ n % 8 = 1 := by
  rcases hn with ⟨m, hm⟩
  have h2 : n = 2 * m := by
    linarith
  rw [h2]
  have h3 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
    have h1 : a % 2 = 1 := by
      rcases ha with ⟨k, hk⟩
      omega
    omega
  have h4 : a ^ 2 % 8 = 1 := by
    rcases h3 with (h | h | h | h)
    · -- a % 8 = 1
      norm_num [Nat.pow_mod, h]
    · -- a % 8 = 3
      norm_num [Nat.pow_mod, h]
    · -- a % 8 = 5
      norm_num [Nat.pow_mod, h]
    · -- a % 8 = 7
      norm_num [Nat.pow_mod, h]
  have h7 : (a ^ (2 * m)) % 8 = 1 := by
    have h8 : a ^ (2 * m) = (a ^ 2) ^ m := by
      rw [← pow_mul]
      all_goals ring
    rw [h8]
    have h9 : ((a ^ 2) ^ m) % 8 = ((a ^ 2) % 8) ^ m % 8 := by
      simp [Nat.pow_mod]
    rw [h9, h4]
    simp [Nat.one_pow]
  exact h7