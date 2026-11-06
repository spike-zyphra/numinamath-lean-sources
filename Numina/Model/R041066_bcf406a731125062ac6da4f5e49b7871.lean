import Mathlib

theorem number_theory_605058 : ∃ a : ℕ → ℕ, (0 < a 0) ∧ (∀ n, a (n + 1) = 5 * a n + 4) ∧ 2013 ∣ a 54 := by
  use fun n => (1534 * 5 ^ n - 1 : ℕ)
  constructor
  · -- Show a 0 > 0
    norm_num
  constructor
  · -- Show the recurrence relation
    intro n
    have eq1 : (1534 * 5 ^ (n + 1) - 1 : ℕ) = 5 * ((1534 * 5 ^ n - 1 : ℕ) ) + 4 := by
      have h1 : (1534 * 5 ^ (n + 1) : ℕ) = 5 * (1534 * 5 ^ n) := by ring
      have h2 : (1534 * 5 ^ n : ℕ) ≥ 1 := by
        have h4 : 5 ^ n ≥ 1 := by
          apply Nat.one_le_pow
          all_goals omega
        nlinarith
      have eq2 : (1534 * 5 ^ (n + 1) - 1 : ℕ) = 5 * (1534 * 5 ^ n) - 1 := by
        rw [show (1534 * 5 ^ (n + 1) - 1 : ℕ) = (1534 * 5 ^ (n + 1) : ℕ) - 1 by omega]
        rw [h1]
      have eq3 : 5 * ((1534 * 5 ^ n - 1 : ℕ) ) + 4 = 5 * (1534 * 5 ^ n) - 1 := by
        have h20 : (1534 * 5 ^ n : ℕ) ≥ 1 := h2
        omega
      omega
    simpa using eq1
  · -- Show divisibility
    norm_num