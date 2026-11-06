import Mathlib

theorem algebra_327764 {a : ℕ → ℝ}
    (ha0 : a 0 = 1) (ha1 : a 1 = 5)
    (han : ∀ n ≥ 2, a n = (2 * (a (n - 1))^2 - 3 * a (n - 1) - 9) / (2 * a (n - 2))) :
    ∀ n, a n = 2^(n + 2) - 3 := by
  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    rw [ha0]
    norm_num
  | succ n =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      have h2 := ih (n) (by linarith)
      have h3 := ih (n + 1) (by linarith)
      have eq1 := han (n + 2) (by linarith)
      simp [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega] at eq1 
      rw [eq1]
      rw [h3]
      rw [h2]
      field_simp [(show (2 : ℝ) ^ (n + 2 : ℕ) - 3 ≠ 0 by
        by_contra h
        have h1 : (2 : ℝ) ^ (n + 2 : ℕ) = 3 := by linarith
        have h4 : (2 : ℕ) ^ (n + 2 : ℕ) = 3 := by
          have h5 : (2 : ℕ) ^ (n + 2 : ℕ) = (3 : ℕ) := by
            exact_mod_cast (show (2 : ℝ) ^ (n + 2 : ℕ) = (3 : ℝ) by linarith)
          exact_mod_cast h5
        have h5 : n + 2 > 0 := by
          omega
        have h6 : (2 : ℕ) ^ (n + 2 : ℕ) ≥ 4 := by
          have : n + 2 ≥ 2 := by
            omega
          have h7 : (2 : ℕ) ^ (n + 2 : ℕ) ≥ (2 : ℕ) ^ 2 := by
            apply Nat.pow_le_pow_of_le_right
            all_goals
              omega
          have h8 : (2 : ℕ) ^ 2 = 4 := by
            norm_num
          have h9 : (2 : ℕ) ^ (n + 2 : ℕ) ≥ (2 : ℕ) ^ 2 := h7
          linarith [h7, h8]
        omega
      )]
      <;> ring_nf <;> norm_num