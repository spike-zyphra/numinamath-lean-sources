import Mathlib

theorem inequalities_50396 (n : ℕ) (hn : n ≥ 2) (x : ℝ) (hx : |x| < 1) :
    (1 - x)^n + (1 + x)^n < 2^n := by
  have h1 : -1 < x := by
    cases' abs_lt.mp hx with h2 h3
    linarith
  have h2 : x < 1 := by
    cases' abs_lt.mp hx with h3 h4
    linarith
  have h3 : (1 - x) > 0 := by
    linarith
  have h4 : (1 + x) > 0 := by 
    linarith
  have h5 : ∀ (n : ℕ), n ≥ 2 → (1 - x) ^ n + (1 + x) ^ n < (2 : ℝ) ^ n := by
    intro n hn
    have base2 : (1 - x) ^ 2 + (1 + x) ^ 2 < (2 : ℝ) ^ 2 := by
      have h6 : (1 - x) ^ 2 + (1 + x) ^ 2 = 2 * (1 + x ^ 2) := by
        nlinarith
      rw [h6]
      nlinarith [sq_pos_of_pos (show 0 < (1 - x : ℝ) by linarith), sq_pos_of_pos (show 0 < (1 + x : ℝ) by linarith), sq_pos_of_pos (show 0 < (1 : ℝ) by linarith)]
    have step : ∀ (k : ℕ), k ≥ 2 → (1 - x) ^ k + (1 + x) ^ k < (2 : ℝ) ^ k → (1 - x) ^ (k + 1) + (1 + x) ^ (k + 1) < (2 : ℝ) ^ (k + 1) := by 
      intro k hk h
      have eq1 : (1 - x) ^ (k + 1) + (1 + x) ^ (k + 1) = (1 - x) * (1 - x) ^ k + (1 + x) * (1 + x) ^ k := by
        ring
      rw [eq1]
      have h6 : (1 - x) * (1 - x) ^ k + (1 + x) * (1 + x) ^ k < (2 : ℝ) ^ k * 2 := by
        nlinarith [h, mul_pos (show (0 : ℝ) < 1 - x by linarith) (show (0 : ℝ) < 1 + x by linarith), 
          sq_nonneg ((1 - x) ^ k - (1 + x) ^ k), 
          sq_nonneg ((1 - x) * (1 + x)), 
          sq_nonneg (x), 
          pow_pos (show (0 : ℝ) < 1 - x by linarith) k, 
          pow_pos (show (0 : ℝ) < 1 + x by linarith) k, 
          mul_pos (show (0 : ℝ) < 1 - x by linarith) (show (0 : ℝ) < 1 + x by linarith)
        ]
      have h7 : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by 
        ring
      rw [h7]
      linarith
    exact Nat.le_induction base2 step n hn
  specialize h5 n hn
  simpa using h5