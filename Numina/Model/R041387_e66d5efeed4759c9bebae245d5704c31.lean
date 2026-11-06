import Mathlib

theorem algebra_279104 {a : ℝ} {n : ℕ} (ha : a > 0) (hn : n > 0) :
    (a > 1 → (a ^ ((1 : ℝ) / n) > 1)) ∧ (a < 1 → (a ^ ((1 : ℝ) / n) < 1)) := by
  constructor
  · -- Assume a > 1, prove a^(1/n) > 1
    intro ha1
    have h1 : a ^ ((1 : ℝ) / n) > 1 := by
      have h2 : (1 : ℝ) / (n : ℝ) > (0 : ℝ) := by
        have hn' : (n : ℝ) > (0 : ℝ) := by
          exact_mod_cast show (n : ℕ) > (0 : ℕ) by exact_mod_cast hn
        positivity
      have h3 : 1 < a := by linarith
      have h4 : ((1 : ℝ) / (n : ℝ) : ℝ) > (0 : ℝ) := h2
      have h5 : a ^ ((1 : ℝ) / (n : ℝ)) > (1 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) := by
        apply Real.rpow_lt_rpow
        all_goals
          try linarith
        all_goals
          try nlinarith
      have h6 : (1 : ℝ) ^ ((1 : ℝ) / (n : ℝ) ) = 1 := by
        simp
      linarith [h5, h6]
    exact h1
  · -- Assume a < 1, prove a^(1/n) < 1
    intro ha2
    have h1 : a ^ ((1 : ℝ) / n) < 1 := by
      have h2 : (1 : ℝ) / (n : ℝ) > (0 : ℝ) := by
        have hn' : (n : ℝ) > (0 : ℝ) := by
          exact_mod_cast show (n : ℕ) > (0 : ℕ) by exact_mod_cast hn
        positivity
      have h3 : a < (1 : ℝ) := by linarith
      have h4 : ((1 : ℝ) / (n : ℝ) : ℝ) > (0 : ℝ) := h2
      have h5 : a ^ ((1 : ℝ) / (n : ℝ) ) < ((1 : ℝ) ) ^ ((1 : ℝ) / (n : ℝ) ) := by
        apply Real.rpow_lt_rpow
        all_goals
          try linarith
        all_goals
          try nlinarith
      have h6 : (1 : ℝ) ^ ((1 : ℝ) / (n : ℝ) ) = 1 := by
        simp
      linarith [h5, h6]
    exact h1