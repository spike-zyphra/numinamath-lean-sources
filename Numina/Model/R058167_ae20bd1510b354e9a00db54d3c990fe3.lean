import Mathlib

theorem number_theory_204704 (n : ℕ) (hn : n ≠ 0) (h : (1 / 3 : ℚ) * n + (45 / 100 : ℚ) * n < (50 / 100 : ℚ) * n) :
    n = 5 := by
  have h1 : (n : ℚ) > 0 := by
    exact_mod_cast show (0 : ℕ) < n by
      have : n > 0 := by
        by_contra h2
        push_neg at h2
        have h2' : n = 0 := by
          omega
        rw [h2'] at hn
        contradiction
      omega
  have h2 : (17 : ℚ) * (n : ℚ) < 0 := by
    linarith
  have h3 : (n : ℚ) > 0 := h1
  have h4 : (n : ℚ) < 0 := by
    nlinarith
  linarith