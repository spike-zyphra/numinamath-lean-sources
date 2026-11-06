import Mathlib

theorem number_theory_224449 (n : ℕ) (h₀ : n ≠ 0) (h₁ : (96 / 100 : ℝ) * n * (0.5 / 100 : ℝ) = n - (4 / 100 : ℝ) * n) :
    n = 23 := by
  have h2 : (n : ℝ) > 0 := by
    have h3 : (n : ℝ) ≥ 1 := by
      have h4 : n ≥ 1 := by
        have : n > 0 := by
          exact Nat.pos_of_ne_zero h₀
        omega
      exact_mod_cast h4
    linarith
  have h3 : (n : ℝ) = 23 := by
    nlinarith 
  have h4 : n = 23 := by
    exact_mod_cast h3
  exact h4