import Mathlib

theorem algebra_268115 (n : ℕ) (h₀ : n > 0) (h₁ : (13 + (25 / 100 : ℝ) * (n - 20)) / n = 50 / 100) :
    n = 32 := by
  have h2 : (n : ℝ) > 0 := by exact_mod_cast (show (n : ℕ) > 0 by linarith)
  have eq1 : (13 + (25 / 100 : ℝ) * (n - 20 : ℝ)) = (50 / 100 : ℝ) * (n : ℝ) := by
    have h3 : (n : ℝ) > 0 := by exact_mod_cast (show (n : ℕ) > 0 by linarith)
    field_simp at h₁ ⊢
    linarith
  have eq2 : (n : ℝ) = 32 := by
    nlinarith
  have hn : n = 32 := by
    exact_mod_cast eq2
  exact hn