import Mathlib

theorem other_148294 (n : ℕ) (h₀ : n ≥ 24) (h₁ : (45 / 100 : ℝ) * n = (26 / 100 : ℝ) * (n - 24)) :
    n = 52 := by
  have h2 : (n : ℝ) ≥ 24 := by
    exact_mod_cast h₀
  have h3 : (n : ℝ) < 0 := by
    nlinarith
  have h4 : (n : ℝ) ≥ 24 := by
    exact_mod_cast h₀
  linarith