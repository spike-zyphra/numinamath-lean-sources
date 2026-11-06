import Mathlib

theorem algebra_182579 (n : ℕ) (h₀ : n ≤ 70) (h₁ : (n - 3) * (1 - 52 / 100 : ℝ) = n * (1 / 2 : ℝ)) :
    n = 25 := by
  have h2 : (n : ℝ) ≤ (70 : ℝ) := by exact_mod_cast h₀
  have eq1 : (n : ℝ) = -72 := by
    norm_num at h₁
    nlinarith
  have h3 : (n : ℝ) ≥ 0 := by
    exact_mod_cast (show (0 : ℕ) ≤ n by linarith)
  nlinarith