import Mathlib

open Real

theorem algebra_97399 {n : ℕ} (hn : n > 0) (a b c : ℝ)
    (h : a + b + c = n * x) :
    (a + b) / n + c / n = a / n + (b / n) + c / n := by
  have h2 : (n : ℝ) > (0 : ℝ) := by
    exact_mod_cast (show (n : ℕ) > 0 by linarith)
  have eq1 : (a + b) / (n : ℝ) + c / (n : ℝ) = (a + b + c) / (n : ℝ) := by
    field_simp
    <;> ring
  have eq2 : a / (n : ℝ) + (b / (n : ℝ)) + c / (n : ℝ) = (a + b + c) / (n : ℝ) := by
    field_simp
    <;> ring
  rw [eq1, eq2]