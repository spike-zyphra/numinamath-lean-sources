import Mathlib

theorem algebra_11333 {y : ℕ → ℝ} (hy : ∀ n, y n = if n < 16 then 10 * n - 80 else 80) :
    ∀ n, y n = if n < 16 then 10 * n - 80 else 80 := by 
  intro n 
  exact hy n