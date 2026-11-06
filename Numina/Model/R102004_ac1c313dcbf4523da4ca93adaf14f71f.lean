import Mathlib

theorem inequalities_50648 (a b x : ℝ)
    (h₁ : abs (a + x + b) ≤ 1) (h₂ : abs (4 * a + 2 * x + b) ≤ 1) (h₃ : abs (9 * a + 6 * x + 4 * b) ≤ 1) :
    abs x ≤ 15 := by
  have h1a : -1 ≤ a + x + b := by linarith [abs_le.mp h₁]
  have h1b : a + x + b ≤ 1 := by linarith [abs_le.mp h₁]

  have h2a : -1 ≤ 4 * a + 2 * x + b := by linarith [abs_le.mp h₂]
  have h2b : 4 * a + 2 * x + b ≤ 1 := by linarith [abs_le.mp h₂]

  have h3a : -1 ≤ 9 * a + 6 * x + 4 * b := by linarith [abs_le.mp h₃]
  have h3b : 9 * a + 6 * x + 4 * b ≤ 1 := by linarith [abs_le.mp h₃]
  
  cases' abs_cases x with hx hx
  · -- x ≥ 0
    linarith
  · -- x < 0
    linarith