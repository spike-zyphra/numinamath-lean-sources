import Mathlib

open Real

theorem inequalities_603680 :
    ∃ c : ℝ, ∀ x y : ℝ, x > 0 → y > 0 → x / (2 * x + y) + y / (x + 2 * y) ≤ c ∧
    c ≤ x / (x + 2 * y) + y / (2 * x + y) := by
  use 2 / 3
  intro x y hx hy
  constructor
  · -- Show that $\frac{x}{2x+y} + \frac{y}{x+2y} \leq \frac{2}{3}$
    have h1 : 0 < (2 * x + y) * (x + 2 * y) := by
      positivity
    have h2 : x / (2 * x + y) + y / (x + 2 * y) - (2 / 3) ≤ 0 := by
      have h3 : x / (2 * x + y) + y / (x + 2 * y) - (2 / 3) = 
        (3 * x * (x + 2 * y) + 3 * y * (2 * x + y) - 2 * (2 * x + y) * (x + 2 * y)) / (3 * (2 * x + y) * (x + 2 * y)) := by 
        field_simp
        ring
      rw [h3] 
      have h4 : 3 * x * (x + 2 * y) + 3 * y * (2 * x + y) - 2 * (2 * x + y) * (x + 2 * y) ≤ 0 := by
        nlinarith [sq_nonneg (x - y)]
      have h5 : 3 * (2 * x + y) * (x + 2 * y) > 0 := by positivity
      apply div_nonpos_of_nonpos_of_nonneg h4 (by positivity)
    linarith
  · -- Show that $\frac{2}{3} \leq \frac{x}{x+2y} + \frac{y}{2x+y}$
    have h1 : 0 < (x + 2 * y) * (2 * x + y) := by 
      positivity
    have h2 : (2 / 3 : ℝ) - (x / (x + 2 * y) + y / (2 * x + y)) ≤ 0 := by
      have h3 : (2 / 3 : ℝ) - (x / (x + 2 * y) + y / (2 * x + y)) = 
        (2 * (x + 2 * y) * (2 * x + y) - 3 * x * (2 * x + y) - 3 * y * (x + 2 * y)) / (3 * (x + 2 * y) * (2 * x + y)) := by 
        field_simp 
        ring 
      rw [h3] 
      have h4 : 2 * (x + 2 * y) * (2 * x + y) - 3 * x * (2 * x + y) - 3 * y * (x + 2 * y) ≤ 0 := by 
        nlinarith [sq_nonneg (x - y)]
      have h5 : 3 * (x + 2 * y) * (2 * x + y) > 0 := by positivity
      apply div_nonpos_of_nonpos_of_nonneg h4 (by positivity)
    linarith