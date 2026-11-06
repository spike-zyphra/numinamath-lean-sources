import Mathlib

theorem algebra_251366 : {x : ℝ | (2 * (x - 10)) / (x ^ 2 - 13 * x + 30) = 1 ∧ x ^ 2 - 13 * x + 30 ≠ 0} ≠ {x : ℝ | x ^ 2 - 15 * x + 50 = 0} := by
  by_contra h
  have h1 : (10 : ℝ) ∈ ({x : ℝ | x ^ 2 - 15 * x + 50 = 0} : Set ℝ) := by
    norm_num
  have h2 : (10 : ℝ) ∈ ({x : ℝ | (2 * (x - 10)) / (x ^ 2 - 13 * x + 30) = 1 ∧ x ^ 2 - 13 * x + 30 ≠ 0} : Set ℝ) := by 
    rw [h] at *
    exact h1
  norm_num at h2 ⊢