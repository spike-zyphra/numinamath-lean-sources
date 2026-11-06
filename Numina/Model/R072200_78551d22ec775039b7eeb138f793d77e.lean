import Mathlib

theorem algebra_601735 {x y : ℝ} (h1 : x * (x + 1) * (3 * x + 5 * y) = 144) (h2 : x ^ 2 + 4 * x + 5 * y = 24) :
    (x = -4 ∧ y = 24 / 5) ∨ (x = 3 ∧ y = 3 / 5) := by 

  have eq1 : y = (24 - x^2 - 4 * x) / 5 := by 
    linarith [h2]

  rw [eq1] at h1

  have h3 : x^4 + 2 * x^3 - 23 * x^2 - 24 * x + 144 = 0 := by
    nlinarith [sq_nonneg (x * (x + 1) - 12), sq_nonneg (x * (x + 1) + 12)]

  have h4 : (x - 3) ^ 2 * (x + 4) ^ 2 = 0 := by 
    nlinarith [h3]

  cases' (mul_eq_zero.mp h4) with h5 h6

  · -- Case where (x - 3)^2 = 0
    have hx : x = 3 := by nlinarith
    have hy : y = 3 / 5 := by
      rw [hx] at eq1
      nlinarith
    right
    exact ⟨hx, hy⟩

  · -- Case where (x + 4)^2 = 0
    have hx : x = -4 := by nlinarith
    have hy : y = 24 / 5 := by
      rw [hx] at eq1
      nlinarith
    left
    exact ⟨hx, hy⟩