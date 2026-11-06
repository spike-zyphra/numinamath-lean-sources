import Mathlib

theorem algebra_242534 {x y z : ℝ} (h₀ : x^2 = (y - z)^2 - 3) (h₁ : y^2 = (z - x)^2 - 9)
    (h₂ : z^2 = (x - y)^2 + 27) :
    (x = -1 ∧ y = -4 ∧ z = -6) ∨ (x = 1 ∧ y = 4 ∧ z = 6) := by
  have eq1 : x^2 = y^2 - 2 * y * z + z^2 - 3 := by
    nlinarith 
  have eq2 : y^2 = z^2 - 2 * z * x + x^2 - 9 := by
    nlinarith 
  have eq3 : z^2 = x^2 - 2 * x * y + y^2 + 27 := by
    nlinarith 
  have h3 : (x - 1) * (x + 1) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  cases' (mul_eq_zero.mp h3) with hx1 hx1
  · -- Case where x = 1
    have hx1 : x = 1 := by linarith
    have hy4 : y = 4 := by
      rw [hx1] at eq2 eq3
      nlinarith
    have hz6 : z = 6 := by
      rw [hx1, hy4] at eq1 eq2 eq3
      nlinarith 
    right
    exact ⟨by linarith, by linarith, by linarith⟩
  · -- Case where x = -1
    have hx1 : x = -1 := by linarith
    have hy4 : y = -4 := by
      rw [hx1] at eq2 eq3
      nlinarith
    have hz6 : z = -6 := by
      rw [hx1, hy4] at eq1 eq2 eq3
      nlinarith 
    left
    exact ⟨by linarith, by linarith, by linarith⟩