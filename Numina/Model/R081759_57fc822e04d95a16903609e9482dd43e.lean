import Mathlib

theorem algebra_321182 {x y : ℝ} (h₁ : x + y + x * y = 19) (h₂ : x ^ 2 + y ^ 2 = 25) :
    x + y = 7 ∧ x * y = 12 := by
  have h3 : (x + y - 7) * (x + y + 9) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

  cases' (mul_eq_zero.mp h3) with h4 h6

  · -- Case where $x + y - 7 = 0$, so $x + y = 7$.
    have h5 : x + y = 7 := by linarith

    have h7 : x * y = 12 := by 
      nlinarith [h₁, h5]

    exact ⟨h5, h7⟩

  · -- Case where $x + y + 9 = 0$, so $x + y = -9$.
    have h7 : x + y = -9 := by linarith
    have h8 : x * y = 28 := by 
      nlinarith [h₁, h7]

    have h9 : (x + y) ^ 2 - 4 * (x * y) < 0 := by
      nlinarith [sq_nonneg (x - y)]

    nlinarith [sq_nonneg (x - y), h7, h8]