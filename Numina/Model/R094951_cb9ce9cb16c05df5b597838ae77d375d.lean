import Mathlib

theorem algebra_318743 (k : ℝ) (f : ℝ → ℝ) (hf : f = fun x => x^2 + (k + 2) * x + k + 5)
    (h : ∃ x y, x > 0 ∧ y > 0 ∧ f x = 0 ∧ f y = 0 ∧ x ≠ y) :
    -5 < k ∧ k < -4 := by
  rcases h with ⟨x, y, hx_pos, hy_pos, hx_eq, hy_eq, hxy⟩

  have hfx : f x = x^2 + (k + 2) * x + k + 5 := by simp [hf]
  have hfy : f y = y^2 + (k + 2) * y + k + 5 := by simp [hf]

  rw [hfx] at hx_eq
  rw [hfy] at hy_eq

  have eq1 : x^2 + (k + 2) * x + k + 5 = 0 := by linarith
  have eq2 : y^2 + (k + 2) * y + k + 5 = 0 := by linarith

  have sub_eq : (x^2 + (k + 2) * x + k + 5) - (y^2 + (k + 2) * y + k + 5) = 0 := by 
    linarith [eq1, eq2]

  have eq3 : (x^2 - y^2) + (k + 2) * (x - y) = 0 := by
    nlinarith

  have eq4 : (x - y) * (x + y + k + 2) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp eq4) with h1 h2
  · -- Case h1: x - y = 0
    exfalso
    exact hxy (by linarith)
  · -- Case h2: x + y + k + 2 = 0 
    have h3 : k + 2 < 0 := by 
      nlinarith [show x + y > 0 by linarith [hx_pos, hy_pos]]

    have h4 : k + 5 > 0 := by
      nlinarith [show x * y > 0 by nlinarith]

    have h5 : (k + 2) ^ 2 - 4 * (k + 5) > 0 := by
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hxy), sq_nonneg (x - y)]

    have h6 : k^2 - 16 > 0 := by
      nlinarith

    constructor
    · -- k > -5
      nlinarith 
    · -- k < -4
      nlinarith