import Mathlib

theorem algebra_304581 {a : ℝ} (h : ∃ x y, x ≠ y ∧ 2*x^2-(a+1)*x+a+3=0 ∧ 2*y^2-(a+1)*y+a+3=0 ∧ |x-y| = 1) :
    a = 9 ∨ a = -3 := by
  rcases h with ⟨x, y, hxy, hx, hy, habs⟩
  cases eq_or_eq_neg_of_abs_eq habs with
  | inl h1 =>
    -- We know |x - y| = 1, so x - y = 1 in this case
    -- Subtract the two quadratic equations
    have h5 : (x - y) * (2 * (x + y) - (a + 1)) = 0 := by 
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hxy), h1, hx, hy]
      -- Now factor the difference equation into terms of (x - y) and sum
      -- From subtraction: 2(x^2-y^2) = (a+1)(x-y)
      -- This expands to (x-y)(2(x+y) = a+1)
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- We have x - y = 0, but we know x ≠ y
      exfalso
      exact hxy (by linarith)
    · -- We have 2(x + y) - (a + 1) = 0
      have h8 : x + y = (a + 1) / 2 := by
        linarith
      -- We also know |x - y| = 1, so x - y = 1
      have hx' : x = (a + 3) / 4 := by
        nlinarith [h8, h1]
      have hy' : y = (a - 1) / 4 := by
        nlinarith [h8, h1]
      rw [show x = (a + 3) / 4 by linarith [hx']] at hx
      have : (a - 9) * (a + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp this) with h9 h10
      · -- We have a - 9 = 0, so a = 9
        left
        linarith
      · -- We have a + 3 = 0, so a = -3
        right
        linarith
  | inr h2 =>
    -- We know |x - y| = 1, so x - y = -1 in this case
    -- Subtract the two quadratic equations
    have h5 : (x - y) * (2 * (x + y) - (a + 1)) = 0 := by 
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hxy), h2, hx, hy]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- We have x - y = 0, but we know x ≠ y
      exfalso
      exact hxy (by linarith)
    · -- We have 2(x + y) - (a + 1) = 0
      have h8 : x + y = (a + 1) / 2 := by
        linarith
      -- We know |x - y| = 1, so x - y = -1
      -- From this and the sum relation, derive expressions for x and y
      have hx' : x = (a - 1) / 4 := by
        nlinarith [h8, show x - y = -1 by linarith [h2]]
      have hy' : y = (a + 3) / 4 := by
        nlinarith [h8, show x - y = -1 by linarith [h2]]
      rw [show x = (a - 1) / 4 by linarith [hx']] at hx
      have : (a - 9) * (a + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp this) with h9 h10
      · -- We have a - 9 = 0, so a = 9
        left
        linarith
      · -- We have a + 3 = 0, so a = -3
        right
        linarith