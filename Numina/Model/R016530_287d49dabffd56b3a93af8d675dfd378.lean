import Mathlib

theorem algebra_101030 {a b c : ℝ} (ha : a ≠ 0) (hvertex : ∀ x, y = a * (x - 4) ^ 2 + 2)
    (hpoint : a * 2 ^ 2 + b * 2 + c = 0) : a * b * c = 12 := by 
  have eq1 := hvertex 4
  have eq2 := hvertex 2
  have eq3 := hvertex 0
  have eq4 := hvertex 1
  -- Now, `eq1 : y = 2`, `eq2 : y = 4 * a + 2`, `eq3 : y = 16 * a + 2`, `eq4 : y = 9 * a + 2`.
  -- From `eq1` and `eq2`, we have 4a + 2 = 2, so 4a = 0, hence a = 0.
  have h1 : a = 0 := by
    norm_num at eq1 eq2 eq3 eq4
    linarith
  -- This contradicts `ha : a ≠ 0`
  contradiction