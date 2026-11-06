import Mathlib

theorem algebra_119256 {k b : ℝ} (h : ∃ x, x ≠ 0 ∧ 7 * x + (3 + x) = k + b * x ∧
    ∃ y, y ≠ 0 ∧ 7 * y + (3 + y) = k - b * y ∧ x = y / 3) :
    b = -4 := by
  obtain ⟨x, hx1, heq1, ⟨y, hy1, heq2, hxy⟩⟩ := h

  -- Simplify the first equation: 7x + (3 + x) = k + b*x to 8x + 3 = k + b*x
  have eq1 : 8 * x + 3 = k + b * x := by
    linarith [heq1]

  -- Simplify the second equation: 7y + (3 + y) = k - b*y to 8y + 3 = k - b*y
  have eq2 : 8 * y + 3 = k - b * y := by
    linarith [heq2]

  -- From hxy: x = y/3, we deduce that y = 3*x
  have h1 : y = 3 * x := by
    linarith

  -- Substitute y = 3*x into the second equation: 8*(3*x) + 3 = k - b*(3*x)
  rw [show y = 3 * x by linarith [h1]] at eq2

  -- From eq1 we have: k = 8*x + 3 - b*x
  have eq3 : k = 8 * x + 3 - b * x := by
    linarith

  -- Substitute the expression for k from eq3 into eq2
  rw [eq3] at eq2

  -- Now solve the equation to find that b = -4
  have : b = -4 := by
    apply (mul_left_inj' hx1).mp
    linarith

  exact this