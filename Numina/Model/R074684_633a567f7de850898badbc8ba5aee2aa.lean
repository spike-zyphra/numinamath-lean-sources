import Mathlib

theorem algebra_321002 {a b : ℝ} (ha : a ≠ b) (h1 : a^2 = 4 * a + 3) (h2 : b^2 = 4 * b + 3) :
    a^2 / b + b^2 / a = -100 / 3 := by

  have ha1 : a ≠ 0 := by
    intro h
    rw [h] at h1
    nlinarith
  have hb1 : b ≠ 0 := by
    intro h
    rw [h] at h2
    nlinarith
  -- Compute $a + b$ and $a \cdot b$ from the quadratic equations
  have h3 : a + b = 4 := by
    have eq1 : a^2 - b^2 = 4 * (a - b) := by linarith
    have eq2 : a^2 - b^2 = (a - b) * (a + b) := by ring
    have h4 : (a - b) * (a + b) = 4 * (a - b) := by linarith [eq1, eq2]
    have h5 : a - b ≠ 0 := sub_ne_zero.mpr ha
    have h6 : a + b = 4 := by
      apply (mul_left_inj' h5).mp
      linarith
    linarith
  have h4 : a * b = -3 := by
    have eq1 : a^2 + b^2 = 4 * (a + b) + 6 := by
      linarith [h1, h2]
    have eq2 : a^2 + b^2 = (a + b)^2 - 2 * (a * b) := by ring
    rw [show a + b = 4 by linarith [h3]] at eq2
    linarith [eq1, eq2]
  -- Compute $a^3 + b^3$
  have eq1 : a^3 + b^3 = 100 := by
    -- Use the formula: $a^3 + b^3 = (a + b)( (a + b)^2 - 3*a*b )$
    have h_sum : a + b = 4 := h3
    have h_prod : a * b = -3 := h4
    have h_a3b3 : a^3 + b^3 = (a + b) * ( (a + b)^2 - 3 * (a * b) ) := by
      ring
    rw [h_a3b3, h_sum, h_prod]
    norm_num
  -- Compute $\frac{a^2}{b} + \frac{b^2}{a} = \frac{a^3 + b^3}{a \cdot b}$
  have eq2 : a^2 / b + b^2 / a = (a^3 + b^3) / (a * b) := by
    field_simp [show b ≠ 0 by exact hb1, show a ≠ 0 by exact ha1]
    <;> ring
  rw [eq2]
  rw [eq1, h4]
  norm_num