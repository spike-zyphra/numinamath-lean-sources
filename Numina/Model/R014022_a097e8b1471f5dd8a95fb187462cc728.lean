import Mathlib

theorem algebra_7203
    {a b : ℝ}
    (ha : 0 < a)
    (hb : 0 < b)
    (h : 1 / a - 1 / b - 1 / (a + b) = 0) :
    (b / a)^2 + (a / b)^2 = 3 := by

  have h1 : 0 < a + b := by 
    linarith

  have eq1 : b * (a + b) - a * (a + b) - a * b = 0 := by
    have h2 : a ≠ 0 := by linarith
    have h3 : b ≠ 0 := by linarith
    have h4 : a + b ≠ 0 := by linarith
    field_simp [h2, h3, h4] at h ⊢
    nlinarith [h, mul_pos ha hb, mul_pos (show 0 < a from ha) (show 0 < b from hb)]
  
  -- From $b(a + b) - a(a + b) - ab = 0$, expanding gives $b^2 - a^2 - ab = 0$
  -- Therefore $b^2 = a^2 + ab$.
  have eq2 : b^2 = a^2 + a * b := by 
    nlinarith [eq1]

  -- Now compute $(b/a)^2 + (a/b)^2$. It can be written as $(b^2 + a^2)^2 / (ab)^2 - 2$.
  -- But we use the identity $x^2 + y^2 = (x + y)^2 - 2xy$.
  -- Let $x = \frac{b}{a}$ and $y = \frac{a}{b}$.
  -- Then $x + y = \frac{b}{a} + \frac{a}{b} = \frac{b^2 + a^2}{ab}$.
  -- So we need to compute $\left( \frac{b^2 + a^2}{ab} \right)^2 - 2 \cdot 1$.
  -- Since $\frac{b}{a} \cdot \frac{a}{b} = 1$.
  have eq3 : (b / a)^2 + (a / b)^2 = ((b^2 + a^2) / (a * b)) ^ 2 - 2 := by
    field_simp
    <;> nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]

  -- Compute $\frac{b^2 + a^2}{ab}$.
  -- From $b^2 = a^2 + ab$, $b^2 + a^2 = 2 a^2 + ab$.
  have eq4 : (b^2 + a^2) = 2 * a^2 + a * b := by
    nlinarith [eq2]

  -- So $\frac{b^2 + a^2}{ab} = \frac{2 a^2 + ab}{ab} = \frac{2 a + b}{b}$.
  have eq5 : (b^2 + a^2) / (a * b) = (2 * a + b) / b := by
    have h1 : a * b ≠ 0 := by
      apply mul_ne_zero
      linarith
      linarith
    field_simp [h1]
    <;> nlinarith [eq4, mul_pos ha hb]

  rw [eq3]
  rw [eq5]
  -- Compute $\left( \frac{2a + b}{b} \right)^2 - 2$, which equals 3.
  have eq6 : ((2 * a + b) / b) ^ 2 - 2 = 3 := by
    have h1 : b ≠ 0 := by linarith
    field_simp [h1]
    <;> nlinarith [eq2, mul_pos ha hb, sq_pos_of_pos ha, sq_pos_of_pos hb]

  linarith [eq6]