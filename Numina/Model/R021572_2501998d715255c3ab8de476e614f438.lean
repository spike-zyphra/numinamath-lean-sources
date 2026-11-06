import Mathlib

theorem inequalities_324540 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (2*a+b+c)^2/(2*a^2+(b+c)^2) + (2*b+c+a)^2/(2*b^2+(c+a)^2) +
    (2*c+a+b)^2/(2*c^2+(a+b)^2) ≤ 8 := by
  have h1 : 0 < 2 * a^2 + (b + c)^2 := by positivity
  have h2 : 0 < 2 * b^2 + (c + a)^2 := by positivity
  have h3 : 0 < 2 * c^2 + (a + b)^2 := by positivity
  have h6 : (2*a+b+c)^2/(2*a^2+(b+c)^2) + (2*b+c+a)^2/(2*b^2+(c+a)^2) + (2*c+a+b)^2/(2*c^2+(a+b)^2) - 8 ≤ 0 := by
    have h10 : 0 < (2*a^2 + (b + c)^2) * (2*b^2 + (c + a)^2) * (2*c^2 + (a + b)^2) := by positivity
    have eq1 : (2*a+b+c)^2/(2*a^2+(b+c)^2) + (2*b+c+a)^2/(2*b^2+(c+a)^2) + (2*c+a+b)^2/(2*c^2+(a+b)^2) - 8 =
        ((2*a+b+c)^2 * (2*b^2+(c+a)^2) * (2*c^2+(a+b)^2) +
        (2*b+c+a)^2 * (2*a^2+(b+c)^2) * (2*c^2+(a+b)^2) +
        (2*c+a+b)^2 * (2*a^2+(b+c)^2) * (2*b^2+(c+a)^2) - 8 * (2*a^2+(b + c)^2) * (2*b^2+(c+a)^2) * (2*c^2+(a+b)^2)) / ((2*a^2+(b + c)^2) * (2*b^2+(c+a)^2) * (2*c^2+(a+b)^2)) := by
      field_simp
      ring
    rw [eq1] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Prove numerator nonpositive
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2)]
    · -- Prove denominator non-negative
      positivity
  linarith