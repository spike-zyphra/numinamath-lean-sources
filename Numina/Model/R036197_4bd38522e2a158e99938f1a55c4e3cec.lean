import Mathlib

theorem algebra_9276
  {a b c : ℝ}
  (h : a ≠ b)
  (h1 : a^2 * (b + c) = 2011)
  (h2 : b^2 * (a + c) = 2011) :
  a * b * c = -2011 := by

  have eq1 : a^2 * (b + c) = 2011 := h1
  have eq2 : b^2 * (a + c) = 2011 := h2
  have eq3 : a^2 * (b + c) - b^2 * (a + c) = 0 := by
    linarith [h1, h2]

  have eq4 : (a - b) * (a * b + c * (a + b)) = 0 := by
    have eq5 : a^2 * (b + c) - b^2 * (a + c) =
        (a - b) * (a * b + c * (a + b)) := by
      ring
    rw [eq5] at eq3
    linarith

  have eq5 : a * b + c * (a + b) = 0 := by
    cases (mul_eq_zero.mp eq4) with
    | inl h' => 
      -- a - b = 0, but a ≠ b
      exfalso
      apply h
      linarith
    | inr h' => 
      linarith

  -- From h1: a^2(b + c) = 2011. This means $a^2b + a^2c = 2011$.
  -- From eq5: ab + ac + bc = 0. Multiply by a: a^2b + a^2c + a * b * c = 0 
  -- Hence, 2011 + a * b * c = 0, so a * b * c = -2011
  have eq6 : a * b * c = -2011 := by
    have eq5' : a * b + c * (a + b) = 0 := eq5
    have eq7 : a^2 * (b + c) = 2011 := h1
    have eq8 : a^2 * b + a^2 * c = 2011 := by
      linarith [eq7]
    have eq9 : a * b + c * (a + b) = 0 := eq5
    have eq10 : a^2 * b + a^2 * c + a * b * c = 0 := by
      have eq9' : a * b + c * (a + b) = 0 := eq5
      have eq11 : (a * b + c * (a + b)) * a = 0 := by
        rw [eq9']
        all_goals norm_num
      linarith [eq11]
    nlinarith [eq8, eq10]

  exact eq6