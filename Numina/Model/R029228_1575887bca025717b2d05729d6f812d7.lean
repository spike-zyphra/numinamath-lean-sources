import Mathlib

theorem algebra_4354
    (a b c : ℝ)
    (apos : 0 < a)
    (bpos : 0 < b)
    (cpos : 0 < c)
    (h1 : a * b + a + b = 8)
    (h2 : b * c + b + c = 8)
    (h3 : c * a + c + a = 8) :
    (a + 1) * (b + 1) * (c + 1) = 27 := by
  have h4 : a = c := by
    have eq1 : (b + 1) * (a - c) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp eq1) with h5 h6
    · -- Since b > 0, b + 1 > 0, so it's a contradiction
      linarith
    · -- a - c = 0
      linarith
  -- Subtract equations 2 and 3 to get $b = a$
  have h5 : b = a := by
    have eq2 : (c + 1) * (b - a) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq2) with h6 h7
    · -- Since c > 0, c + 1 > 0, contradiction
      linarith
    · -- b - a = 0
      linarith
  -- Now $a = c$ and $b = a$, so $a = b = c$
  have h6 : b = a := h5
  have h7 : c = a := by linarith [h4]
  -- Substitute $b = a$ into h1
  rw [show b = a by linarith [h5]] at h1
  -- Now h1 is $a \cdot a + a + a = 8$, i.e., $a^2 + 2 a - 8 = 0$
  have ha : a ^ 2 + 2 * a - 8 = 0 := by
    nlinarith
  -- Solving the quadratic $a^2 + 2a - 8 = 0$ 
  have ha2 : a = 2 := by
    have h8 : a ^ 2 + 2 * a - 8 = 0 := ha
    have h9 : (a - 2) * (a + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- a - 2 = 0, so a = 2
      linarith
    · -- a + 4 = 0, so a = -4, which is a contradiction
      nlinarith
  -- Therefore $a = 2$
  have ha2 : a = 2 := by
    nlinarith [ha, apos]
  -- Since $b = a$, $b = 2$
  have hb2 : b = 2 := by linarith [h5, ha2]
  -- Since $c = a$, $c = 2$
  have hc2 : c = 2 := by linarith [h4, ha2]
  -- Compute $(a + 1)(b + 1)(c + 1)$
  rw [ha2, hb2, hc2]
  norm_num