import Mathlib

theorem algebra_171454 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (a b : ℝ)
    (ha : a = 1 + x / y) (hb : b = 1 + y / x) (h : a ^ 2 + b ^ 2 = 15) :
    a ^ 3 + b ^ 3 = 50 := by
  have h1 : a * b = a + b := by
    rw [ha, hb]
    have hxy1 : 0 < x * y := mul_pos hx hy
    field_simp at *
    <;> nlinarith
  have h2 : a + b > 0 := by
    have ha1 : a > 0 := by
      rw [ha]
      have h11 : x / y > 0 := by apply div_pos; all_goals linarith
      linarith
    have hb1 : b > 0 := by
      rw [hb]
      have h11 : y / x > 0 := by apply div_pos; all_goals linarith
      linarith
    linarith
  have h3 : (a + b) ^ 2 - 2 * (a + b) - 15 = 0 := by
    have h1' : a * b = a + b := h1
    have eq1 : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by
      nlinarith
    rw [h1'] at eq1
    linarith [h, eq1]
  have h4 : (a + b - 5) * (a + b + 3) = 0 := by
    nlinarith
  have h5 : a + b = 5 := by
    have h6 : a + b > 0 := h2
    cases' (mul_eq_zero.1 h4) with h6 h7
    · linarith
    · nlinarith
  have h6 : a ^ 3 + b ^ 3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by
    ring
  rw [h6, h5]
  have h7 : a * b = a + b := h1
  rw [h7]
  rw [h5]
  all_goals nlinarith