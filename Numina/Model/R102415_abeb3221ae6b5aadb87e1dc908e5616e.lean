import Mathlib

open Real

theorem algebra_3616 {a b : ℝ} (ha : 2017 * a ^ 2 - 212 * a - 1 = 0) (hb : 2017 * b = 1 / b + 212) (hab : a ≠ b) : 1 / a + 1 / b = -212 := by 
  have hb1 : b ≠ 0 := by
    by_contra h
    rw [h] at hb
    norm_num at hb
  have ha1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    nlinarith
  have h1 : 2017 * b ^ 2 - 212 * b - 1 = 0 := by 
    field_simp [hb1] at hb
    linarith
  have h2 : a + b = 212 / 2017 := by
    have h11 : 2017 * a ^ 2 - 212 * a - 1 = 0 := ha
    have h12 : 2017 * b ^ 2 - 212 * b - 1 = 0 := h1
    have h13 : 2017 * (a^2 - b^2) - 212 * (a - b) = 0 := by
      nlinarith [h11, h12]
    have h14 : (a - b) * (2017 * (a + b) - 212) = 0 := by
      nlinarith [h13]
      -- ring
    cases' (mul_eq_zero.1 h14) with h15 h16
    · -- Case where $a - b = 0$, which would imply $a = b$
      exfalso
      exact hab (by linarith)
    · -- Case where $2017 \cdot (a + b) - 212 = 0$
      linarith
  have h3 : a * b = -1 / 2017 := by
    nlinarith [ha, h1, sq_pos_of_ne_zero (sub_ne_zero_of_ne hab), sq_pos_of_ne_zero (show a - b ≠ 0 by intro h; apply hab; linarith)
    ]
  have h4 : 1 / a + 1 / b = (a + b) / (a * b) := by
    field_simp [ha1, hb1]
    <;> nlinarith [ha, h1]
  rw [h4, h2, h3]
  norm_num