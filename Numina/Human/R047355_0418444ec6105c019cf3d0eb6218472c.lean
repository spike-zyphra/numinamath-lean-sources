import Mathlib

/-Given positive numbers a,b,c,d satisfy a+2b=1, c+2d=1. Then the minimum value of 1/a +1/bcd is ?-/
theorem algebra_310982 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + 2 * b = 1) (h2 : c + 2 * d = 1) :
    1 / a + 1 / (b * c * d) ≥ 25 := by 
  have h3 : a = 1 - 2 * b := by linarith 
  have h4 : c = 1 - 2 * d := by linarith 
  have hb1 : 1 - 2 * b > 0 := by linarith [ha]
  have hd1 : 1 - 2 * d > 0 := by linarith [hc]
  have hb2 : b < 1 / 2 := by nlinarith 
  have hd2 : d < 1 / 2 := by nlinarith 
  have h5 : 0 < 1 - 2 * b := by linarith
  have h6 : 0 < 1 - 2 * d := by linarith
  -- write a c in terms of b and d --
  have h7 : 1 / a + 1 / (b * c * d) = 1 / (1 - 2 * b) + 1 / (b * (1 - 2 * d) * d) := by
    rw [h3, h4]
  rw [h7]
  -- prove by completing the square --
  have h8 : 1 / (1 - 2 * b) + 1 / (b * (1 - 2 * d) * d) ≥ 25 := by
    have h9 : b * (1 - 2 * d) * d + (1 - 2 * b) ≥ 25 * (b * (1 - 2 * d) * d * (1 - 2 * b)) := by 
      nlinarith [sq_nonneg (b - 2 / 5), sq_nonneg (d - 1 / 4),
        mul_pos hb hd, mul_pos hd (show 0 < 1 - 2 * d by linarith [hc]), 
        mul_pos hb (show 0 < 1 - 2 * b by linarith [ha])]
    have h10 : (1 / (1 - 2 * b) + 1 / (b * (1 - 2 * d) * d)) - 25 ≥ 0 := by
      have h11 : b * (1 - 2 * d) * d + (1 - 2 * b) ≥ 25 * (b * (1 - 2 * d) * d * (1 - 2 * b)) := h9
      have h12 : 0 < b * (1 - 2 * d) * d * (1 - 2 * b) := by
        apply mul_pos
        apply mul_pos
        apply mul_pos
        all_goals linarith
      have h13 : (1 / (1 - 2 * b) + 1 / (b * (1 - 2 * d) * d)) - 25 = 
        (b * (1 - 2 * d) * d + (1 - 2 * b) - 25 * (b * (1 - 2 * d) * d * (1 - 2 * b))) / 
        (b * (1 - 2 * d) * d * (1 - 2 * b)) := by 
        field_simp
        ring
      rw [h13]
      apply div_nonneg
      nlinarith
      nlinarith
    linarith
  linarith