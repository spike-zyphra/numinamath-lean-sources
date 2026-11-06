import Mathlib

open Real

theorem inequalities_216381 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * b + b * c + c * a = 1) :
    1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≥ 5 / 2 := by

  have h1 : a + b > 0 := by
    by_contra h1
    have h1 : a + b ≤ 0 := by nlinarith
    have ha0 : a = 0 := by linarith [show 0 ≤ a by linarith, show 0 ≤ b by linarith]
    have hb0 : b = 0 := by linarith [show 0 ≤ a by linarith, show 0 ≤ b by linarith]
    have h11 : a * b + b * c + c * a = 0 := by 
      rw [ha0, hb0]
      nlinarith
    linarith
  have h2 : b + c > 0 := by 
    by_contra h2
    have h2 : b + c ≤ 0 := by nlinarith
    have hb0 : b = 0 := by linarith [show 0 ≤ b by linarith, show 0 ≤ c by linarith]
    have hc0 : c = 0 := by linarith [show 0 ≤ b by linarith, show 0 ≤ c by linarith]
    have h11 : a * b + b * c + c * a = 0 := by 
      rw [hb0, hc0]
      nlinarith
    linarith
  have h3 : c + a > 0 := by 
    by_contra h3
    have h3 : c + a ≤ 0 := by nlinarith
    have hc0 : c = 0 := by linarith [show 0 ≤ c by linarith, show 0 ≤ a by linarith]
    have ha0 : a = 0 := by linarith [show 0 ≤ c by linarith, show 0 ≤ a by linarith]
    have h11 : a * b + b * c + c * a = 0 := by 
      rw [hc0, ha0]
      nlinarith
    linarith
  have h4 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - 5 / 2 ≥ 0 := by 
    have h5 : 0 < (a + b) * (b + c) * (c + a) := by
      positivity
    have h6 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - 5 / 2 =
        (2 * (b + c) * (c + a) + 2 * (a + b) * (c + a) + 2 * (a + b) * (b + c) - 5 * (a + b) * (b + c) * (c + a)) / (2 * (a + b) * (b + c) * (c + a)) := by
      field_simp
      ring
    rw [h6]
    have h7 : 2 * (b + c) * (c + a) + 2 * (a + b) * (c + a) + 2 * (a + b) * (b + c) - 5 * (a + b) * (b + c) * (c + a) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        sq_nonneg (a + b + c - 2), 
        h, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc
      ]
    apply div_nonneg 
    linarith 
    positivity 
  linarith