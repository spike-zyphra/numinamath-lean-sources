import Mathlib

theorem inequalities_92159 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    a * (1 + b - c) ^ ((1 : ℝ) / 3) +
    b * (1 + c - a) ^ ((1 : ℝ) / 3) +
    c * (1 + a - b) ^ ((1 : ℝ) / 3) ≤ 1 := by

  have h2 : ∀ x ≥ (0 : ℝ), x ^ ((1 : ℝ) / 3) ≤ (x + 2) / 3 := by
    intro x hx
    have h2 : x ≥ 0 := hx
    have h6 : x ^ ((1 : ℝ) / 3) ≤ (x + 2) / 3 := by
      have h10 : (x ^ ((1 : ℝ) / 3)) * 3 ≤ x + 2 := by
        have h13 : ((x ^ ((1 : ℝ) / 3)) ) ^ 3 = x := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals nlinarith
        nlinarith [sq_nonneg ((x ^ ((1 : ℝ) / 3)) - 1), sq_nonneg ((x ^ ((1 : ℝ) / 3)) + 2), sq_nonneg ((x ^ ((1 : ℝ) / 3)) ^ 2 - (x ^ ((1 : ℝ) / 3))), sq_nonneg ((x ^ ((1 : ℝ) / 3)) ^ 2 - 1)]
      linarith
    linarith

  have h10 : 1 + b - c ≥ 0 := by 
    nlinarith [h, show a > 0 by linarith, show b > 0 by linarith, show c > 0 by linarith]
  have h110 : (1 + b - c) ^ ((1 : ℝ) / 3) ≤ (1 + b - c + 2) / 3 := by
    apply h2
    linarith

  have h100 : 1 + c - a ≥ 0 := by 
    nlinarith [h, show a > 0 by linarith, show b > 0 by linarith, show c > 0 by linarith]
  have h111 : (1 + c - a) ^ ((1 : ℝ) / 3) ≤ (1 + c - a + 2) / 3 := by
    apply h2
    linarith

  have h101 : 1 + a - b ≥ 0 := by 
    nlinarith [h, show a > 0 by linarith, show b > 0 by linarith, show c > 0 by linarith]
  have h112 : (1 + a - b) ^ ((1 : ℝ) / 3) ≤ (1 + a - b + 2) / 3 := by
    apply h2
    linarith

  have h3 : a * (1 + b - c) ^ ((1 : ℝ) / 3) ≤ a * ((1 + b - c + 2) / 3) := by
    apply mul_le_mul_of_nonneg_left h110
    linarith

  have h4 : b * (1 + c - a) ^ ((1 : ℝ) / 3) ≤ b * ((1 + c - a + 2) / 3) := by
    apply mul_le_mul_of_nonneg_left h111
    linarith

  have h5 : c * (1 + a - b) ^ ((1 : ℝ) / 3) ≤ c * ((1 + a - b + 2) / 3) := by
    apply mul_le_mul_of_nonneg_left h112
    linarith

  have h6 : a * (1 + b - c) ^ ((1 : ℝ) / 3) + b * (1 + c - a) ^ ((1 : ℝ) / 3) + c * (1 + a - b) ^ ((1 : ℝ) / 3) ≤
    a * ((1 + b - c + 2) / 3) + b * ((1 + c - a + 2) / 3) + c * ((1 + a - b + 2) / 3) := by
    linarith [h3, h4, h5]

  have h7 : a * ((1 + b - c + 2) / 3) + b * ((1 + c - a + 2) / 3) + c * ((1 + a - b + 2) / 3) ≤ 1 := by
    nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  linarith [h6, h7]