import Mathlib

theorem inequalities_169938 (a b c : ℝ) (h₀ : a ≠ b) (h₁ : b ≠ c) (h₂ : a ≠ c) :
    5 ≤ ((2 * a - b) / (a - b)) ^ 2 + ((2 * b - c) / (b - c)) ^ 2 +
        ((2 * c - a) / (c - a)) ^ 2 := by
  have ha : a - b ≠ 0 := by
    intro h
    apply h₀
    linarith
  have hb : b - c ≠ 0 := by
    intro h
    apply h₁
    linarith
  have hc : c - a ≠ 0 := by
    intro h
    apply h₂
    linarith
  have h4 : ((2 * a - b) / (a - b)) ^ 2 + ((2 * b - c) / (b - c)) ^ 2 + ((2 * c - a) / (c - a)) ^ 2 = 5 + (a / (a - b) + b / (b - c) + c / (c - a)) ^ 2 := by
    have eq1 : ((2 * a - b) / (a - b)) ^ 2 + ((2 * b - c) / (b - c)) ^ 2 + ((2 * c - a) / (c - a)) ^ 2 =
        5 + (a / (a - b) + b / (b - c) + c / (c - a)) ^ 2 := by
      have ha1 : a - b ≠ 0 := by
        intro h
        apply h₀
        linarith
      have hb1 : b - c ≠ 0 := by
        intro h
        apply h₁
        linarith
      have hc1 : c - a ≠ 0 := by
        intro h
        apply h₂
        linarith
      field_simp [ha1, hb1, hc1]
      <;> nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
        intro h
        apply h₀
        linarith
      ), sq_pos_of_ne_zero (show (b - c) ≠ 0 by
        intro h
        apply h₁
        linarith
      ), sq_pos_of_ne_zero (show (c - a) ≠ 0 by
        intro h
        apply h₂
        linarith
      ), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)), sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)), sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a)]
    linarith
  rw [h4]
  nlinarith [sq_nonneg (a / (a - b) + b / (b - c) + c / (c - a)), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_pos_of_ne_zero (show (a - b) ≠ 0 by
    intro h
    apply h₀
    linarith
  ), sq_pos_of_ne_zero (show (b - c) ≠ 0 by
    intro h
    apply h₁
    linarith
  ), sq_pos_of_ne_zero (show (c - a) ≠ 0 by
    intro h
    apply h₂
    linarith
  )]