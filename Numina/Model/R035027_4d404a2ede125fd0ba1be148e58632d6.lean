import Mathlib

theorem inequalities_8205 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ 1 / a + 1 / b + 1 / c) :
    a + b + c ≥ 3 / (a + b + c) + 2 / (a * b * c) := by
  have h₁ : a * b * c * (a + b + c) ≥ a * b + a * c + b * c := by
    have h₁ : 0 < a * b * c := by
      positivity
    have h₂ : a + b + c ≥ 1 / a + 1 / b + 1 / c := h
    have h₃ : a * b * c * (a + b + c) ≥ a * b * c * (1 / a + 1 / b + 1 / c) := by
      apply mul_le_mul_of_nonneg_left h₂
      positivity
    have h₄ : a * b * c * (1 / a + 1 / b + 1 / c) = a * b + a * c + b * c := by
      field_simp [show 0 < a * b * c by positivity, show a ≠ 0 by positivity, show b ≠ 0 by positivity, show c ≠ 0 by positivity]
      <;> ring
    linarith [h₃, h₄]
  have h2 : 0 < a * b * c := by
    positivity
  have h3 : 0 < a + b + c := by
    linarith [ha, hb, hc]
  have h4 : a + b + c ≥ 3 / (a + b + c) + 2 / (a * b * c) := by
    have pos1 : 0 < (a + b + c) := h3
    have pos2 : 0 < (a * b * c) := h2
    have pos3 : 0 < (a * b * c) * (a + b + c) := by positivity
    have h5 : a * b * c * (a + b + c) ^ 2 ≥ 3 * (a * b * c) + 2 * (a + b + c) := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (a * c - b * c), 
                 sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
                 h₁, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                 mul_pos (show 0 < a * b by positivity) (show 0 < c by positivity)]
    have h7 : (a + b + c) - (3 / (a + b + c) + 2 / (a * b * c)) ≥ 0 := by
      have h8 : a * b * c * (a + b + c) * ((a + b + c) - (3 / (a + b + c) + 2 / (a * b * c))) ≥ 0 := by
        have h9 : a * b * c * (a + b + c) * ((a + b + c) - (3 / (a + b + c) + 2 / (a * b * c))) = 
          a * b * c * (a + b + c) ^ 2 - (3 * (a * b * c) + 2 * (a + b + c)) := by
          field_simp [show a + b + c ≠ 0 by positivity, show a * b * c ≠ 0 by positivity]
          <;> ring
        rw [h9]
        linarith
      have pos4 : 0 < a * b * c * (a + b + c) := by positivity
      nlinarith
    linarith
  exact h4