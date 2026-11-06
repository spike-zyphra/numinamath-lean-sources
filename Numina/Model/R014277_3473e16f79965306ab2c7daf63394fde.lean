import Mathlib

theorem inequalities_6937 (a b : ℝ) (ha : 0 ≤ a ∧ a < 1) (hb : 0 ≤ b ∧ b < 1) :
    9 / (3 + a + b) ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 - a * b) := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  have h1 : 0 < (1 + a) := by nlinarith
  have h2 : 0 < (1 + b) := by nlinarith
  have h3 : 0 < (1 - a * b) := by nlinarith
  have h4 : 0 < (3 + a + b) := by nlinarith
  have h5 : 0 < (1 + a) * (1 + b) * (1 - a * b) * (3 + a + b) := by positivity
  have h6 : (1 / (1 + a) + 1 / (1 + b) + 1 / (1 - a * b) - 9 / (3 + a + b)) ≥ 0 := by
    have h7 : (1 / (1 + a) + 1 / (1 + b) + 1 / (1 - a * b) - 9 / (3 + a + b)) =
        ((1 + b) * (1 - a * b) * (3 + a + b) + (1 + a) * (1 - a * b) * (3 + a + b) + (1 + a) * (1 + b) * (3 + a + b) - 9 * (1 + a) * (1 + b) * (1 - a * b)) / ((1 + a) * (1 + b) * (1 - a * b) * (3 + a + b)) := by 
      field_simp
      ring
    rw [h7] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a)), sq_nonneg (b - (1 - b)), 
      sq_nonneg (a + b - 1), sq_nonneg (a * b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), 
      mul_nonneg ha1 hb1, mul_nonneg (show 0 ≤ (1 - a) by nlinarith) (show 0 ≤ (1 - b) by nlinarith)]
    all_goals positivity
  linarith [h6]