import Mathlib

theorem inequalities_597634 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 ≤ (a + 3) / (a + 1) ^ 2 + (b + 3) / (b + 1) ^ 2 + (c + 3) / (c + 1) ^ 2 := by
  have h1 : 0 < a * b * c := by positivity
  have h2 : a * b * c = 1 := habc
  have h10 : (a + 3) / (a + 1) ^ 2 + (b + 3) / (b + 1) ^ 2 + (c + 3) / (c + 1) ^ 2 - (3 : ℝ) ≥ 0 := by
    have h11 : 0 < (a + 1) ^ 2 := by positivity
    have h12 : 0 < (b + 1) ^ 2 := by positivity
    have h13 : 0 < (c + 1) ^ 2 := by positivity
    have h14 : (a + 3) / (a + 1) ^ 2 + (b + 3) / (b + 1) ^ 2 + (c + 3) / (c + 1) ^ 2 - (3 : ℝ) =
        ((a + 3) * (b + 1) ^ 2 * (c + 1) ^ 2 + (b + 3) * (a + 1) ^ 2 * (c + 1) ^ 2 + (c + 3) * (a + 1) ^ 2 * (b + 1) ^ 2 - 3 * (a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2) / ((a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2) := by
      field_simp
      <;> ring
    have hx2 : ((a + 3) * (b + 1) ^ 2 * (c + 1) ^ 2 + (b + 3) * (a + 1) ^ 2 * (c + 1) ^ 2 + (c + 3) * (a + 1) ^ 2 * (b + 1) ^ 2 - 3 * (a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2) ≥ 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha (show 0 < b * c by nlinarith), 
          mul_pos hb (show 0 < a * c by nlinarith), 
          mul_pos hc (show 0 < a * b by nlinarith), 
          mul_pos ha hb, mul_pos ha hc, 
          mul_pos hb hc, 
          habc]
    rw [h14] at *
    apply div_nonneg
    linarith 
    all_goals positivity 
    all_goals positivity
  linarith 
  all_goals positivity