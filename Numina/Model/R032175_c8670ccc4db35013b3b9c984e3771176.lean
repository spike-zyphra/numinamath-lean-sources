import Mathlib

theorem inequalities_319164 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * b + b * c + a * c = 1) :
    5 / 2 ≤ 1 / (a + b) + 1 / (b + c) + 1 / (a + c) := by

  have h1 : 0 < a + b := by
    by_contra h1
    have h1' : a + b = 0 := by linarith
    have ha0 : a = 0 := by linarith [h1', ha, hb]
    have hb0 : b = 0 := by linarith [h1', ha, hb]
    have h0 : a * b + b * c + a * c = 0 := by
      rw [ha0, hb0]
      all_goals
        nlinarith
    linarith

  have h2 : 0 < b + c := by
    by_contra h2
    have h2' : b + c = 0 := by linarith
    have hb0 : b = 0 := by linarith [h2', hb, hc]
    have hc0 : c = 0 := by linarith [h2', hb, hc]
    have h0 : a * b + b * c + a * c = 0 := by
      rw [hb0, hc0]
      all_goals
        nlinarith
    linarith
  have h3 : 0 < a + c := by
    by_contra h3
    have h3' : a + c = 0 := by linarith
    have ha0 : a = 0 := by linarith [h3', ha, hc]
    have hc0 : c = 0 := by linarith [h3', ha, hc]
    have h0 : a * b + b * c + a * c = 0 := by
      rw [ha0, hc0]
      all_goals
        nlinarith
    linarith

  have h4 : 1 / (a + b) + 1 / (b + c) + 1 / (a + c) - 5 / 2 ≥ 0 := by 
    have h5 : 0 < (a + b) * (b + c) * (a + c) := by
      positivity
    have h7 : 0 < 2 * (a + b) * (b + c) * (a + c) := by
      positivity
    have h6 : (1 / (a + b) + 1 / (b + c) + 1 / (a + c) - 5 / 2) =
      (2 * ((b + c) * (a + c) ) + 2 * ((a + b) * (a + c)) + 2 * ((a + b) * (b + c)) - 5 * (a + b) * (b + c) * (a + c)) / (2 * (a + b) * (b + c) * (a + c)) := by
      field_simp
      <;> ring
    rw [h6] at *
    apply div_nonneg
    have h8 : 2 * ((b + c) * (a + c)) + 2 * ((a + b) * (a + c)) + 2 * ((a + b) * (b + c)) - 5 * (a + b) * (b + c) * (a + c) ≥ 0 := by
      have h1' : a * b + b * c + a * c = 1 := h
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith), 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith), 
          mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ b * c by nlinarith), 
          mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ c * a by nlinarith), 
          mul_nonneg (show 0 ≤ b * c by nlinarith) (show 0 ≤ c * a by nlinarith), 
          sq_nonneg (a + b + c - 2), 
          h]
    linarith
    all_goals
      positivity

  linarith