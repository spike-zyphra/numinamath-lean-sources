import Mathlib

open Real

theorem algebra_218444 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (h1 : logb 10 a + logb b c = 3) (h2 : logb 10 b + logb a c = 4) :
    logb 10 a * logb 10 c ≤ 16 / 3 := by
  have h1' : logb b c = logb 10 c / logb 10 b := by
    field_simp [logb]
    all_goals linarith
  rw [h1'] at h1
  have h2' : logb a c = logb 10 c / logb 10 a := by
    field_simp [logb]
    all_goals linarith
  rw [h2'] at h2

  have h10 : 0 < logb 10 a := by
    have h11 : logb 10 a > 0 := by
      apply logb_pos
      all_goals linarith
    linarith
  have h11 : 0 < logb 10 b := by
    have h12 : logb 10 b > 0 := by
      apply logb_pos
      all_goals linarith
    linarith

  have h4 : 3 * logb 10 b = 4 * logb 10 a := by
    have h7 : logb 10 a * logb 10 b + logb 10 c = 3 * logb 10 b := by
      have h8 : logb 10 b ≠ 0 := by
        linarith
      field_simp [h8] at h1 ⊢
      nlinarith
    have h8 : logb 10 a * logb 10 b + logb 10 c = 4 * logb 10 a := by
      have h9 : logb 10 a ≠ 0 := by
        linarith
      field_simp [h9] at h2 ⊢
      nlinarith
    nlinarith
  have h5 : logb 10 b = 4 / 3 * logb 10 a := by
    nlinarith

  have h6 : logb 10 c = 4 * logb 10 a - 4 / 3 * (logb 10 a)^2 := by
    have h7 : logb 10 a * logb 10 b + logb 10 c = 3 * logb 10 b := by
      have h8 : logb 10 b ≠ 0 := by
        linarith
      field_simp [h8] at h1 ⊢
      nlinarith
    rw [h5] at h7
    nlinarith [sq_nonneg (logb 10 a - 2), sq_nonneg (logb 10 a), sq_nonneg (logb 10 a - 3 / 2)]
  
  have h7 : logb 10 a * logb 10 c = 4 * (logb 10 a)^2 - 4 / 3 * (logb 10 a)^3 := by
    rw [h6]
    ring_nf

  have h8 : 4 * (logb 10 a)^2 - 4 / 3 * (logb 10 a)^3 ≤ 16 / 3 := by
    nlinarith [sq_nonneg (logb 10 a - 2), sq_nonneg (logb 10 a), sq_nonneg (logb 10 a - 3 / 2)]
  
  have h9 : logb 10 a * logb 10 c ≤ 16 / 3 := by
    linarith [h7, h8]

  linarith [h9]