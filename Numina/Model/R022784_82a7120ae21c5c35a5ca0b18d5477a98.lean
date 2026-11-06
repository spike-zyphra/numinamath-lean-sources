import Mathlib

open Real

theorem inequalities_601721 (k : ℝ) :
    (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → k * a * b * c / (a + b + c) ≤ (a + b)^2 + (a + b + 4 * c)^2) ↔
    k ≤ 100 := by 
  constructor
  · -- Forward direction: prove k ≤ 100 from the inequality
    intro h
    have h1 := h 2 2 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h1 
    nlinarith 
  · -- Backward direction: prove the inequality from k ≤ 100
    intro hk a b c ha hb hc
    have h1 : k * a * b * c / (a + b + c) ≤ 100 * a * b * c / (a + b + c) := by
      have h2 : k ≤ 100 := by linarith 
      have h3 : a * b * c > 0 := by 
        positivity 
      have h4 : (a + b + c) > 0 := by positivity
      have h5 : k * a * b * c ≤ 100 * a * b * c := by 
        nlinarith [h2, show a * b * c ≥ 0 by positivity] 
      have h6 : k * a * b * c / (a + b + c) ≤ 100 * a * b * c / (a + b + c) := by 
        apply (div_le_div_right (by positivity)).mpr 
        linarith 
      linarith
    have h2 : 100 * a * b * c / (a + b + c) ≤ (a + b) ^ 2 + (a + b + 4 * c) ^ 2 := by 
      have h3 : 0 < a + b + c := by positivity 
      have h4 : 100 * a * b * c ≤ ((a + b) ^ 2 + (a + b + 4 * c) ^ 2) * (a + b + c) := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * c), sq_nonneg (a - b), sq_nonneg (a + b - 4 * c), sq_nonneg (b - 2 * c), sq_nonneg (a - 2 * c), sq_nonneg (c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a + b - 2 * c), sq_nonneg (a^2 + b^2 - c^2)]
      have h5 : 100 * a * b * c / (a + b + c) ≤ (a + b) ^ 2 + (a + b + 4 * c) ^ 2 := by
        have h6 : 0 < a + b + c := by positivity
        apply (div_le_iff₀ (by positivity)).mpr 
        linarith [h4]
      linarith 
    linarith [h1, h2]