import Mathlib
open Real

theorem algebra_4441 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ((a * sqrt b + b * sqrt a) / (sqrt a + sqrt b)) *
    ((sqrt b) / (sqrt (a * b) - b) - (1 / (sqrt a + sqrt b))) /
    (sqrt b / (a - b)) = 2 * sqrt (a * b) := by
  have hab1 : sqrt (a * b) = sqrt a * sqrt b := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  have h1 : (a * sqrt b + b * sqrt a) / (sqrt a + sqrt b) = sqrt a * sqrt b := by
    have hne : sqrt a + sqrt b ≠ 0 := by
      have h1 : sqrt a > 0 := by positivity
      have h2 : sqrt b > 0 := by positivity
      linarith
    field_simp [hne]
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith)]
  have h2 : (sqrt b / (sqrt (a * b) - b) - (1 / (sqrt a + sqrt b))) = 
      (2 * sqrt b / (a - b)) := by
    rw [hab1]
    have hne1 : sqrt a * sqrt b - b ≠ 0 := by
      by_contra h
      have : sqrt a * sqrt b = b := by linarith
      have h3 : sqrt a ^ 2 * sqrt b ^ 2 = b ^ 2 := by
        calc
          sqrt a ^ 2 * sqrt b ^ 2 = (sqrt a * sqrt b) ^ 2 := by ring
          _ = b ^ 2 := by
            have h4 : sqrt a * sqrt b = b := by linarith
            rw [h4]
            all_goals nlinarith
      have h4 : sqrt a ^ 2 = a := Real.sq_sqrt (show 0 ≤ a by linarith)
      have h5 : sqrt b ^ 2 = b := Real.sq_sqrt (show 0 ≤ b by linarith)
      rw [h4, h5] at h3
      have h6 : a * b = b ^ 2 := by nlinarith
      have h7 : a = b := by
        nlinarith [show b > 0 by linarith]
      have h8 : a = b := by
        nlinarith
      tauto
    have hne2 : sqrt a + sqrt b ≠ 0 := by
      have h1 : sqrt a > 0 := by positivity
      have h2 : sqrt b > 0 := by positivity
      linarith
    have hne3 : a - b ≠ 0 := by
      intro h
      apply hab
      linarith
    field_simp [hne1, hne2, hne3, Real.sqrt_pos.2 (show 0 < b by linarith), Real.sqrt_pos.2 (show 0 < a by linarith)]
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith), sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt b - 0), sq_nonneg (sqrt a - 0)]
  have hne3 : a - b ≠ 0 := by
    intro h
    apply hab
    linarith
  rw [h1, h2]
  field_simp [Real.sqrt_pos.2 (show 0 < b by linarith), Real.sqrt_pos.2 (show 0 < a by linarith), hne3, Real.sqrt_nonneg (a * b), sq_nonneg (sqrt a - sqrt b)]
  <;> 
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), sq_nonneg (sqrt a - sqrt b), Real.sq_sqrt (show 0 ≤ a * b by positivity)]