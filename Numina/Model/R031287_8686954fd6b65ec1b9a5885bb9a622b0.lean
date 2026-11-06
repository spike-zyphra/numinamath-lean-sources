import Mathlib

  theorem algebra_21014 {F : ℝ → ℝ → ℝ → ℝ → ℝ} (hF : ∀ a b c d, F a b c d = a ^ b + c * d) :
    F 6 b 4 3 = 48 ↔ b = 2 := by
  constructor
  · -- Forward direction: If F(6, b, 4, 3) = 48, then b = 2.
    intro h
    have h1 : (6 : ℝ) ^ b + (4 : ℝ) * (3 : ℝ) = 48 := by
      rw [hF] at h
      linarith
    have h2 : (6 : ℝ) ^ b = 36 := by
      nlinarith
    have h3 : b = (2 : ℝ) := by
      have h4 : (6 : ℝ) ^ b = (6 : ℝ) ^ (2 : ℝ) := by
        rw [h2]
        all_goals norm_num
      have h5 : b = (2 : ℝ) := by 
        have h7 : (6 : ℝ) ^ b = (6 : ℝ) ^ (2 : ℝ) := h4
        have h7_left : Real.logb (6 : ℝ) ((6 : ℝ) ^ b) = b := by
          rw [Real.logb_rpow]
          all_goals linarith
        have h7_right : Real.logb (6 : ℝ) ((6 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by
          rw [Real.logb_rpow]
          all_goals norm_num
        have h7' : Real.logb (6 : ℝ) ((6 : ℝ) ^ b) = Real.logb (6 : ℝ) ((6 : ℝ) ^ (2 : ℝ)) := by 
          rw [show (6 : ℝ) ^ b = (6 : ℝ) ^ (2 : ℝ) by linarith [h7]]
        linarith [h7_left, h7_right, h7']
      linarith
    linarith
  · -- Backward direction: If b = 2, then F(6, b, 4, 3) = 48.
    intro h
    rw [hF]
    rw [h]
    norm_num