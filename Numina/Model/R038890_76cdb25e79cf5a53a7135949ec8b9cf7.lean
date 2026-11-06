import Mathlib

theorem inequalities_33141 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / (1 + a + b) ≤ a / (1 + a) + b / (1 + b) ∧
    a / (1 + a) + b / (1 + b) ≤ 2 * (a + b) / (2 + a + b) := by
  constructor
  · -- Prove that (a + b) / (1 + a + b) ≤ a / (1 + a) + b / (1 + b)
    have h1 : 0 < 1 + a + b := by
      linarith
    have h2 : 0 < 1 + a := by
      linarith
    have h3 : 0 < 1 + b := by
      linarith
    have h4 : (a + b) / (1 + a + b) - (a / (1 + a) + b / (1 + b)) ≤ 0 := by
      have pos1 : (1 + a + b) > 0 := by linarith
      have pos2 : (1 + a) > 0 := by linarith
      have pos3 : (1 + b) > 0 := by linarith
      have h5 : (a + b) / (1 + a + b) - (a / (1 + a) + b / (1 + b)) =
          ((a + b) * (1 + a) * (1 + b) - (a * (1 + b) * (1 + a + b) + b * (1 + a) * (1 + a + b))) / ((1 + a + b) * (1 + a) * (1 + b)) := by
        field_simp
        <;> ring
      rw [h5]
      apply div_nonpos_of_nonpos_of_nonneg
      · 
        nlinarith [sq_nonneg (a * b), sq_nonneg (a - b), 
          sq_nonneg (a), sq_nonneg (b), 
            mul_nonneg ha hb, 
              mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) ha, 
                mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hb, 
                  mul_nonneg ha (show (0 : ℝ) ≤ 1 by norm_num), 
                    mul_nonneg hb (show (0 : ℝ) ≤ 1 by norm_num)]
      · 
        positivity
    linarith
  · -- Prove that a / (1 + a) + b / (1 + b) ≤ 2 * (a + b) / (2 + a + b)
    have h1 : 0 < 2 + a + b := by
      linarith
    have h2 : 0 < 1 + a := by
      linarith
    have h3 : 0 < 1 + b := by
      linarith
    have h5 : (a / (1 + a) + b / (1 + b)) - (2 * (a + b) / (2 + a + b)) ≤ 0 := by
      have pos1 : (1 + a) > 0 := by linarith
      have pos2 : (1 + b) > 0 := by linarith
      have pos3 : (2 + a + b) > 0 := by linarith
      have h6 : (a / (1 + a) + b / (1 + b)) - (2 * (a + b) / (2 + a + b)) =
          ( (a * (2 + a + b) * (1 + b) + b * (2 + a + b) * (1 + a) - 2 * (a + b) * (1 + a) * (1 + b) ) ) / ( (1 + a) * (1 + b) * (2 + a + b) ) := by
        field_simp
        <;> ring
      rw [h6]
      apply div_nonpos_of_nonpos_of_nonneg
      · 
        nlinarith [sq_nonneg (a * b), sq_nonneg (a - b), 
          sq_nonneg (a), sq_nonneg (b), 
            mul_nonneg ha hb, 
              mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) ha, 
                mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hb, 
                  mul_nonneg ha (show (0 : ℝ) ≤ 1 by norm_num), 
                    mul_nonneg hb (show (0 : ℝ) ≤ 1 by norm_num)]
      · 
        positivity
    linarith