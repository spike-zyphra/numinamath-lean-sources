import Mathlib

theorem algebra_311169 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : (3 : ℝ)^a = 2007) (h2 : (223 : ℝ)^b = 2007) :
    1 / a + 1 / (2 * b) = 1 / 2 := by

  have h3 : a * (Real.log 3) = Real.log 2007 := by
    have h5 : (3 : ℝ) ^ a = 2007 := h1
    have h6 : Real.log ((3 : ℝ) ^ a) = Real.log 2007 := by
      rw [h5]
    have h7 : Real.log ((3 : ℝ) ^ a) = a * (Real.log 3) := by
      rw [Real.log_rpow]
      all_goals linarith
    linarith

  have h4 : b * (Real.log 223) = Real.log 2007 := by
    have h3_ : (223 : ℝ) ^ b = 2007 := h2
    have h4_ : Real.log ((223 : ℝ) ^ b) = Real.log 2007 := by
      rw [h3_]
    have h5_ : Real.log ((223 : ℝ) ^ b) = b * (Real.log 223) := by
      rw [Real.log_rpow]
      all_goals linarith
    linarith

  have h5 : Real.log 2007 = 2 * (Real.log 3) + (Real.log 223) := by
    calc
      Real.log 2007 = Real.log (3 ^ 2 * (223 : ℝ)) := by
        norm_num
      _ = Real.log (3 ^ 2) + Real.log (223 : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = 2 * (Real.log 3) + Real.log (223 : ℝ) := by 
        simp [Real.log_pow]
        all_goals linarith
      _ = 2 * (Real.log 3) + (Real.log 223) := by
        norm_num

  have eq1 : a * (Real.log 3) = 2 * (Real.log 3) + (Real.log 223) := by
    linarith [h3, h5]

  have eq2 : b * (Real.log 223) = 2 * (Real.log 3) + (Real.log 223) := by
    linarith [h4, h5]

  have h6 : Real.log 3 > 0 := by
    apply Real.log_pos
    norm_num

  have h7 : Real.log 223 > 0 := by
    apply Real.log_pos
    norm_num

  have h10 : (b - 1) * (a - 2) = 2 := by
    have eq3 : (a - 2) * (Real.log 3) = (Real.log 223) := by
      linarith [eq1]
    have eq4 : (b - 1) * (Real.log 223) = 2 * (Real.log 3) := by
      linarith [eq2]
    have h9 : Real.log 3 ≠ 0 := by
      linarith [h6]
    have h12 : (b - 1) * ((a - 2) * (Real.log 3)) = 2 * (Real.log 3) := by
      have h13 : Real.log 223 = (a - 2) * (Real.log 3) := by
        linarith [eq3]
      rw [h13] at eq4
      linarith
    apply (mul_left_inj' h9).mp
    linarith [h12, h9]

  have h14 : 1 / a + 1 / (2 * b) = 1 / 2 := by
    have h15 : a ≠ 0 := by linarith
    have h16 : b ≠ 0 := by linarith
    field_simp
    <;> nlinarith [sq_pos_of_pos h6, sq_pos_of_pos h7, mul_pos h6 h7, sq_nonneg (a - 4), sq_nonneg (b - 2), mul_pos ha hb, h10]

  exact h14