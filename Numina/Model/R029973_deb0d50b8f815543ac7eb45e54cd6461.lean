import Mathlib

theorem inequalities_102694 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (a * b / ((a + c) * (b + c))) +
    Real.sqrt (b * c / ((b + a) * (c + a))) +
    Real.sqrt (c * a / ((c + b) * (b + a))) ≤ 3 / 2 := by

  have h10 : Real.sqrt (a * b / ((a + c) * (b + c))) ≤ (a * (b + c) + b * (a + c)) / (2 * (a + c) * (b + c)) := by
    have h11 : (Real.sqrt (a * b / ((a + c) * (b + c)))) ^ 2 ≤ ((a * (b + c) + b * (a + c)) / (2 * (a + c) * (b + c))) ^ 2 := by
      have h12 : (Real.sqrt (a * b / ((a + c) * (b + c)))) ^ 2 = a * b / ((a + c) * (b + c)) := by
        rw [Real.sq_sqrt]
        positivity
      have h13 : ((a * (b + c) + b * (a + c)) / (2 * (a + c) * (b + c))) ^ 2 ≥ a * b / ((a + c) * (b + c)) := by
        have h14 : 0 < (a + c) * (b + c) := by positivity
        suffices 4 * a * b * ((a + c) * (b + c)) ≤ (a * (b + c) + b * (a + c)) ^ 2 by
          have h15 : ((a * (b + c) + b * (a + c)) / (2 * (a + c) * (b + c))) ^ 2 = (a * (b + c) + b * (a + c)) ^ 2 / (4 * ((a + c) * (b + c)) ^ 2) := by
            field_simp
            ring
          rw [h15]
          have h16 : a * b / ((a + c) * (b + c)) = (4 * a * b * ((a + c) * (b + c))) / (4 * ((a + c) * (b + c)) ^ 2) := by
            field_simp
            ring
          rw [h16]
          apply (div_le_div_right (by positivity)).mpr
          nlinarith
        nlinarith [sq_nonneg (a * (b + c) - b * (a + c)), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      nlinarith
    have h17 : ((a * (b + c) + b * (a + c)) / (2 * (a + c) * (b + c))) ≥ 0 := by positivity
    have h18 : Real.sqrt (a * b / ((a + c) * (b + c))) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (a * b / ((a + c) * (b + c))), show (a * (b + c) + b * (a + c)) / (2 * (a + c) * (b + c)) ≥ 0 by positivity]

  have h11 : Real.sqrt (b * c / ((b + a) * (c + a))) ≤ (b * (c + a) + c * (b + a)) / (2 * (b + a) * (c + a)) := by
    have h12 : (Real.sqrt (b * c / ((b + a) * (c + a)))) ^ 2 ≤ ((b * (c + a) + c * (b + a)) / (2 * (b + a) * (c + a))) ^ 2 := by
      have h13 : (Real.sqrt (b * c / ((b + a) * (c + a)))) ^ 2 = b * c / ((b + a) * (c + a)) := by
        rw [Real.sq_sqrt]
        positivity
      have h14 : ((b * (c + a) + c * (b + a)) / (2 * (b + a) * (c + a))) ^ 2 ≥ b * c / ((b + a) * (c + a)) := by
        have h15 : 0 < (b + a) * (c + a) := by positivity
        suffices 4 * b * c * ((b + a) * (c + a)) ≤ (b * (c + a) + c * (b + a)) ^ 2 by
          have h16 : ((b * (c + a) + c * (b + a)) / (2 * (b + a) * (c + a))) ^ 2 = (b * (c + a) + c * (b + a)) ^ 2 / (4 * ((b + a) * (c + a)) ^ 2) := by
            field_simp
            ring
          rw [h16]
          have h17 : b * c / ((b + a) * (c + a)) = (4 * b * c * ((b + a) * (c + a))) / (4 * ((b + a) * (c + a)) ^ 2) := by
            field_simp
            ring
          rw [h17]
          apply (div_le_div_right (by positivity)).mpr
          nlinarith
        nlinarith [sq_nonneg (b * (c + a) - c * (b + a)), sq_nonneg (b - c), sq_nonneg (b - a), sq_nonneg (c - a), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      nlinarith
    have h18 : ((b * (c + a) + c * (b + a)) / (2 * (b + a) * (c + a))) ≥ 0 := by positivity
    have h19 : Real.sqrt (b * c / ((b + a) * (c + a))) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (b * c / ((b + a) * (c + a))), show (b * (c + a) + c * (b + a)) / (2 * (b + a) * (c + a)) ≥ 0 by positivity]

  have h12 : Real.sqrt (c * a / ((c + b) * (b + a))) ≤ (c * (a + b) + a * (c + b)) / (2 * (c + b) * (b + a)) := by
    have h13 : (Real.sqrt (c * a / ((c + b) * (b + a)))) ^ 2 ≤ ((c * (a + b) + a * (c + b)) / (2 * (c + b) * (b + a))) ^ 2 := by
      have h14 : (Real.sqrt (c * a / ((c + b) * (b + a)))) ^ 2 = c * a / ((c + b) * (b + a)) := by
        rw [Real.sq_sqrt]
        positivity
      have h15 : ((c * (a + b) + a * (c + b)) / (2 * (c + b) * (b + a))) ^ 2 ≥ c * a / ((c + b) * (b + a)) := by
        have h16 : 0 < (c + b) * (b + a) := by positivity
        suffices 4 * c * a * ((c + b) * (b + a)) ≤ (c * (a + b) + a * (c + b)) ^ 2 by
          have h17 : ((c * (a + b) + a * (c + b)) / (2 * (c + b) * (b + a))) ^ 2 = (c * (a + b) + a * (c + b)) ^ 2 / (4 * ((c + b) * (b + a)) ^ 2) := by
            field_simp
            ring
          rw [h17]
          have h18 : c * a / ((c + b) * (b + a)) = (4 * c * a * ((c + b) * (b + a))) / (4 * ((c + b) * (b + a)) ^ 2) := by
            field_simp
            ring
          rw [h18]
          apply (div_le_div_right (by positivity)).mpr
          nlinarith
        nlinarith [sq_nonneg (c * (a + b) - a * (c + b)), sq_nonneg (c - a), sq_nonneg (c - b), sq_nonneg (a - b), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      nlinarith
    have h19 : ((c * (a + b) + a * (c + b)) / (2 * (c + b) * (b + a))) ≥ 0 := by positivity
    have h20 : Real.sqrt (c * a / ((c + b) * (b + a))) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (c * a / ((c + b) * (b + a))), show (c * (a + b) + a * (c + b)) / (2 * (c + b) * (b + a)) ≥ 0 by positivity]

  have h14 : Real.sqrt (a * b / ((a + c) * (b + c))) + Real.sqrt (b * c / ((b + a) * (c + a))) + Real.sqrt (c * a / ((c + b) * (b + a))) ≤ (a * (b + c) + b * (a + c)) / (2 * (a + c) * (b + c)) + (b * (c + a) + c * (b + a)) / (2 * (b + a) * (c + a)) + (c * (a + b) + a * (c + b)) / (2 * (c + b) * (b + a)) := by 
    linarith [h10, h11, h12]

  have h15 : (a * (b + c) + b * (a + c)) / (2 * (a + c) * (b + c)) + (b * (c + a) + c * (b + a)) / (2 * (b + a) * (c + a)) + (c * (a + b) + a * (c + b)) / (2 * (c + b) * (b + a)) = 3 / 2 := by
    field_simp
    ring

  linarith [h14, h15]