import Mathlib

open Real

theorem inequalities_112388 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    sqrt (a^2 - a * b + b^2) + sqrt (b^2 - b * c + c^2) >
    sqrt (c^2 - c * a + a^2) ∧
    sqrt (a^2 + a * b + b^2) + sqrt (b^2 + b * c + c^2) >
    sqrt (c^2 + c * a + a^2) := by 
  constructor
  · -- First inequality: sqrt (a^2 - a * b + b^2) + sqrt (b^2 - b * c + c^2) > sqrt (c^2 - c * a + a^2)
    have h1 : 0 < a ^ 2 - a * b + b ^ 2 := by
      nlinarith [sq_nonneg (a - b), mul_pos ha hb]
    have h2 : 0 < b ^ 2 - b * c + c ^ 2 := by
      nlinarith [sq_nonneg (b - c), mul_pos hb hc]
    have h3 : 0 < c ^ 2 - c * a + a ^ 2 := by
      nlinarith [sq_nonneg (c - a), mul_pos ha hc]
    have h4 : sqrt (a^2 - a * b + b^2) + sqrt (b^2 - b * c + c^2) > sqrt (c^2 - c * a + a^2) := by
      have h7 : (sqrt (a^2 - a * b + b^2) + sqrt (b^2 - b * c + c^2)) ^ 2 > (sqrt (c^2 - c * a + a^2)) ^ 2 := by
        have h8 : (sqrt (a^2 - a * b + b^2) + sqrt (b^2 - b * c + c^2)) ^ 2 =
            (sqrt (a^2 - a * b + b^2)) ^ 2 + (sqrt (b^2 - b * c + c^2)) ^ 2 + 2 * (sqrt (a^2 - a * b + b^2) * sqrt (b^2 - b * c + c^2)) := by ring
        have h9 : (sqrt (c^2 - c * a + a^2)) ^ 2 = c^2 - c * a + a^2 := by
          rw [Real.sq_sqrt]
          nlinarith
        have h10 : (sqrt (a^2 - a * b + b^2)) ^ 2 = a^2 - a * b + b^2 := by
          rw [Real.sq_sqrt]
          nlinarith
        have h11 : (sqrt (b^2 - b * c + c^2)) ^ 2 = b^2 - b * c + c^2 := by
          rw [Real.sq_sqrt]
          nlinarith
        rw [h8, h10, h11, h9]
        have h100 : sqrt (a^2 - a * b + b^2) * sqrt (b^2 - b * c + c^2) ≥ 0 := by
          positivity
        nlinarith [Real.sqrt_nonneg (a ^ 2 - a * b + b ^ 2), Real.sqrt_nonneg (b ^ 2 - b * c + c ^ 2), Real.sqrt_nonneg (c ^ 2 - c * a + a ^ 2),
          mul_nonneg (Real.sqrt_nonneg (a ^ 2 - a * b + b ^ 2)) (Real.sqrt_nonneg (b ^ 2 - b * c + c ^ 2)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have h100 : (sqrt (a^2 - a * b + b^2) + sqrt (b^2 - b * c + c^2)) ≥ 0 := by positivity
      have h101 : sqrt (c^2 - c * a + a^2) ≥ 0 := Real.sqrt_nonneg (c^2 - c * a + a^2)
      nlinarith [Real.sqrt_nonneg (a ^ 2 - a * b + b ^ 2), Real.sqrt_nonneg (b ^ 2 - b * c + c ^ 2), Real.sqrt_nonneg (c ^ 2 - c * a + a ^ 2), h7]
    exact h4
  · -- Second inequality: sqrt (a^2 + a * b + b^2) + sqrt (b^2 + b * c + c^2) > sqrt (c^2 + c * a + a^2)
    have h100 : 0 < a ^ 2 + a * b + b ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]
    have h101 : 0 < b ^ 2 + b * c + c ^ 2 := by
      nlinarith [sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos hb hc]
    have h102 : 0 < c ^ 2 + c * a + a ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hc, mul_pos ha hc]
    have h4 : sqrt (a^2 + a * b + b^2) + sqrt (b^2 + b * c + c^2) > sqrt (c^2 + c * a + a^2) := by
      have h7 : (sqrt (a^2 + a * b + b^2) + sqrt (b^2 + b * c + c^2)) ^ 2 > (sqrt (c^2 + c * a + a^2)) ^ 2 := by
        have h8 : (sqrt (a^2 + a * b + b^2) + sqrt (b^2 + b * c + c^2)) ^ 2 =
            (sqrt (a^2 + a * b + b^2)) ^ 2 + (sqrt (b^2 + b * c + c^2)) ^ 2 + 2 * (sqrt (a^2 + a * b + b^2) * sqrt (b^2 + b * c + c^2)) := by ring
        have h9 : (sqrt (c^2 + c * a + a^2)) ^ 2 = c^2 + c * a + a^2 := by
          rw [Real.sq_sqrt]
          nlinarith
        have h10 : (sqrt (a^2 + a * b + b^2)) ^ 2 = a^2 + a * b + b^2 := by
          rw [Real.sq_sqrt]
          nlinarith
        have h11 : (sqrt (b^2 + b * c + c^2)) ^ 2 = b^2 + b * c + c^2 := by
          rw [Real.sq_sqrt]
          nlinarith
        rw [h8, h10, h11, h9]
        have h100 : sqrt (a^2 + a * b + b^2) * sqrt (b^2 + b * c + c^2) ≥ 0 := by
          positivity
        nlinarith [Real.sqrt_nonneg (a ^ 2 + a * b + b ^ 2), Real.sqrt_nonneg (b ^ 2 + b * c + c ^ 2), Real.sqrt_nonneg (c ^ 2 + c * a + a ^ 2), 
          mul_nonneg (Real.sqrt_nonneg (a ^ 2 + a * b + b ^ 2)) (Real.sqrt_nonneg (b ^ 2 + b * c + c ^ 2)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have h1000 : (sqrt (a^2 + a * b + b^2) + sqrt (b^2 + b * c + c^2)) ≥ 0 := by positivity
      have h1001 : sqrt (c^2 + c * a + a^2) ≥ 0 := Real.sqrt_nonneg (c^2 + c * a + a^2)
      nlinarith [Real.sqrt_nonneg (a ^ 2 + a * b + b ^ 2), Real.sqrt_nonneg (b ^ 2 + b * c + c ^ 2), Real.sqrt_nonneg (c ^ 2 + c * a + a ^ 2), h7]
    exact h4