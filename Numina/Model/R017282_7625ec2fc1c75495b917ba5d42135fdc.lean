import Mathlib

open Real

theorem inequalities_289333 (a b c d : ℝ) :
    sqrt (a^2 + b^2) * sqrt (c^2 + d^2) ≥ a * c + b * d := by
  have h1 : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have h2 : 0 ≤ c ^ 2 + d ^ 2 := by positivity
  have h3 : sqrt (a ^ 2 + b ^ 2) ≥ 0 := by positivity
  have h4 : sqrt (c ^ 2 + d ^ 2) ≥ 0 := by positivity
  have h5 : sqrt (a ^ 2 + b ^ 2) * sqrt (c ^ 2 + d ^ 2) = sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) := by 
    rw [← sqrt_mul (by positivity)]
  have h6 : sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) ≥ (a * c + b * d) := by
    have h7 : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
      nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (a * c - b * d), sq_nonneg (a * d + b * c), sq_nonneg (a * c + b * d), mul_self_nonneg (a - c), mul_self_nonneg (a - d), mul_self_nonneg (b - c), mul_self_nonneg (b - d)]
    have h8 : (a * c + b * d : ℝ) ≤ sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) := by
      have h9 : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
        nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (a * c - b * d), sq_nonneg (a * d + b * c), sq_nonneg (a * c + b * d), mul_self_nonneg (a - c), mul_self_nonneg (a - d), mul_self_nonneg (b - c), mul_self_nonneg (b - d)]
      have h10 : (sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2))) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by 
        rw [Real.sq_sqrt]
        positivity
      nlinarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)), sq_nonneg ((sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) ) - (a * c + b * d)), sq_nonneg ((sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)))), Real.sqrt_nonneg ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2))]
    linarith
  linarith [h5, h6]