import Mathlib

theorem algebra_151928 (a b : ℝ) :
    IsLeast {z : ℝ | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z = x + y + Real.sqrt ((a - x) ^ 2 + (b - y) ^ 2)} (Real.sqrt (a ^ 2 + b ^ 2)) := by
  constructor
  · -- Show that `Real.sqrt (a ^ 2 + b ^ 2)` is in the set.
    use 0, 0
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show that `Real.sqrt (a - 0) ^ 2 + (b - 0) ^ 2 = Real.sqrt (a ^ 2 + b ^ 2)`
      have h1 : Real.sqrt ((a - (0 : ℝ)) ^ 2 + (b - (0 : ℝ)) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) := by
        ring_nf
      linarith [h1]
  · -- Show it's a lower bound
    intro z hz
    rcases hz with ⟨x, y, hx, hy, hz⟩
    have h1 : Real.sqrt (a ^ 2 + b ^ 2) ≥ 0 := by positivity
    have h4 : x + y + Real.sqrt ((a - x) ^ 2 + (b - y) ^ 2) ≥ Real.sqrt (a ^ 2 + b ^ 2) := by
      have h5 : x + y + Real.sqrt ((a - x) ^ 2 + (b - y) ^ 2) ≥ Real.sqrt (a ^ 2 + b ^ 2) := by
        have h8 : (Real.sqrt ((a - x) ^ 2 + (b - y) ^ 2) + x + y) ^ 2 ≥ (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by
          have h9 : (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (show (a ^ 2 + b ^ 2 : ℝ) ≥ 0 by positivity)
          have h12 : (Real.sqrt ((a - x) ^ 2 + (b - y) ^ 2)) ^ 2 = (a - x) ^ 2 + (b - y) ^ 2 := Real.sq_sqrt (show ((a - x) ^ 2 + (b - y) ^ 2 : ℝ) ≥ 0 by positivity)
          nlinarith [Real.sqrt_nonneg ((a - x) ^ 2 + (b - y) ^ 2), Real.sqrt_nonneg (a ^ 2 + b ^ 2), 
            mul_nonneg (show (0 : ℝ) ≤ x by linarith [hx]) (show (0 : ℝ) ≤ y by linarith [hy]), 
            mul_nonneg (Real.sqrt_nonneg ((a - x) ^ 2 + (b - y) ^ 2)) (show (0 : ℝ) ≤ x by linarith [hx]), 
            mul_nonneg (Real.sqrt_nonneg ((a - x) ^ 2 + (b - y) ^ 2)) (show (0 : ℝ) ≤ y by linarith [hy]), 
            sq_nonneg (Real.sqrt ((a - x) ^ 2 + (b - y) ^ 2) - x - y), 
            sq_nonneg (x * b - y * a), 
            sq_nonneg (Real.sqrt (a ^ 2 + b ^ 2) - (Real.sqrt ((a - x) ^ 2 + (b - y) ^ 2) + x + y)), Real.sqrt_nonneg (a ^ 2 + b ^ 2)]
        have h9 : Real.sqrt ((a - x) ^ 2 + (b - y) ^ 2) + x + y ≥ 0 := by
          positivity
        have h3 : Real.sqrt (a ^ 2 + b ^ 2) ≥ 0 := Real.sqrt_nonneg (a ^ 2 + b ^ 2)
        nlinarith [h8, Real.sqrt_nonneg (a ^ 2 + b ^ 2)]
      linarith 
    linarith [hz, h4]