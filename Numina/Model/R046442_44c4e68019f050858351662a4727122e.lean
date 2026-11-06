import Mathlib
theorem inequalities_164111 (m n : ℕ) (hmn : m < n) : m ^ 2 + √(m ^ 2 + m) < n ^ 2 - √(n ^ 2 - n):= by
  have h1 : m < n := hmn
  have h2 : m ^ 2 + (m : ℝ) ≤ (m + 1 : ℝ) ^ 2 := by 
    nlinarith [sq_nonneg ((m : ℝ) + 1)]
  have h3 : √(m ^ 2 + (m : ℝ)) ≤ (m + 1 : ℝ) := by
    have h4 : m ^ 2 + (m : ℝ) ≤ ((m + 1 : ℝ) ) ^ 2 := h2
    have h5 : √(m ^ 2 + (m : ℝ)) ≤ √(((m + 1 : ℝ) ) ^ 2) := Real.sqrt_le_sqrt (h4)
    have h6 : √(((m + 1 : ℝ) ) ^ 2) = (m + 1 : ℝ) := Real.sqrt_sq (show 0 ≤ (m + 1 : ℝ) by positivity)
    linarith [h5, h6]
  have h8 : (n : ℝ) ≥ (1 : ℝ) := by
    have hn : n > 0 := by
      linarith [show m ≥ 0 by omega, hmn]
    have h9 : n ≥ 1 := by
      omega
    exact_mod_cast h9
  have h9 : √(n ^ 2 - (n : ℝ)) ≤ (n : ℝ) := by
    have h10 : (n ^ 2 - (n : ℝ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith [show (n : ℝ) ≥ (1 : ℝ) from h8]
    have h11 : √(n ^ 2 - (n : ℝ)) ≤ √((n : ℝ) ^ 2) := Real.sqrt_le_sqrt (h10)
    have h12 : √((n : ℝ) ^ 2) = (n : ℝ) := Real.sqrt_sq (show 0 ≤ (n : ℝ) by positivity)
    linarith [h11, h12]
  by_cases h11 : n > m + 1
  · -- Case n > m + 1
    have h12 : (n : ℝ) ≥ (m + 2 : ℝ) := by
      have h11' : n ≥ m + 2 := by
        omega
      exact_mod_cast h11'
    nlinarith [h3, Real.sqrt_nonneg (m ^ 2 + (m : ℝ)), Real.sqrt_nonneg (n ^ 2 - (n : ℝ)), sq_nonneg ((n : ℝ) - (m + 1 : ℝ)), sq_nonneg ((m : ℝ) + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (m ^ 2 + (m : ℝ)) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (n ^ 2 - (n : ℝ)) by nlinarith), Real.sqrt_nonneg (m ^ 2 + (m : ℝ)), Real.sqrt_nonneg (n ^ 2 - (n : ℝ))]
  · -- Case n = m + 1
    have h11' : n = m + 1 := by 
      omega
    rw [show (n : ℝ) = (m + 1 : ℝ) by exact_mod_cast h11']
    have h17 : ((m + 1 : ℝ) ) ^ 2 - √((m + 1 : ℝ) ^ 2 - (m + 1 : ℝ)) = (m + 1 : ℝ) ^ 2 - √(m ^ 2 + (m : ℝ)) := by
      have h18 : (m + 1 : ℝ) ^ 2 - (m + 1 : ℝ) = m ^ 2 + (m : ℝ) := by
        nlinarith
      have h19 : √((m + 1 : ℝ) ^ 2 - (m + 1 : ℝ)) = √(m ^ 2 + (m : ℝ)) := by 
        rw [h18]
      rw [h19]
    have h18 : (m : ℝ) ^ 2 + √(m ^ 2 + (m : ℝ)) < (m + 1 : ℝ) ^ 2 - √(m ^ 2 + (m : ℝ)) := by
      have h19 : √(m ^ 2 + (m : ℝ)) ≥ 0 := by positivity
      have h16 : 2 * √(m ^ 2 + (m : ℝ)) < (2 * (m : ℝ) + 1) := by
        have h17 : (√(m ^ 2 + (m : ℝ)) ) ^ 2 < (( (2 * (m : ℝ) + 1) / 2 ) ) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (m ^ 2 + (m : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (m ^ 2 + (m : ℝ)) by positivity), sq_nonneg ( (√(m ^ 2 + (m : ℝ)) ) - ( (2 * (m : ℝ) + 1 ) / 2 ) ) ]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (m ^ 2 + (m : ℝ)) by positivity), Real.sqrt_nonneg (m ^ 2 + (m : ℝ)), sq_nonneg ( (√(m ^ 2 + (m : ℝ)) ) - ( (2 * (m : ℝ) + 1 ) / 2 ) ) ]
      linarith
    rw [h17]
    linarith [h18]