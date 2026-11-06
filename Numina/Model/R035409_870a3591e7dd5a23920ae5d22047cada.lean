import Mathlib

theorem algebra_215541 (a b c : ℝ) (ha : a ≠ 0) (h : (b + c) / a ≤ -1) :
    ∃ x, a * x ^ 2 + b * x + c = 0 := by
  by_cases h1 : a > 0
  · -- If a > 0, then (b + c) / a ≤ -1 implies b + c ≤ -a
    have h2 : b + c ≤ -a := by
      apply (div_le_iff₀ h1).mp at h
      linarith
    have h3 : b ^ 2 ≥ 4 * a * c := by
      nlinarith [sq_nonneg (b + c + a), sq_nonneg (c + a), sq_nonneg (b + a), sq_nonneg (c - a), sq_pos_of_pos h1]
    have h4 : ∃ x, a * x ^ 2 + b * x + c = 0 := by
      have h5 : b ^ 2 - 4 * a * c ≥ 0 := by linarith
      use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
      field_simp
      nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), Real.sq_sqrt (show (b ^ 2 - 4 * a * c) ≥ 0 by linarith)]
    exact h4
  · -- If a ≤ 0, since a ≠ 0, we have a < 0
    have h1' : a < 0 := by
      by_contra h1
      push_neg at h1
      have h2 : a = 0 := by linarith
      contradiction
    have h2 : b + c ≥ -a := by
      have h3 : a < 0 := h1'
      apply (div_le_iff_of_neg' (by linarith)).mp at h
      linarith
    have h3 : b ^ 2 ≥ 4 * a * c := by
      nlinarith [sq_nonneg (b + c + a), sq_nonneg (b - (-c - a)), sq_nonneg (c + a), sq_nonneg (c - a), sq_pos_of_neg h1']
    have h4 : ∃ x, a * x ^ 2 + b * x + c = 0 := by
      have h5 : b ^ 2 - 4 * a * c ≥ 0 := by linarith
      use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
      field_simp
      nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), Real.sq_sqrt (show (b ^ 2 - 4 * a * c) ≥ 0 by linarith)]
    exact h4