import Mathlib

theorem number_theory_293541 (n : ℝ) (hn : n > 0) :
    133^5 + 110^5 + 84^5 + 27^5 = n^5 ↔ n = 144 := by
  constructor
  · -- Assume 133^5 + 110^5 + 84^5 + 27^5 = n^5, prove n = 144
    intro h
    have h1 : n^5 = (133 : ℝ) ^ 5 + (110 : ℝ) ^ 5 + (84 : ℝ) ^ 5 + (27 : ℝ) ^ 5 := by 
      linarith
    have h2 : n^5 = (144 : ℝ) ^ 5 := by
      norm_num [h1]
    -- Since n^5 = 144^5 and n > 0, we can take the positive real root
    have h3 : n = (144 : ℝ) := by
      have h4 : n^5 - (144 : ℝ) ^ 5 = 0 := by 
        linarith
      have h5 : (n - (144 : ℝ)) * (n^4 + n^3 * (144 : ℝ) + n^2 * (144 : ℝ)^2 + n * (144 : ℝ)^3 + (144 : ℝ)^4) = 0 := by
        ring_nf at h4 ⊢
        <;> nlinarith
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- First factor is zero: n - 144 = 0, so n = 144
        linarith
      · -- Show the second factor cannot be zero since n > 0
        have h8 : n^4 + n^3 * (144 : ℝ) + n^2 * (144 : ℝ)^2 + n * (144 : ℝ)^3 + (144 : ℝ)^4 > 0 := by
          nlinarith [sq_nonneg (n^2), sq_nonneg (n + (144 : ℝ)), sq_nonneg (n - (144 : ℝ)), sq_nonneg (n + 2 * (144 : ℝ)), sq_nonneg (n + 3 * (144 : ℝ)), sq_nonneg (n + 4 * (144 : ℝ)), sq_nonneg (n - 4 * (144 : ℝ)), sq_nonneg (n - 3 * (144 : ℝ)), sq_nonneg (n - 2 * (144 : ℝ)), sq_nonneg (n - (144 : ℝ)), sq_nonneg (n + (144 : ℝ)), sq_nonneg (n^2 - (144 : ℝ)^2), sq_nonneg (n^2 + (144 : ℝ)^2), sq_nonneg (n^3), sq_nonneg (n^4), sq_nonneg (n^5 - (144 : ℝ)^5)]
        nlinarith [h8]
    norm_num at h3 ⊢
    exact h3
  · -- Assume n = 144, prove 133^5 + 110^5 + 84^5 + 27^5 = n^5
    intro h
    rw [h]
    all_goals norm_num