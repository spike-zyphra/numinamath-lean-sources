import Mathlib

open BigOperators Real Set

theorem algebra_160944 (f : ℝ → ℝ) (hf : f = λ x => (5 * x + sqrt (9 * x ^ 2 - 16)) / (1 + x ^ 2)) :
    IsGreatest (range f) 3 := by
  constructor
  · -- Show 3 is attained, using x = 5/3
    use 5 / 3
    rw [hf]
    have h1 : Real.sqrt (9 * (5 / 3 : ℝ) ^ 2 - 16) = (3 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    simp [h1]
    norm_num
  · -- Show that 3 is an upper bound
    intro y
    rintro ⟨x, hy⟩
    rw [hf] at hy
    have h_eq : (5 * x + Real.sqrt (9 * x ^ 2 - 16)) / (1 + x ^ 2) = y := by
      simpa using hy
    have h2 : (5 * x + Real.sqrt (9 * x ^ 2 - 16)) / (1 + x ^ 2) ≤ (3 : ℝ) := by
      have h3 : 1 + x ^ 2 > 0 := by
        nlinarith [sq_nonneg x]
      apply (div_le_iff₀ (by linarith)).mpr
      by_cases h : 9 * x ^ 2 - 16 ≥ 0
      · -- 9x^2 - 16 >= 0
        have h10 : Real.sqrt (9 * x ^ 2 - 16) ^ 2 = 9 * x ^ 2 - 16 := by
          rw [Real.sq_sqrt]
          nlinarith
        have h7 : (Real.sqrt (9 * x ^ 2 - 16) : ℝ) ≤ (3 + 3 * x ^ 2 - 5 * x : ℝ) := by
          by_cases h30 : (3 + 3 * x ^ 2 - 5 * x : ℝ) ≥ 0
          · -- sqrt(a) ≤ b is equivalent to a ≤ b^2 when a ≥ 0 and b ≥ 0
            have h20 : Real.sqrt (9 * x ^ 2 - 16) ^ 2 ≤ (3 + 3 * x ^ 2 - 5 * x) ^ 2 := by
              nlinarith [sq_nonneg ( (3 * x ^ 2 - 5 * x + 3 : ℝ) ), sq_nonneg ( (x - 5/3 : ℝ) ), sq_nonneg (x * (x - 5/3) ), sq_nonneg ( (x^2 - 25/9) ), Real.sqrt_nonneg (9 * x ^ 2 - 16) ]
            have h40 : Real.sqrt (9 * x ^ 2 - 16) ≤ (3 + 3 * x ^ 2 - 5 * x : ℝ) := by
              nlinarith [Real.sqrt_nonneg (9 * x ^ 2 - 16), h30]
            linarith
          · -- When 3 + 3x^2 - 5x < 0
            nlinarith [Real.sqrt_nonneg (9 * x ^ 2 - 16), sq_nonneg ( (x - 5/3 : ℝ) ), Real.sq_sqrt (show 0 ≤ (9 * x ^ 2 - 16 : ℝ) by linarith ) ]
        nlinarith [Real.sqrt_nonneg (9 * x ^ 2 - 16), sq_nonneg ( (x - 5/3 : ℝ) ) ]
      · -- 9x^2 - 16 < 0
        have h11 : Real.sqrt (9 * x ^ 2 - 16) = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith
        rw [h11]
        nlinarith [sq_nonneg ( (x - 5/3 : ℝ) ) ]
    linarith [h2, h_eq]