import Mathlib

-- What is the sum of the solutions to the equation x^4 = 12/(7-x^(1/4))?

theorem AIME_algebra_94869 (x : ℝ) (hx : x ≥ 0) (ne_zero : (7 - x ^ ((1 : ℝ) / 4)) ≠ 0) :
x ^ ((1 : ℝ) / 4) = 12 / (7 - x ^ ((1 : ℝ) / 4)) ↔ (x = 256) ∨ (x = 81) := by
  constructor
  · -- Assume x^(1/4) = 12 / (7 - x^(1/4))
    intro h
    have h1 : x ^ ((1 : ℝ) / 4) = 12 / (7 - x ^ ((1 : ℝ) / 4)) := h
    have h2 : x ^ ((1 : ℝ) / 4) * (7 - x ^ ((1 : ℝ) / 4)) = 12 := by
      have h' : (7 - x ^ ((1 : ℝ) / 4)) ≠ 0 := ne_zero
      field_simp [h'] at h1 ⊢
      linarith
    have eq1 : (x ^ ((1 : ℝ) / 4) - 3) * (x ^ ((1 : ℝ) / 4) - 4) = 0 := by
      nlinarith [sq_nonneg (x ^ ((1 : ℝ) / 4) - 3), sq_nonneg (x ^ ((1 : ℝ) / 4) - 4)]
    cases' (mul_eq_zero.mp eq1) with h4 h5
    · -- Case x^(1/4) = 3
      have h6 : x ^ ((1 : ℝ) / 4) = 3 := by linarith
      have hx : x = 81 := by
        have h7 : x = (x ^ ((1 : ℝ) / 4)) ^ 4 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        rw [h6] at h7
        norm_num at h7 ⊢
        linarith
      right
      exact hx
    · -- Case x^(1/4) = 4
      have h8 : x ^ ((1 : ℝ) / 4) = 4 := by linarith
      have hx : x = 256 := by
        have h7 : x = (x ^ ((1 : ℝ) / 4)) ^ 4 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        rw [h8] at h7
        norm_num at h7 ⊢
        linarith
      left
      exact hx
  · -- Assume x = 256 or x = 81
    rintro (hx | hx)
    · -- Case x = 256
      rw [hx]
      have h5 : (256 : ℝ) ^ ((1 : ℝ) / 4) = 4 := by
        rw [show (256 : ℝ) = 4 ^ (4 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      rw [h5]
      norm_num
    · -- Case x = 81
      rw [hx]
      have h5 : (81 : ℝ) ^ ((1 : ℝ) / 4) = 3 := by
        rw [show (81 : ℝ) = 3 ^ (4 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      rw [h5]
      norm_num