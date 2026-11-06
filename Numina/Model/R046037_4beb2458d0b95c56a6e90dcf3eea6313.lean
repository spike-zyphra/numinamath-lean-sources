import Mathlib

open Real

theorem algebra_16311 (x : ℝ) (hx : 0 ≤ 4 * x - 3) :
    sqrt (4 * x - 3) + 10 / sqrt (4 * x - 3) = 7 ↔ x = 7 / 4 ∨ x = 7 := by 
  constructor
  · -- Assume sqrt (4 * x - 3) + 10 / sqrt (4 * x - 3) = 7, prove x = 7 / 4 ∨ x = 7
    intro h
    have h1 : sqrt (4 * x - 3) > 0 := by
      by_contra h1
      push_neg at h1
      have h2 : sqrt (4 * x - 3) = 0 := by nlinarith [Real.sqrt_nonneg (4 * x - 3)]
      rw [h2] at h
      field_simp at h
      all_goals linarith
    have h2 : (sqrt (4 * x - 3)) ^ 2 = 4 * x - 3 := Real.sq_sqrt (by linarith)
    have eq1 : (sqrt (4 * x - 3)) ^ 2 + 10 = 7 * sqrt (4 * x - 3) := by
      have h1' : sqrt (4 * x - 3) > 0 := h1
      field_simp at h ⊢
      nlinarith [h, Real.sqrt_nonneg (4 * x - 3)]
    have h3 : (sqrt (4 * x - 3) - 5) * (sqrt (4 * x - 3) - 2) = 0 := by
      nlinarith [eq1, Real.sqrt_nonneg (4 * x - 3)]
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- case sqrt (4 * x - 3) = 5 
      have h5' : sqrt (4 * x - 3) = 5 := by linarith
      have h6 : 4 * x - 3 = 25 := by
        calc
          4 * x - 3 = (sqrt (4 * x - 3)) ^ 2 := by rw [Real.sq_sqrt (show 0 ≤ 4 * x - 3 by linarith)]
          _ = (5) ^ 2 := by rw [h5']
          _ = (25 : ℝ) := by norm_num
      have h7 : x = 7 := by linarith 
      right
      exact h7
    · -- case sqrt (4 * x - 3) = 2 
      have h5' : sqrt (4 * x - 3) = 2 := by linarith
      have h8 : 4 * x - 3 = 4 := by
        calc
          4 * x - 3 = (sqrt (4 * x - 3)) ^ 2 := by rw [Real.sq_sqrt (show 0 ≤ 4 * x - 3 by linarith)]
          _ = (2) ^ 2 := by rw [h5']
          _ = (4 : ℝ) := by norm_num
      have h9 : x = 7 / 4 := by linarith 
      left
      exact h9
  · -- Assume x = 7 / 4 ∨ x = 7, prove sqrt (4 * x - 3) + 10 / sqrt (4 * x - 3) = 7 
    rintro (h | h)
    · -- case x = 7 / 4
      have hx1 : x = 7 / 4 := h
      have h1 : sqrt (4 * x - 3) = 2 := by
        rw [hx1]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      norm_num
    · -- case x = 7
      have hx2 : x = 7 := h
      have h2 : sqrt (4 * x - 3) = 5 := by
        rw [hx2]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h2]
      norm_num