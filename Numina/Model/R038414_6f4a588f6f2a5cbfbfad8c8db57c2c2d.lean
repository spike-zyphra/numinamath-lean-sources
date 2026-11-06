import Mathlib

open Real Set

theorem algebra_8052 :
  IsLeast {y : ℝ | ∃ x, y = sqrt (x ^ 2) + sqrt ((x + 1) ^ 2) + sqrt ((x - 2) ^ 2)} 3 := by
  constructor
  · -- Show 3 is achievable, by setting x = 0
    use (0 : ℝ)
    have h1 : sqrt (0 ^ 2 : ℝ) = 0 := by
      simp [Real.sqrt_eq_iff_sq_eq]
    have h2 : sqrt ((0 + 1 : ℝ) ^ 2) = 1 := by
      rw [Real.sqrt_sq_eq_abs]
      norm_num
    have h3 : sqrt ((0 - 2 : ℝ) ^ 2) = 2 := by
      rw [Real.sqrt_sq_eq_abs]
      norm_num
    rw [h1, h2, h3]
    all_goals norm_num
  · -- Show no smaller value is achievable
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : sqrt (x ^ 2 : ℝ) = |x| := by
      rw [Real.sqrt_sq_eq_abs]
    have h2 : sqrt ((x + 1 : ℝ) ^ 2) = |x + 1| := by
      rw [Real.sqrt_sq_eq_abs]
    have h3 : sqrt ((x - 2 : ℝ) ^ 2) = |x - 2| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h1, h2, h3] at hx
    have h4 : |x| + |x + 1| + |x - 2| ≥ (3 : ℝ) := by
      cases' abs_cases x with hx1 hx1 <;> 
      cases' abs_cases (x + 1) with hx2 hx2 <;> 
      cases' abs_cases (x - 2) with hx3 hx3 <;> 
      all_goals linarith
    linarith [abs_nonneg (x), abs_nonneg (x + 1), abs_nonneg (x - 2)]