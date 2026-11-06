import Mathlib

theorem algebra_190145 (x y z : ℝ) (h₀ : x ≠ y) (h₁ : y ≠ z) (h₂ : z ≠ x)
    (h₃ : x + y + z = 0) :
    (x * y + y * z + z * x) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ -1 / 2 := by

  have h4 : x ^ 2 + y ^ 2 + z ^ 2 > 0 := by
    by_contra h
    push_neg at h
    have h5 : x ^ 2 ≥ 0 := sq_nonneg x
    have h6 : y ^ 2 ≥ 0 := sq_nonneg y
    have h7 : z ^ 2 ≥ 0 := sq_nonneg z
    have h8 : x ^ 2 = 0 := by nlinarith [h5, h6, h7, h]
    have h9 : x = 0 := by
      rw [sq_eq_zero_iff] at h8
      exact h8
    have h10 : y ^ 2 = 0 := by nlinarith [h5, h6, h7, h]
    have h11 : y = 0 := by
      rw [sq_eq_zero_iff] at h10
      exact h10
    have h13 : z = 0 := by nlinarith [h₃, h9, h11]
    exfalso
    exact h₀ (by linarith)
  
  have h5 : x * y + y * z + z * x = -1 / 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    have h6 : (x + y + z) ^ 2 = 0 := by
      rw [h₃]
      norm_num
    nlinarith

  have h7 : (x * y + y * z + z * x) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ -1 / 2 := by
    have h8 : x * y + y * z + z * x ≤ -1 / 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by 
      linarith [h5]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [h8]

  exact h7