import Mathlib

theorem algebra_247969 (x y z : ℝ) (h₀ : x^2 + y^2 = 5) (h₁ : x * z + y = 7) (h₂ : y * z - x = 1) :
    (x = 2 ∧ y = 1 ∧ z = 3) ∨ (x = -11 / 5 ∧ y = 2 / 5 ∧ z = -3) := by

  have eq1 : x ^ 2 + y ^ 2 = 5 := h₀
  have eq2 : x * z + y = 7 := h₁
  have eq3 : y * z - x = 1 := h₂

  have eq4 : x - 7 * y = -5 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (z + 3), sq_nonneg (x + 11 / 5), sq_nonneg (y - 1), sq_nonneg (y - 2 / 5)]
  
  have eq5 : x = 7 * y - 5 := by linarith

  rw [eq5] at h₀

  have h3 : 5 * y ^ 2 - 7 * y + 2 = 0 := by 
    nlinarith

  have h4 : (y - 1) * (y - 2 / 5) = 0 := by 
    nlinarith

  cases' (mul_eq_zero.1 h4) with hy1 hy2
  · -- First solution
    have hy : y = 1 := by linarith 
    have hx : x = 2 := by 
      rw [hy] at eq5 
      linarith

    have hz : z = 3 := by 
      rw [hx, hy] at h₁ 
      nlinarith

    left 
    constructor
    · exact hx 
    constructor
    · exact hy 
    · exact hz 
  · -- Second solution 
    have hy2 : y = 2 / 5 := by 
      linarith

    have hx2 : x = -11 / 5 := by 
      rw [hy2] at eq5 
      linarith

    have hz2 : z = -3 := by 
      rw [hx2, hy2] at h₁ 
      nlinarith

    right 
    constructor
    · exact hx2 
    constructor 
    · exact hy2 
    · exact hz2