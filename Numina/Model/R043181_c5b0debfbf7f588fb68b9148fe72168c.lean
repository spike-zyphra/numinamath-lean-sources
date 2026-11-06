import Mathlib

theorem algebra_306599 (x y z : ℝ) (h₀ : x + y = z - 1) (h₁ : x * y = z ^ 2 - 7 * z + 14) :
    x ^ 2 + y ^ 2 ≤ 9 ∧ (x ^ 2 + y ^ 2 = 9 ↔ z = 3) := by
  have h2 : x ^ 2 + y ^ 2 = -z ^ 2 + 12 * z - 27 := by
    calc
      x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
      _ = (z - 1) ^ 2 - 2 * (z ^ 2 - 7 * z + 14) := by rw [h₀, h₁]
      _ = -z ^ 2 + 12 * z - 27 := by ring
  have h3 : x ^ 2 + y ^ 2 ≤ 9 := by
    rw [h2]
    nlinarith [sq_nonneg (z - 3), sq_nonneg (x - y), sq_nonneg ((x + y) - 2*z), sq_nonneg ((x + y) * (x + y) - 4 * (x * y)), sq_nonneg (z - 6)]
  have h4 : x ^ 2 + y ^ 2 = 9 ↔ z = 3 := by
    constructor
    · -- Assume h_eq: x^2 + y^2 = 9, prove z = 3
      intro h_eq
      rw [h2] at h_eq
      have h_eq1 : (z - 3) ^ 2 = 0 := by
        nlinarith [sq_nonneg (z - 3), sq_nonneg (x - y), sq_nonneg ((x + y) - 2*z), sq_nonneg ((x + y) * (x + y) - 4 * (x * y)), sq_nonneg (z - 6)]
      have h_eq2 : z - 3 = 0 := by
        rw [sq_eq_zero_iff] at h_eq1
        exact h_eq1
      linarith
    · -- Assume z = 3, prove x^2 + y^2 = 9
      intro h_eq
      have h_subst : z = 3 := h_eq
      have h_x_y : x + y = 2 := by linarith [h₀, h_subst]
      have h_x_y_prod : x * y = 2 := by 
        rw [h₁, h_subst]
        norm_num
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x * y - 2)]
  exact ⟨h3, h4⟩