import Mathlib

theorem algebra_266564 {x y z : ℝ} (h₀ : x^2 * y * z^3 = 7^4) (h₁ : x * y^2 = 7^5) :
    x * y * z = 7^3 := by
  have h2 : (x * y * z) ^ 3 = 7 ^ 9 := by
    calc
      (x * y * z) ^ 3 = (x^2 * y * z^3) * (x * y^2) := by 
        ring_nf
      _ = 7^4 * 7^5 := by rw [h₀, h₁]
      _ = 7 ^ 9 := by ring
  have h3 : x * y * z = 7 ^ 3 := by
    have h4 : (x * y * z) ^ 3 - (7 : ℝ) ^ 9 = 0 := by 
      rw [h2]
      all_goals ring
    have h7 : (x * y * z - (7 : ℝ) ^ 3) * ((x * y * z) ^ 2 + (x * y * z) * (7 : ℝ) ^ 3 + (7 : ℝ) ^ 6) = 0 := by 
      ring_nf at h4 ⊢
      <;> nlinarith [sq_nonneg ((x * y * z - (7 : ℝ) ^ 3)), sq_nonneg ((x * y * z + (7 : ℝ) ^ 3))]
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- Case where the first factor is zero
      linarith
    · -- Case where the second factor is zero
      nlinarith [sq_nonneg ((x * y * z) + (7 : ℝ) ^ 3 / 2), sq_nonneg ((x * y * z) - (7 : ℝ) ^ 3), sq_nonneg ((x * y * z) + (7 : ℝ) ^ 3)]
  exact h3