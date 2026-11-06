import Mathlib

theorem algebra_276986 {x y z : ℝ} (h₀ : x^2 * y * z^3 = 7^3) (h₁ : x * y^2 = 7^9) :
    x * y * z = 7^4 := by
  have h2 : (x * y * z) ^ 3 = 7 ^ 12 := by
    calc
      (x * y * z) ^ 3 = x^3 * y^3 * z^3 := by ring
      _ = (x^2 * y * z^3) * (x * y^2) := by 
        ring_nf
      _ = (7^3) * (7^9) := by 
        rw [h₀, h₁]
      _ = 7 ^ (3 + 9 : ℕ) := by 
        norm_num
      _ = 7 ^ 12 := by 
        norm_num
  have h3 : x * y * z = 7 ^ 4 := by
    have h4 : (x * y * z : ℝ) ^ 3 = (7 ^ 4 : ℝ) ^ 3 := by
      norm_num at h2 ⊢
      linarith
    have h5 : (x * y * z : ℝ) = (7 ^ 4 : ℝ) := by
      have h6 : (x * y * z : ℝ) ^ 3 = (7 ^ 4 : ℝ) ^ 3 := by
        linarith
      have h7 : (x * y * z : ℝ) = (7 ^ 4 : ℝ) := by
        have h10 : (x * y * z) ^ 3 - (7^4 : ℝ)^3 = 0 := by linarith
        have h11 : (x * y * z - (7 ^ 4 : ℝ)) * ((x * y * z) ^ 2 + (x * y * z) * (7 ^ 4 : ℝ) + (7 ^ 4 : ℝ) ^ 2) = 0 := by 
          ring_nf at h10 ⊢
          nlinarith
        cases' (mul_eq_zero.mp h11) with h12 h13
        · linarith
        · 
          nlinarith [sq_nonneg (x * y * z - (7^4 : ℝ)), sq_nonneg (x * y * z + (7^4 : ℝ)), sq_nonneg (y), sq_nonneg (z)]
      linarith
    linarith
  linarith [h3]