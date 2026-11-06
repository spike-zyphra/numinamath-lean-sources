import Mathlib

theorem algebra_15204 {x y : ℝ} (h₀ : |x - y| = 9) (h₁ : x^2 + y^2 = 153) :
    x * y = 36 := by
  cases eq_or_eq_neg_of_abs_eq h₀ with
  | inl h2 =>
    have h3 : x = y + 9 := by linarith
    rw [h3] at h₁
    have h4 : 2 * y ^ 2 + 18 * y - 72 = 0 := by
      ring_nf at h₁ ⊢
      linarith
    have h5 : y ^ 2 + 9 * y - 36 = 0 := by 
      linarith [h4]
    have h6 : (y - 3) * (y + 12) = 0 := by
      nlinarith [h5]
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- y - 3 = 0, so y = 3
      have hy : y = 3 := by linarith
      have hx : x = 12 := by
        linarith [h3, hy]
      rw [hx, hy]
      norm_num
    · -- y + 12 = 0, so y = -12
      have hy : y = -12 := by linarith
      have hx : x = -3 := by
        linarith [h3, hy]
      rw [hx, hy]
      norm_num
  | inr h2 =>
    have h3 : y = x + 9 := by linarith
    rw [h3] at h₁
    have h4 : 2 * x ^ 2 + 18 * x - 72 = 0 := by 
      ring_nf at h₁ ⊢
      linarith
    have h5 : x ^ 2 + 9 * x - 36 = 0 := by
      linarith [h4]
    have h6 : (x - 3) * (x + 12) = 0 := by 
      nlinarith [h5]
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- x - 3 = 0, so x = 3
      have hx : x = 3 := by linarith
      have hy : y = 12 := by 
        linarith [h3, hx]
      rw [hx, hy]
      norm_num
    · -- x + 12 = 0, so x = -12
      have hx : x = -12 := by linarith
      have hy : y = -3 := by 
        linarith [h3, hx]
      rw [hx, hy]
      norm_num