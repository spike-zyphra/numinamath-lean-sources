import Mathlib

theorem algebra_251992 {x y : ℝ} (h1 : x + y = 4) (h2 : (x^2 + y^2) * (x^3 + y^3) = 280) :
    (x = 3 ∧ y = 1) ∨ (x = 1 ∧ y = 3) := by 
  have h3 : x^2 + y^2 = (x + y) ^ 2 - 2 * (x * y) := by 
    ring
  have h4 : x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by 
    ring 
  rw [h3, h4] at h2 
  rw [h1] at h2 
  have h5 : (16 - 2 * (x * y)) * (64 - 12 * (x * y)) = 280 := by
    nlinarith 
  have h6 : 24 * (x * y) ^ 2 - 320 * (x * y) + 744 = 0 := by
    nlinarith 
  have h7 : (x * y - 3) * (x * y - 31/3) = 0 := by 
    nlinarith [sq_nonneg (x * y - 3), sq_nonneg (x * y - 31/3), sq_nonneg (x * y)]
  cases' (mul_eq_zero.1 h7) with h8 h9 
  · -- Case where x * y = 3
    have h9 : x * y = 3 := by 
      linarith 
    have h10 : (x - 3) * (x - 1) = 0 := by 
      have h11 : y = 4 - x := by linarith [h1]
      rw [h11] at h9 
      nlinarith 
    cases' (mul_eq_zero.1 h10) with h11 h12 
    · -- Case where x = 3
      have hx1 : x = 3 := by 
        linarith 
      have hy1 : y = 1 := by 
        nlinarith [h1] 
      left 
      exact ⟨hx1, hy1⟩ 
    · -- Case where x = 1
      have hx2 : x = 1 := by 
        linarith 
      have hy2 : y = 3 := by 
        nlinarith [h1] 
      right 
      exact ⟨hx2, hy2⟩ 
  · -- Case where x * y = 31/3
    have h15 : x * y = 31 / 3 := by 
      linarith 
    have h8 : (x - y) ^ 2 < 0 := by 
      nlinarith [sq_nonneg (x * y - 31/3), sq_nonneg (x + y - 4)] 
    have h9 : (x - y) ^ 2 ≥ 0 := by 
      apply sq_nonneg 
    nlinarith