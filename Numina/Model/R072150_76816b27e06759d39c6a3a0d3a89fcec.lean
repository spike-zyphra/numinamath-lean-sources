import Mathlib

theorem algebra_297246 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x + y + 9 / x + 4 / y = 10) (h2 : (x ^ 2 + 9) * (y ^ 2 + 4) = 24 * x * y) :
    x = 3 ∧ y = 2 := by 
  have h3 : (x * y - 6) ^ 2 + (2 * x - 3 * y) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x * y - 6), sq_nonneg (2 * x - 3 * y), h2]
  have h5 : (x * y - 6) ^ 2 = 0 := by 
    linarith [sq_nonneg (x * y - 6), sq_nonneg (2 * x - 3 * y)]
  have h6 : (2 * x - 3 * y) ^ 2 = 0 := by 
    linarith [sq_nonneg (x * y - 6), sq_nonneg (2 * x - 3 * y)]
  have h7 : x * y - 6 = 0 := by 
    rw [sq_eq_zero_iff] at h5 
    exact h5 
  have h8 : 2 * x - 3 * y = 0 := by 
    rw [sq_eq_zero_iff] at h6 
    exact h6 
  have h9 : x * y = 6 := by 
    linarith 
  have h10 : y = (2 / 3) * x := by 
    linarith 
  rw [h10] at h9 
  have h11 : x ^ 2 = 9 := by 
    nlinarith [h9]
  have hx1 : x = 3 ∨ x = -3 := by 
    have h : x ^ 2 - 9 = 0 := by linarith 
    have hfactored : (x - 3) * (x + 3) = 0 := by 
      ring_nf at h ⊢ 
      linarith 
    cases (mul_eq_zero.mp hfactored) with 
    | inl h1 => 
      left 
      linarith 
    | inr h2 => 
      right 
      linarith 
  cases hx1 with 
  | inl hx2 => 
    have hy2 : y = 2 := by 
      rw [hx2] at h10 
      linarith 
    exact ⟨hx2, hy2⟩ 
  | inr hx2 => 
    have hy2 : y = -2 := by 
      rw [hx2] at h10 
      linarith 
    rw [hx2, hy2] at h1 
    norm_num at h1 
    all_goals 
      linarith