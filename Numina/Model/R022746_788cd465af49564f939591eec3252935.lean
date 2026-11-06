import Mathlib

theorem algebra_297889 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x + y + 9 / x + 4 / y = 10) (h2 : (x ^ 2 + 9) * (y ^ 2 + 4) = 24 * x * y) :
    x = 3 ∧ y = 2 := by 
  have eq1 : (x + y) * (x * y) + 9 * y + 4 * x = 10 * x * y := by
    have h1' : x + y + 9 / x + 4 / y = 10 := h1
    field_simp [hx, hy] at h1' ⊢
    linarith 
  -- The second equation can be written as (xy - 6)^2 + (2x - 3y)^2 = 0
  have eq2 : (x * y - 6) ^ 2 + (2 * x - 3 * y) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x * y - 6), sq_nonneg (2 * x - 3 * y), sq_nonneg (x - 3), sq_nonneg (y - 2), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy]
  have h3 : (x * y - 6) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x * y - 6), sq_nonneg (2 * x - 3 * y), eq2]
  have h4 : (2 * x - 3 * y) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x * y - 6), sq_nonneg (2 * x - 3 * y), eq2]
  have h5 : 2 * x - 3 * y = 0 := by
    rw [sq_eq_zero_iff] at h4
    linarith 
  have h6 : x * y = 6 := by 
    rw [sq_eq_zero_iff] at h3
    linarith 
  have h7 : y = 2 / 3 * x := by 
    linarith 
  have h8 : x ^ 2 = 9 := by
    have h9 : y = 2 / 3 * x := h7 
    rw [h9] at h6 
    nlinarith 
  have h9 : x = 3 ∨ x = -3 := by
    have h10 : x ^ 2 - 9 = 0 := by nlinarith 
    have h11 : (x - 3) * (x + 3) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.1 h11) with h12 h13 
    · -- First case when x - 3 = 0, so x = 3 
      left 
      linarith 
    · -- Second case when x + 3 = 0, so x = -3 
      right 
      linarith 
  cases h9 with 
  | inl hx10 => 
    have hy10 : y = 2 := by
      rw [h7]
      linarith [hx10] 
    exact ⟨hx10, hy10⟩ 
  | inr hx11 => 
    have hy12 : y = -2 := by 
      rw [h7] 
      linarith [hx11] 
    -- Substitute the values. 
    rw [show x = (-3 : ℝ) by linarith [hx11], show y = (-2 : ℝ) by linarith [hy12]] at h1 
    norm_num at h1 
    all_goals try { 
      exfalso <;> linarith 
    }