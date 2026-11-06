import Mathlib

theorem algebra_198358 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : (x + y)^2 + 3 * (x + y) = 4) (h2 : 1 / x + 1 / y = -1 / 6) :
    (x = 3 ∧ y = -2) ∨ (x = -2 ∧ y = 3) := by

  have h3 : (x + y) ^ 2 + 3 * (x + y) - 4 = 0 := by linarith

  have h4 : (x + y - 1) * (x + y + 4) = 0 := by
    ring_nf at h3 ⊢
    linarith
  
  cases' (mul_eq_zero.mp h4) with h5 h6
  
  · -- Case where $x + y = 1$
    have h7 : x + y = 1 := by linarith
  
    have h8 : x * y = -6 := by
      field_simp [hx, hy] at h2 
      nlinarith [h7]
  
    have h9 : (x - 3) * (x + 2) = 0 := by
      nlinarith [h7, h8]

    cases' (eq_zero_or_eq_zero_of_mul_eq_zero h9) with h10 h11
  
    · -- Case where $x - 3 = 0$, so $x = 3$
      have hx3 : x = 3 := by linarith 
      have hy1 : y = -2 := by nlinarith [h7, hx3]
      left
      exact ⟨hx3, hy1⟩
  
    · -- Case where $x + 2 = 0$, so $x = -2$
      have hx2 : x = -2 := by linarith 
      have hy3 : y = 3 := by nlinarith [h7, hx2]
      right 
      exact ⟨hx2, hy3⟩

  · -- Case where $x + y + 4 = 0$, so $x + y = -4$
    have h10 : x + y = -4 := by linarith
  
    have h11 : x * y = 24 := by
      field_simp [hx, hy] at h2 
      nlinarith [h10]

    have h12 : (x + y) ^ 2 - 4 * (x * y) < 0 := by 
      nlinarith [h10, h11]

    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy]