import Mathlib

theorem algebra_303687 {x y : ℝ} (h1 : x^3 + y^3 = 26) (h2 : x * y * (x + y) = -6) : |x - y| = 4 := by
  have h3 : (x + y) ^ 3 = 8 := by
    have h : x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y * (x + y)) := by
      ring
    rw [h] at h1
    linarith [h2]
  
  have h4 : x + y = 2 := by
    have h5 : (x + y) ^ 3 - 8 = 0 := by linarith
    have h6 : (x + y - 2) * ((x + y) ^ 2 + 2 * (x + y) + 4) = 0 := by
      ring_nf at h5 ⊢
      linarith 
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case where $x + y - 2 = 0$, so $x + y = 2$
      linarith
    · -- Case where $(x+y)^2 + 2(x+y) + 4 = 0$
      have h9 : (x + y) ^ 2 + 2 * (x + y) + 4 > 0 := by
        nlinarith [sq_nonneg (x + y + 1)]
      nlinarith

  have h5 : x * y = -3 := by
    rw [h4] at h2
    nlinarith
  
  have h6 : (x - y) ^ 2 = 16 := by
    nlinarith [h4, h5]

  have h7 : |x - y| = 4 := by
    have h8 : (x - y) ^ 2 = 16 := h6
    have h9 : (x - y) = 4 ∨ (x - y) = -4 := by
      have h10 : (x - y) ^ 2 - 16 = 0 := by linarith 
      have h11 : (x - y - 4) * (x - y + 4) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.mp h11) with h12 h13
      · -- Case where $x - y - 4 = 0$, so $x - y = 4$
        left 
        linarith 
      · -- Case where $x - y + 4 = 0$, so $x - y = -4$
        right 
        linarith 
    cases' h9 with h14 h15
    · -- Case where $x - y = 4$, so $|x - y| = 4$
      rw [h14]
      norm_num 
    · -- Case where $x - y = -4$, so $|x - y| = |-4| = 4$
      rw [h15]
      norm_num 
  exact h7