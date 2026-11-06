import Mathlib

theorem algebra_297829 (k : ℝ) (h : ∀ P : ℝ, ∃ A B : ℝ,
    A^2/25 + B^2/16 = 1 ∧ A ≠ B ∧
    (A - P)^2 + (B - P)^2 = 4*k^2) :
    k = 4/5 ∨ k = -4/5 := by

  have h1 := h 0
  rcases h1 with ⟨A, B, h2, h3, h4⟩

  have h5 := h 5
  rcases h5 with ⟨C, D, h6, h7, h8⟩

  have h10 := h 10
  rcases h10 with ⟨E, F, h11, h12, h13⟩

  have h15 := h 20
  rcases h15 with ⟨G, H, h16, h17, h18⟩

  ring_nf at h4 h8 h13 h18

  have hk1 : k^2 = 16/25 := by
    nlinarith [sq_pos_of_ne_zero (show (A - B) ≠ 0 by
      intro h'
      apply h3
      linarith
    ), sq_nonneg (A - B), sq_nonneg (C - D), sq_nonneg (E - F), sq_nonneg (G - H)]
  
  have hk3 : (k - 4/5) * (k + 4/5) = 0 := by 
    nlinarith

  cases' (mul_eq_zero.mp hk3) with hk4 hk5
  · 
    left
    linarith
  · 
    right
    linarith