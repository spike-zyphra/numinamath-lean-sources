import Mathlib

theorem algebra_93808 {x : ℝ} (hx : x > 0) (h : (1 + x / 100) * (1 - x / 100) = 0.84) :
x = 40 := by

  have h1 : (1 + x / 100) * (1 - x / 100) = 1 - (x ^ 2 / 10000) := by
    ring_nf

  rw [h1] at h

  have h2 : x ^ 2 / 10000 = 0.16 := by
    nlinarith
  
  have h3 : x^2 = 1600 := by
    have h4 : x ^ 2 / 10000 = (0.16 : ℝ) := h2
    have h5 : x^2 = (0.16 : ℝ) * 10000 := by
      field_simp at h4 ⊢
      nlinarith
    rw [h5]
    norm_num
  
  have h4 : x = 40 := by
    nlinarith [sq_nonneg x, h3, hx]

  exact h4