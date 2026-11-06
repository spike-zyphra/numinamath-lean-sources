import Mathlib

theorem algebra_20442 (a b c : ℝ) (ha : a ≠ 0) (h1 : ∀ x, a * (1 + x) ^ 2 + b * (1 + x) + c = a * (1 - x) ^ 2 + b * (1 - x) + c)
    (h2 : a * (-1) ^ 2 + b * (-1) + c = 3) (h3 : a * (2) ^ 2 + b * (2) + c = -2)
    (n : ℝ) (hn : n > 0) (hroots : ∃ x y, x > y ∧ a * x ^ 2 + b * x + c = 0 ∧ a * y ^ 2 + b * y + c = 0 ∧ x = Real.sqrt n + 1) :
    n = 2.2 := by

  have h5 := h1 1
  ring_nf at h5 
  have h7 : b = -2 * a := by
    linarith

  have h10 : c = -2 := by 
    have h5' := h1 1
    have h6 := h1 (-1)
    ring_nf at h5' h6 
    nlinarith

  have h11 : a = 5 / 3 := by 
    have h4 := h1 0
    ring_nf at h4
    nlinarith [h5, h2, h3] 

  have h12 : b = -10 / 3 := by
    rw [h11] at h7 
    linarith 

  rcases hroots with ⟨x, y, hxy, hx, hy, hx_eq⟩ 
  have hx_sub : a * x ^ 2 + b * x + c = 0 := hx 
  rw [h11, h12, h10] at hx_sub 
  have h15 : (5 / 3) * x ^ 2 - (10 / 3) * x - 2 = (0 : ℝ) := by
    linarith

  have eq1 : x = Real.sqrt n + 1 := by 
    linarith [hx_eq] 

  rw [eq1] at h15 
  ring_nf at h15 
  have h18 : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt (show 0 ≤ (n : ℝ) by linarith) 
  nlinarith [Real.sqrt_nonneg n, Real.sq_sqrt (show 0 ≤ (n : ℝ) by linarith) ]