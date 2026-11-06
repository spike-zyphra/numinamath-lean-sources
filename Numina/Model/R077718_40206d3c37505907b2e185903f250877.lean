import Mathlib

theorem algebra_11846 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x, a * x ^ 2 + b * x + c = 4 * (x - 2) ^ 2 - 4)
    (m n : ℝ) (hm : m > n) (hmn : a * m ^ 2 + b * m + c = 0) (hmn' : a * n ^ 2 + b * n + c = 0) :
    m - n = 2 := by
  have h1 := h 0
  have h2 := h 1
  have h3 := h 2
  have h4 := h 3
  have h5 := h 4
  have ha2 : a = 4 := by
    nlinarith [h1, h2, h3, h4, h5]
  have hb : b = -16 := by
    nlinarith [h1, h2, h3, h4, h5]
  have hc : c = 12 := by
    nlinarith [h1]
  rw [ha2, hb, hc] at hmn hmn'
  have h_eq1 : 4 * m ^ 2 + -16 * m + 12 = 0 := by linarith
  have h_eq2 : 4 * n ^ 2 + -16 * n + 12 = 0 := by linarith
  have h1 : (m - 3) * (m - 1) = 0 := by
    nlinarith 
  have h2 : (n - 3) * (n - 1) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.mp h1) with hm_eq3 hm_eq1
  · -- m = 3
    have hm3 : m = 3 := by linarith
    cases' (mul_eq_zero.mp h2) with hn_eq3 hn_eq1
    · -- If n = 3, which contradicts to m > n
      have hn3 : n = 3 := by linarith
      linarith 
    · -- n = 1
      have hn1 : n = 1 := by linarith
      have : m - n = 2 := by
        linarith 
      linarith 
  · -- m = 1 
    have hm1 : m = 1 := by linarith
    cases' (mul_eq_zero.mp h2) with hn_eq3 hn_eq1
    · -- If n = 3, which contradicts m > n
      have hn3 : n = 3 := by linarith
      linarith 
    · -- If n = 1, which would lead to m = n, contradiction
      have hn1 : n = 1 := by linarith
      linarith