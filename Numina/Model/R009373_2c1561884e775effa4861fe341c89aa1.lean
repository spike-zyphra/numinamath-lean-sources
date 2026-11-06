import Mathlib

theorem algebra_21771 (c : ℝ) (h : ∃ x y, x ≠ y ∧ x^3-10*x^2+55*x-c=0 ∧ y^3-10*y^2+55*y-c=0 ∧ x*y=30) :
    c=150 := by
  obtain ⟨x, y, hxy, hx, hy, hxyprod⟩ := h
  have h1 : x^3 - 10*x^2 + 55*x - c = 0 := by 
    linarith
  have h2 : y^3 - 10*y^2 + 55*y - c = 0 := by
    linarith
  have h3 : x^3 - 10 * x^2 + 55 * x - c - (y^3 - 10 * y^2 + 55 * y - c) = 0 := by
    linarith [hx, hy]
  have h4 : (x - y) * (x^2 + x*y + y^2 - 10*(x + y) + 55) = 0 := by
    ring_nf at h3 ⊢
    nlinarith
  cases' (mul_eq_zero.1 h4) with h5 h6
  · 
    exfalso
    exact hxy (by linarith)
  ·
    have h6' : x^2 + x*y + y^2 - 10*(x + y) + 55 = 0 := by 
      linarith
    have h7 : x^2 + y^2 + 85 = 10 * (x + y) := by
      have hxyprod' : x * y = 30 := hxyprod
      nlinarith
      all_goals linarith
    have h9 : c = x^3 - 10*x^2 + 55*x := by
      linarith
    have h10 : c = y^3 - 10*y^2 + 55*y := by
      nlinarith
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hxy), hxyprod, h7, h1, h2, sq_nonneg (x - 5), sq_nonneg (y - 5)]