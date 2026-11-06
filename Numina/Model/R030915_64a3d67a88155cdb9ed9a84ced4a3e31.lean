import Mathlib

theorem number_theory_129177 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : x^3 + 4 * x^2 - 3 * x + 6 = y^3) :
    (x, y) = (1, 2) ∨ (x, y) = (5, 6) := by
  have h1 : y > x := by
    nlinarith [sq_nonneg (y - x), sq_nonneg (x + 2), sq_nonneg (y + 1),
              sq_nonneg (x - 1), sq_nonneg (x - 5)]
  have h2 : y < x + 2 := by
    nlinarith [sq_nonneg (y - (x + 1)), sq_nonneg (x + 2), sq_nonneg (y + 1),
              sq_nonneg (x - 1), sq_nonneg (x - 5)]
  have h3 : y = x + 1 := by 
    linarith
  rw [show y = x + 1 by linarith] at h 
  have h4 : x ^ 2 - 6 * x + 5 = 0 := by
    nlinarith 
  have h5 : (x - 1) * (x - 5) = 0 := by 
    nlinarith 
  have h6 : x = 1 ∨ x = 5 := by
    cases (mul_eq_zero.mp h5) with
    | inl h7 =>
      left 
      linarith 
    | inr h8 =>
      right 
      linarith 
  cases h6 with
  | inl hx1 =>
    have hy1 : y = 2 := by 
      linarith 
    left 
    simp [hx1, hy1] 
  | inr hx2 =>
    have hy2 : y = 6 := by 
      linarith 
    right 
    simp [hx2, hy2]