import Mathlib

theorem algebra_305419 {p q : ℝ} (h : ∃ x y, x ≠ y ∧ x^2 - p * x + q = 0 ∧ y^2 - p * y + q = 0 ∧ |x - y| = 1) :
    q = (p^2 - 1) / 4 := by 
  rcases h with ⟨x, y, hxy, hx, hy, habs⟩ 
  have h1 : x^2 - p * x + q = 0 := hx
  have h2 : y^2 - p * y + q = 0 := hy
  have h3 : x^2 - p * x + q - (y^2 - p * y + q) = 0 := by
    linarith
  have h4 : (x - y) * (x + y - p) = 0 := by 
    nlinarith [h3]
  cases (mul_eq_zero.mp h4) with
  | inl h5 =>
    exfalso
    apply hxy
    nlinarith
  | inr h6 =>
    have h7 : (x - y) ^ 2 = 1 := by
      cases eq_or_eq_neg_of_abs_eq habs with
      | inl h8 =>
        nlinarith
      | inr h8 =>
        nlinarith
    have h8 : x + y = p := by linarith
    nlinarith [sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y)]