import Mathlib

theorem algebra_96217 {p q : ℝ} (hp : p > 0) (hq : q > 0)
    (hroots : ∃ x y, x ≠ y ∧ x^2 + p * x + q = 0 ∧ y^2 + p * y + q = 0 ∧ |x - y| = 1) :
    p = Real.sqrt (4 * q + 1) := by
  rcases hroots with ⟨x, y, hxy, hx, hy, h1⟩
  have h2 : (x - y) ^ 2 = 1 := by
    cases eq_or_eq_neg_of_abs_eq h1 with
    | inl h =>
      nlinarith
    | inr h =>
      nlinarith
  have h3 : x + y = -p := by
    have h_sub : (x - y) * (x + y + p) = 0 := by 
      nlinarith [hx, hy]
    cases (mul_eq_zero.mp h_sub) with 
    | inl h4 =>
      exfalso
      apply hxy
      linarith
    | inr h5 =>
      linarith
  have h4 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
    ring
  rw [h3] at h4
  have h5 : x * y = q := by 
    nlinarith [hx, hy]
  have h6 : (x - y) ^ 2 = p^2 - 4 * q := by 
    rw [h4, h5]
    ring
  have h7 : p^2 - 4 * q = 1 := by
    linarith [h2, h6]
  have h8 : p^2 = 4 * q + 1 := by
    linarith
  have h9 : p = Real.sqrt (p^2) := by
    rw [Real.sqrt_sq (by positivity)]
  rw [h9]
  rw [h8]
  all_goals positivity