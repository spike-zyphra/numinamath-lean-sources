import Mathlib

theorem algebra_229315 {b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hroots : ∃ x y, x ≠ y ∧ x^2 + b * x + c = 0 ∧ y^2 + b * y + c = 0)
    (D : ℝ) (hD : D = b^2 - 4 * c) :
    ∃! x, (x^2 + b * x + c) + (x - Real.sqrt D)^2 + b * (x - Real.sqrt D) + c = 0 := by 
  rcases hroots with ⟨x, y, hxy, hx, hy⟩
  have hD_pos : b^2 - 4 * c > 0 := by
    have h1 : x^2 + b * x + c = 0 := hx
    have h2 : y^2 + b * y + c = 0 := hy
    have h3 : x ≠ y := hxy
    have h4 : (x - y) * (x + y + b) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h4) with h6 h7
    · -- x - y ≠ 0
      exfalso
      apply h3
      linarith
    · -- x + y + b = 0
      nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by intro h0; apply h3; linarith), sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x + y), sq_nonneg (b)]
  have h2 : Real.sqrt D ≥ 0 := by
    rw [hD]
    apply Real.sqrt_nonneg
  have h3 : Real.sqrt D ^ 2 = D := by
    rw [hD]
    rw [Real.sq_sqrt]
    nlinarith
  use (-b + Real.sqrt D) / 2
  constructor
  · -- Show is root
    nlinarith [Real.sqrt_nonneg D, Real.sq_sqrt (show (0 : ℝ) ≤ D by nlinarith), sq_nonneg (Real.sqrt D), sq_nonneg (b ^ 2 - 4 * c), sq_nonneg (b - Real.sqrt D), sq_nonneg ((-b) + Real.sqrt D), sq_nonneg ((-b) - Real.sqrt D)]
  · -- Show uniqueness
    intro x h_eq
    have eq1 : (x^2 + b * x + c) + (x - Real.sqrt D)^2 + b * (x - Real.sqrt D) + c = 0 := h_eq
    have h7 : (x - (-b + Real.sqrt D) / 2 ) ^ 2 = 0 := by
      nlinarith [Real.sqrt_nonneg D, Real.sq_sqrt (show (0 : ℝ) ≤ D by nlinarith), sq_nonneg (x - (-b + Real.sqrt D ) / 2), sq_nonneg (b - Real.sqrt D), sq_nonneg (Real.sqrt D), sq_nonneg (b ^ 2 - 4 * c), sq_nonneg ((-b) + Real.sqrt D), sq_nonneg ((-b) - Real.sqrt D)]
    have hx : x - (-b + Real.sqrt D) / 2 = 0 := by
      nlinarith
    linarith