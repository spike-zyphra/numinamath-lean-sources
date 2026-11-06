import Mathlib


theorem algebra_317855 {a b c x1 x2 : ℝ} (hroots : (x1 - a) * (x1 - b) - c * x1 = 0 ∧ (x2 - a) * (x2 - b) - c * x2 = 0)
    (hx12 : x1 ≠ x2) :
    (a - x1) * (a - x2) + c * a = 0 ∧ (b - x1) * (b - x2) + c * b = 0 := by
  rcases hroots with ⟨h1, h2⟩
  constructor
  · -- Show (a - x1) * (a - x2) + c * a = 0
    nlinarith [sq_pos_of_ne_zero ((show (x1 - x2) ≠ 0 by intro h0; apply hx12; linarith)), sq_nonneg (x1 - x2), sq_nonneg (x1 - a), sq_nonneg (x1 - b), sq_nonneg (x2 - a), sq_nonneg (x2 - b)]
  · -- Show (b - x1) * (b - x2) + c * b = 0
    nlinarith [sq_pos_of_ne_zero ((show (x1 - x2) ≠ 0 by intro h0; apply hx12; linarith)), sq_nonneg (x1 - x2), sq_nonneg (x1 - a), sq_nonneg (x1 - b), sq_nonneg (x2 - a), sq_nonneg (x2 - b)]