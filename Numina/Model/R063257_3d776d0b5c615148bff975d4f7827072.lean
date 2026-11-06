import Mathlib

open Polynomial

theorem algebra_3592 {a : ℝ} (h : (C 1 * X^2 + C (-17) * X + C a).roots.toFinset.card = 2 ∧
    ∃ x y, x ≠ y ∧ (C 1 * X^2 + C (-17) * X + C a).eval x = 0 ∧ (C 1 * X^2 + C (-17) * X + C a).eval y = 0 ∧ |x - y| = 9) :
    a = 52 := by

  rcases h with ⟨h₁, h₂⟩
  rcases h₂ with ⟨x, y, h_ne, h₁₁, h₂₂, h_abs⟩
  have eq1 : x^2 - 17 * x + a = 0 := by
    simp [eval_add, eval_pow, eval_mul, eval_C] at h₁₁
    linarith
  have eq2 : y^2 - 17 * y + a = 0 := by
    simp [eval_add, eval_pow, eval_mul, eval_C] at h₂₂
    linarith
  have h_sub : (x - y) * (x + y - 17) = 0 := by
    have h : x^2 - 17 * x + a - (y^2 - 17 * y + a) = 0 := by
      linarith [eq1, eq2]
    nlinarith 
  cases (mul_eq_zero.mp h_sub) with 
  | inl h_zero =>
    exfalso
    exact h_ne (by linarith)
  | inr h_sum =>
    have h_abs_eq : (x - y) ^ 2 = 81 := by
      cases' abs_cases (x - y) with h h
      ·
        nlinarith
      ·
        nlinarith
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by
      intro h_zero
      apply h_ne 
      linarith
    ), h_sum]