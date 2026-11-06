import Mathlib

theorem algebra_8079 {x y : ℝ} (hx : |x| = 5) (hy : |y| = 4)
    (hxy : |y - x| = y - x) :
    x^2 + 2 * x * y + y^2 = 1 ∨ x^2 + 2 * x * y + y^2 = 81 := by
  have hx_cases : (x = 5 ∨ x = -5) := by
    cases eq_or_eq_neg_of_abs_eq hx with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  have hy_cases : (y = 4 ∨ y = -4) := by
    cases eq_or_eq_neg_of_abs_eq hy with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  cases hx_cases with
  | inl hx_pos =>
    cases hy_cases with
    | inl hy_pos =>
      exfalso
      rw [show y = 4 by linarith [hy_pos], show x = 5 by linarith [hx_pos]] at hxy
      norm_num at hxy
    | inr hy_neg =>
      exfalso
      rw [show y = -4 by linarith [hy_neg], show x = 5 by linarith [hx_pos]] at hxy
      norm_num at hxy
  | inr hx_neg =>
    cases hy_cases with
    | inl hy_pos =>
      left
      rw [show x = -5 by linarith [hx_neg], show y = 4 by linarith [hy_pos]]
      norm_num
    | inr hy_neg =>
      right
      rw [show x = -5 by linarith [hx_neg], show y = -4 by linarith [hy_neg]]
      norm_num