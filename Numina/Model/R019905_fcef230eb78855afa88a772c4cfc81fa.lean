import Mathlib

theorem algebra_21067 (a b c : ℝ) (ha : a ≠ 0) (hvertex : ∀ x, a * x ^ 2 + b * x + c = a * (x - 4) ^ 2 - 5)
    (hx1 : ∃ x1, x1 > 0 ∧ a * x1 ^ 2 + b * x1 + c = 0) (hx2 : ∃ x2, x2 < 0 ∧ a * x2 ^ 2 + b * x2 + c = 0) :
    a > 0 := by
  have eq1 : c = 16 * a - 5 := by
    specialize hvertex 0
    linarith
  have eq2 : b = -8 * a := by
    have eq3 := hvertex 1
    have eq4 := hvertex 2
    simp only [show (1 : ℝ) ^ 2 = 1 by norm_num, show (2 : ℝ) ^ 2 = 4 by norm_num] at eq3 eq4
    linarith [eq1]
  rcases hx1 with ⟨x1, hx1_pos, hx1_eq⟩
  rcases hx2 with ⟨x2, hx2_neg, hx2_eq⟩
  have eq5 : a * x1 ^ 2 + b * x1 + c = 0 := by
    linarith
  have eq6 : a * x2 ^ 2 + b * x2 + c = 0 := by
    linarith
  rw [show b = -8 * a by linarith [eq2]] at eq5 eq6
  rw [show c = 16 * a - 5 by linarith [eq1]] at eq5 eq6
  have eq7 : a * (x1 - 4) ^ 2 = 5 := by
    nlinarith
  have eq8 : a * (x2 - 4) ^ 2 = 5 := by
    nlinarith
  nlinarith [sq_pos_of_pos hx1_pos, sq_pos_of_neg hx2_neg, sq_nonneg (x1 - 4), sq_nonneg (x2 - 4)]