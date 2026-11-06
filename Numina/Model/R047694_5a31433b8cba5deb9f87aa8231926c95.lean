import Mathlib

theorem algebra_297827 {a : ℝ} (ha : a ≠ 0) (h : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1 < 2 / 5 ∧ 2 / 5 < x2 ∧
    a * x1 ^ 2 + (a + 2) * x1 + 9 * a = 0 ∧ a * x2 ^ 2 + (a + 2) * x2 + 9 * a = 0) :
    -2 / 11 < a ∧ a < 0 := by 
  rcases h with ⟨x1, x2, hx12, hx1, hx2, he1, he2⟩
  have h3 : x1 < 2 / 5 := hx1
  have h4 : 2 / 5 < x2 := hx2
  have h5 : x1 < x2 := by linarith
  have h6 : x1 - x2 < 0 := by linarith
  have eq1 : a * (x1 + x2) + a + 2 = 0 := by
    have eq2 : a * x1 ^ 2 + (a + 2) * x1 + 9 * a = 0 := he1
    have eq3 : a * x2 ^ 2 + (a + 2) * x2 + 9 * a = 0 := he2
    have eq4 : a * (x1 ^ 2 - x2 ^ 2) + (a + 2) * (x1 - x2) = 0 := by
      nlinarith
    have h7 : x1 - x2 ≠ 0 := by 
      intro h'
      apply hx12
      linarith
    have eq5 : a * (x1 + x2) + a + 2 = 0 := by
      apply (mul_left_inj' h7).mp
      linarith
    linarith
  have eq2 : a * (x1 ^ 2 + x2 ^ 2) + (a + 2) * (x1 + x2) + 18 * a = 0 := by 
    nlinarith
  constructor
  · -- Proof that $-2/11 < a$
    nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_pos (show (0 : ℝ) < x2 - x1 by linarith), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (x1 - 2 / 5), sq_nonneg (x2 - 2 / 5), sq_nonneg (a), sq_nonneg (x1 * x2)]
  · -- Proof that $a < 0$
    nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_pos (show (0 : ℝ) < x2 - x1 by linarith), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (x1 - 2 / 5), sq_nonneg (x2 - 2 / 5), sq_nonneg (a), sq_nonneg (x1 * x2)]