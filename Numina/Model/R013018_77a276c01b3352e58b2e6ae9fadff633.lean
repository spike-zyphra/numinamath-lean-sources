import Mathlib

theorem inequalities_87534 (a b c : ℝ) (ha : 0 < a) (h : 12 * a + 5 * b + 2 * c > 0)
    (h1 : ∃ x1 x2 : ℝ, x1 ∈ Set.Ioo 2 3 ∧ x2 ∈ Set.Ioo 2 3 ∧ x1 ≠ x2 ∧ a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0) :
    False := by
  rcases h1 with ⟨x1, x2, hx1, hx2, hneq, he1, he2⟩
  rcases hx1 with ⟨hx1l, hx1r⟩
  rcases hx2 with ⟨hx2l, hx2r⟩
  have h4 : x1 - x2 ≠ 0 := by
    intro heq
    apply hneq
    linarith
  have h3 : a * (x1 + x2) + b = 0 := by
    have eq1 : a * x1 ^ 2 + b * x1 + c - (a * x2 ^ 2 + b * x2 + c) = 0 := by linarith [he1, he2]
    have eq2 : a * (x1 ^ 2 - x2 ^ 2) + b * (x1 - x2) = 0 := by
      nlinarith
    have eq3 : (x1 - x2) * (a * (x1 + x2) + b) = 0 := by
      ring_nf at eq2 ⊢
      nlinarith
    cases' (mul_eq_zero.mp eq3) with h4' h5
    · -- h4' : x1 - x2 = 0
      exfalso
      apply h4
      linarith
    · -- h5 : a * (x1 + x2) + b = 0
      linarith
  nlinarith [sq_nonneg (x1 - 2.5), sq_nonneg (x2 - 2.5), sq_pos_of_pos ha, mul_pos ha (show 0 < (3 - x1) by linarith), mul_pos ha (show 0 < (x1 - 2) by linarith), mul_pos ha (show 0 < (3 - x2) by linarith), mul_pos ha (show 0 < (x2 - 2) by linarith), sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by tauto), mul_nonneg (show (0 : ℝ) ≤ x1 - 2 by linarith) (show (0 : ℝ) ≤ 3 - x1 by linarith), mul_nonneg (show (0 : ℝ) ≤ x2 - 2 by linarith) (show (0 : ℝ) ≤ 3 - x2 by linarith), sq_nonneg (x1 - x2)]