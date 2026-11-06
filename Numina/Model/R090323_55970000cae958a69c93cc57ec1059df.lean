import Mathlib

theorem algebra_14240 {A B C : ℝ} (h : ∀ x, x ≠ 0 → (x^3 + x) ≠ 0 → (-x^2 + 3 * x - 4) / (x^3 + x) = A / x + (B * x + C) / (x^2 + 1)) :
    A = -4 ∧ B = 3 ∧ C = 3 := by
  have eq1 := h 1 (by norm_num) (by norm_num)
  have eq2 := h (-1) (by norm_num) (by norm_num)
  have eq3 := h 2 (by norm_num) (by norm_num)
  have eq4 := h (-2) (by norm_num) (by norm_num)
  norm_num at eq1 eq2 eq3 eq4
  -- From eq1 and eq2 we can get A = -4
  have hA : A = -4 := by 
    linarith
  -- Solving with eq1 and hA we get b, c
  have hB : B = 3 := by
    linarith [eq1, hA]
  -- Solving with eq1 and hA we get c
  have hC : C = 3 := by
    linarith [eq1, hA]
  exact ⟨hA, hB, hC⟩