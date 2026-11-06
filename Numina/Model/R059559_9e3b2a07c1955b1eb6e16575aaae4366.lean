import Mathlib

theorem algebra_7361 {A B C : ℝ} (h : ∀ x, x ≠ 0 ∧ x ≠ 3 ∧ x ≠ -2 → (x^2 - x + 2)/(x*(x-3)*(x+2)) = A/x + B/(x-3) + C/(x+2)) :
    A*B*C = -32/225 := by
  have eq1 := h 1 ⟨by norm_num, by norm_num, by norm_num⟩
  have eq2 := h 4 ⟨by norm_num, by norm_num, by norm_num⟩
  have eq3 := h 5 ⟨by norm_num, by norm_num, by norm_num⟩
  field_simp at eq1 eq2 eq3
  ring_nf at eq1 eq2 eq3

  have hA : A = -1 / 3 := by
    nlinarith

  have hB : B = 8 / 15 := by
    nlinarith [eq1, eq2, eq3, hA]

  have hC : C = 4 / 5 := by
    nlinarith [eq1, eq2, eq3, hA, hB]

  rw [hA, hB, hC]
  norm_num
  <;> nlinarith
  <;> ring_nf <;> nlinarith