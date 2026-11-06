import Mathlib

theorem algebra_10503 {A B : ℝ} (h : ∀ x, x ≠ 7 ∧ x ≠ -6 → (3 * x + 5) / (x ^ 2 - x - 42) = A / (x - 7) + B / (x + 6)) :
    (A,B)=(2,1) := by
  have eq1 := h 0 ⟨by norm_num, by norm_num⟩
  have eq2 := h 1 ⟨by norm_num, by norm_num⟩
  norm_num at eq1 eq2
  have eq3 : -6 * A + 7 * B = -5 := by
    linarith
  have eq4 : -7 * A + 6 * B = -8 := by
    linarith
  have hB : B = 1 := by 
    linarith [eq3, eq4]
  have hA : A = 2 := by
    linarith [eq3, hB]
  simp [Prod.ext_iff, hA, hB]