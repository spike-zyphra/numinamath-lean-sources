import Mathlib

theorem algebra_21511 {A B : ℝ} (h : ∀ x, x + 2 ≠ 0 → x - 1 ≠ 0 → (4 * x + 5) / (x ^ 2 + x - 2) = A / (x + 2) + B / (x - 1)) :
    ∀ x, x + 1 ≠ 0 → x - 2 ≠ 0 → B / (x + 1) - A / (x - 2) = (2 * x - 7) / ((x + 1) * (x - 2)) := by
  intro x h1 h2
  have eq1 := h 0 (by norm_num) (by norm_num)
  have eq2 := h 2 (by norm_num) (by norm_num)
  field_simp at eq1 eq2
  have hA : A = 1 := by
    linarith
  have hB : B = 3 := by 
    linarith
  rw [hA, hB]
  field_simp [(show x + 1 ≠ 0 by intro h3; apply h1; linarith), 
              (show x - 2 ≠ 0 by intro h3; apply h2; linarith)]
  ring