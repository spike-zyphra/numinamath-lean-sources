import Mathlib

theorem algebra_12962 {A B : ℝ} (h : ∀ x, x ^ 2 - 7 * x - 30 ≠ 0 → x - 10 ≠ 0 → x + 3 ≠ 0 → (5 * x + 2) / (x ^ 2 - 7 * x - 30) = A / (x - 10) + B / (x + 3)) :
    (A, B) = (4, 1) := by

  have eq1 := h 0 (by norm_num) (by norm_num) (by norm_num)
  have eq2 := h 1 (by norm_num) (by norm_num) (by norm_num)
  have eq3 := h 2 (by norm_num) (by norm_num) (by norm_num)
  have eq4 := h 3 (by norm_num) (by norm_num) (by norm_num)

  have h1 : A = 4 := by
    field_simp [(show (2 : ℝ) ≠ 0 by norm_num), (show (3 : ℝ) ≠ 0 by norm_num), 
            (show (6 : ℝ) ≠ 0 by norm_num), (show (4 : ℝ) ≠ 0 by norm_num), 
            (show (5 : ℝ) ≠ 0 by norm_num), (show (9 : ℝ) ≠ 0 by norm_num), 
            (show (8 : ℝ) ≠ 0 by norm_num), (show (7 : ℝ) ≠ 0 by norm_num), 
            (show (12 : ℝ) ≠ 0 by norm_num), (show (17 : ℝ) ≠ 0 by norm_num)] at eq1 eq2 eq3 eq4 ⊢
    linarith

  have h2 : B = 1 := by
    field_simp [(show (2 : ℝ) ≠ 0 by norm_num), (show (3 : ℝ) ≠ 0 by norm_num), 
            (show (6 : ℝ) ≠ 0 by norm_num), (show (4 : ℝ) ≠ 0 by norm_num), 
            (show (5 : ℝ) ≠ 0 by norm_num), (show (9 : ℝ) ≠ 0 by norm_num), 
            (show (8 : ℝ) ≠ 0 by norm_num), (show (7 : ℝ) ≠ 0 by norm_num), 
            (show (12 : ℝ) ≠ 0 by norm_num), (show (17 : ℝ) ≠ 0 by norm_num)] at eq1 eq2 eq3 eq4 ⊢
    linarith

  simp [Prod.ext_iff, h1, h2]
  <;> tauto