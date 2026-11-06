import Mathlib

theorem algebra_7854 (H : ℕ → ℝ) (hH : ∀ n, H n = H (n - 1) * 0.1) (hH0 : H 0 ≠ 0)
    (hH6 : H 5 = 785) : H 0 = 7.85 * 10 ^ 7 := by

  have eq1 : H 5 = H 4 * 0.1 := hH 5
  have eq2 : H 4 = H 3 * 0.1 := hH 4
  have eq3 : H 3 = H 2 * 0.1 := hH 3
  have eq4 : H 2 = H 1 * 0.1 := hH 2
  have eq5 : H 1 = H 0 * 0.1 := hH 1

  rw [eq1] at hH6
  have hH4 : H 4 = 7850 := by
    norm_num at hH6 ⊢
    linarith

  rw [eq2] at hH4
  have hH3 : H 3 = 78500 := by
    norm_num at hH4 ⊢
    linarith

  rw [eq3] at hH3
  have hH2 : H 2 = 785000 := by
    norm_num at hH3 ⊢
    linarith

  rw [eq4] at hH2
  have hH1 : H 1 = 7850000 := by
    norm_num at hH2 ⊢
    linarith

  rw [eq5] at hH1
  norm_num at hH1 ⊢
  linarith