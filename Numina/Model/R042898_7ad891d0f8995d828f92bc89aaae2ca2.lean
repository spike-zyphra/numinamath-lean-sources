import Mathlib

open Real

theorem algebra_167853 {x y : ℝ} (hx : x > 0) (hy : y - logb 3 x = 1) (h : x^y = 3^12) :
    (x = 1 / 81 ∧ y = -3) ∨ (x = 27 ∧ y = 4) := by
  have eq1 : y = logb 3 x + 1 := by
    linarith
  have eq2 : x ^ y = 3 ^ 12 := by
    simpa using h
  have eq3 : logb 3 (x ^ y) = logb 3 (3 ^ 12) := by
    rw [eq2]
  have eq4 : logb 3 (x ^ y) = y * logb 3 x := by
    rw [logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith
  have eq5 : logb 3 (3 ^ 12) = 12 := by
    rw [logb_pow]
    all_goals norm_num
  rw [eq4, eq5] at eq3
  rw [eq1] at eq3
  have h1 : (logb 3 x) ^ 2 + logb 3 x - 12 = 0 := by
    nlinarith
  have h2 : (logb 3 x - 3) * (logb 3 x + 4) = 0 := by
    nlinarith [h1]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case $\logb 3 x - 3 = 0$, i.e., $\logb 3 x = 3$.
    have h5 : logb 3 x = 3 := by linarith
    have hx1 : x = 27 := by
      have h5' : x = (3 : ℝ) ^ (logb 3 x : ℝ) := by
        field_simp [hx]
      rw [h5] at h5'
      norm_num at h5' ⊢
      linarith
    have hy1 : y = 4 := by
      rw [eq1]
      linarith [h5]
    right
    exact ⟨hx1, hy1⟩
  · -- Case $\logb 3 x + 4 = 0$, i.e., $\logb 3 x = -4$.
    have h6 : logb 3 x = -4 := by linarith
    have hx2 : x = 1 / 81 := by
      have h6' : x = (3 : ℝ) ^ (logb 3 x : ℝ) := by
        field_simp [hx]
      rw [h6] at h6'
      norm_num at h6' ⊢
      linarith
    have hy2 : y = -3 := by
      rw [eq1]
      linarith [h6]
    left
    exact ⟨hx2, hy2⟩