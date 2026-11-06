import Mathlib

theorem algebra_12456 {k : ℝ} (hk : k ≠ 0) (h : ∃ x y, x^2 + 6 * x + k = 0 ∧ y^2 + 6 * y + k = 0 ∧ x / y = 2) :
    k = 8 := by
  rcases h with ⟨x, y, hx, hy, hxy⟩
  have h1 : y ≠ 0 := by
    by_contra h2
    have h3 : x / y = 0 := by
      rw [h2]
      norm_num
      all_goals linarith
    linarith [hxy, h3]
  
  have h2 : x = 2 * y := by
    have h1' : y ≠ 0 := h1
    field_simp [h1'] at hxy
    linarith
  
  rw [h2] at hx
  
  have eq1 : 4 * y^2 + 12 * y + k = 0 := by
    nlinarith
  
  have eq2 : y^2 + 6 * y + k = 0 := by
    linarith [hy]

  have eq3 : 3 * y^2 + 6 * y = 0 := by
    nlinarith [eq1, eq2]

  have eq4 : y * (y + 2) = 0 := by
    nlinarith [eq3]

  cases' (mul_eq_zero.1 eq4) with hy1 hy2

  · -- y = 0 is a contradiction since we assumed y ≠ 0
    exfalso
    apply h1
    linarith

  · -- y + 2 = 0 so y = -2 and we can compute k
    have hy2' : y = -2 := by linarith
    rw [hy2'] at hy
    nlinarith
  all_goals norm_num
  all_goals nlinarith
  all_goals try linarith
  all_goals nlinarith
  all_goals tauto
  all_goals try { exfalso <;> tauto }
  all_goals nlinarith  -- This handles the final computation to verify that k = 8.