import Mathlib

theorem algebra_319947 {x : ℝ} (hx : x ≠ 0) (h : x + 1 / x = 2 * Real.cos 0) (n : ℕ) :
    x ^ n + 1 / x ^ n = 2 * Real.cos (n * 0) := by
  have h_cos : Real.cos 0 = 1 := Real.cos_zero
  rw [h_cos] at h
  -- Solve for x: x + 1/x = 2 => (x - 1)^2 = 0 => x = 1
  have hx_eq : x = 1 := by
    field_simp [hx] at h
    have h_eq : (x - 1) ^ 2 = 0 := by
      nlinarith
    have h_zero : x - 1 = 0 := by
      rw [sq_eq_zero_iff] at h_eq
      exact h_eq
    linarith
  rw [hx_eq]
  have h_cos2 : Real.cos (n * (0 : ℝ)) = 1 := by
    simp
  simp [h_cos2]
  all_goals norm_num