import Mathlib

theorem algebra_186649 (x : ℝ) (hx : x ≠ 0) (h : 3 * (x + 1 / x ^ 2) - 7 * (1 + 1 / x) = 0) :
    x = -1 ∨ x = 1 / 3 ∨ x = 3 := by

  have eq1 : 3 * x ^ 3 - 7 * x ^ 2 - 7 * x + 3 = 0 := by
    have eq2 : 3 * (x + 1 / x ^ 2) - 7 * (1 + 1 / x) = (3 * x ^ 3 - 7 * x ^ 2 - 7 * x + 3) / x ^ 2 := by
      field_simp [hx]
      <;> ring
    rw [eq2] at h 
    have hx2 : x ^ 2 ≠ 0 := by
      intro h0
      have h00 : x = 0 := by 
        have h1 : x ^ 2 = 0 := by linarith 
        simp at h1 ⊢ 
        <;> nlinarith 
      contradiction 
    have eq3 : 3 * x ^ 3 - 7 * x ^ 2 - 7 * x + 3 = 0 := by 
      field_simp [hx2] at h 
      all_goals linarith
    linarith
  have eq2 : (x + 1) * (3 * x - 1) * (x - 3) = 0 := by
    nlinarith [eq1]
  cases' (mul_eq_zero.mp eq2) with h3 h4
  cases' (mul_eq_zero.mp h3) with h1 h2
  · -- Case x + 1 = 0, so x = -1 
    left 
    linarith 
  · -- Case 3 * x - 1 = 0, so x = 1/3 
    right 
    left 
    linarith 
  · -- Case x - 3 = 0, so x = 3 
    right 
    right 
    linarith