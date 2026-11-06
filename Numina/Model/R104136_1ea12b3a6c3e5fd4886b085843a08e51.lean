import Mathlib

theorem algebra_187048 {x y : ℝ} (hy : y ≠ 1 ∧ y ≠ -1) (h1 : 1 / (y - 1) - 1 / (y + 1) = 1 / x)
    (h2 : y ^ 2 - x - 5 = 0) :
    (x, y) = (4, 3) ∨ (x, y) = (4, -3) := by
  have h3 : x ≠ 0 := by
    by_contra h
    rw [h] at h1
    have eq1 : 1 / (y - 1) - 1 / (y + 1) = (0 : ℝ) := by
      simpa using h1
    have eq2 : 1 / (y - 1) = 1 / (y + 1) := by
      linarith
    have eq3 : y + 1 ≠ 0 := by 
      intro h
      apply hy.right
      linarith
    have eq4 : y - 1 ≠ 0 := by 
      intro h
      apply hy.left
      linarith
    -- Cross-multiplying
    field_simp [eq4, eq3] at eq2 ⊢
    all_goals
      nlinarith
  have eq1 : (y - 1) ≠ 0 := by
    intro h
    apply hy.left
    linarith
  have eq2 : (y + 1) ≠ 0 := by
    intro h
    apply hy.right
    linarith
  have eq3 : 2 * x = y ^ 2 - 1 := by
    field_simp [(show y - 1 ≠ 0 by intro h; apply eq1; linarith), 
               (show y + 1 ≠ 0 by intro h; apply eq2; linarith), 
               h3] at h1
    nlinarith
  have eq4 : x = 4 := by
    nlinarith [h2, eq3]
  have eq5 : y ^ 2 = 9 := by
    nlinarith [h2, eq4]
  have hy2 : y = 3 ∨ y = -3 := by
    have h3 : y ^ 2 - 9 = 0 := by nlinarith
    have h4 : (y - 3) * (y + 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h4) with h5 h6
    · left
      linarith
    · right
      linarith
  cases' hy2 with h6 h6
  · left
    simp [eq4, h6]
  · right
    simp [eq4, h6]