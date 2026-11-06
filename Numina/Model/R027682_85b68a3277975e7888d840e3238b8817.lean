import Mathlib

theorem algebra_21992 {x : ℝ} (hx : x ≠ 2) (hx1 : x > 0) (h : x = 1 / (2 + 1 / (x - 2))) :
    x = 1 := by
  have h1 : x - 2 ≠ 0 := by
    intro h2
    apply hx
    linarith
  have h2 : 2 + 1 / (x - 2) = (2 * x - 3) / (x - 2) := by
    field_simp [h1]
    <;> ring
  have h3 : x = (x - 2) / (2 * x - 3) := by
    rw [h2] at h
    field_simp [(show 2 * x - 3 ≠ 0 by
      by_contra h4
      have h5 : x = 3 / 2 := by linarith
      rw [h5] at h
      norm_num [h1] at h
      all_goals
        nlinarith
    )] at h ⊢
    <;> nlinarith
  have h4 : 2 * x - 3 ≠ 0 := by
    by_contra h4
    have h5 : x = 3 / 2 := by linarith
    rw [h5] at h3
    norm_num [h1] at h3
    all_goals
      nlinarith
  have h5 : x * (2 * x - 3) = x - 2 := by
    field_simp [h4] at h3
    nlinarith
  have h6 : 2 * x^2 - 4 * x + 2 = 0 := by
    nlinarith
  have h7 : (x - 1)^2 = 0 := by
    nlinarith
  have h8 : x - 1 = 0 := by
    apply pow_eq_zero 
    exact h7
  linarith