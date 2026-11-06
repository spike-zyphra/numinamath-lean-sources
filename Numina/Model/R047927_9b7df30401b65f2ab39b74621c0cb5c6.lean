import Mathlib

theorem algebra_199780 (l k : ℝ) (hl : l > 0) (hk : k > 0)
    (h : l / k = l / (k + 3) + l / (k - 3)) :
    l / k = (3 * k + 1) / (k + 3) := by

  have hk1 : k ≠ 0 := by linarith
  have h2 : k + 3 ≠ 0 := by
    by_contra h2
    have : k = -3 := by linarith
    linarith

  have h3 : k - 3 ≠ 0 := by
    by_contra h3
    have : k = 3 := by linarith
    rw [this] at h
    field_simp [show (3 : ℝ) + 3 ≠ 0 by norm_num, show (3 : ℝ) - 3 = (0 : ℝ) by norm_num] at h
    all_goals
      nlinarith

  have eq1 : l / k = l / (k + 3) + l / (k - 3) := h
  have eq2 : l * (k + 3) * (k - 3) = l * k * (k - 3) + l * k * (k + 3) := by
    field_simp [hk1, show k + 3 ≠ 0 by assumption, show k - 3 ≠ 0 by assumption] at eq1 ⊢
    <;> nlinarith [sq_pos_of_pos hk, sq_pos_of_pos hl]

  have eq3 : l * (k^2 - 9) = 2 * l * k^2 := by
    have h5 : l * (k + 3) * (k - 3) = l * k * (k - 3) + l * k * (k + 3) := eq2
    nlinarith [h5]

  have eq4 : -9 * l = l * k^2 := by
    nlinarith [eq3]

  have eq5 : l * k^2 = -9 * l := by
    linarith [eq4]

  have eq6 : l * k^2 + 9 * l = 0 := by
    nlinarith [eq5]

  have eq7 : l * (k^2 + 9) = 0 := by
    nlinarith [eq6]

  have eq8 : k^2 + 9 = 0 := by
    apply (mul_right_inj' (ne_of_gt hl)).mp
    linarith

  have eq9 : k^2 = -9 := by
    nlinarith [eq8]

  have h6 : k^2 ≥ 0 := by
    exact sq_nonneg k

  nlinarith