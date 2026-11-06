import Mathlib

theorem algebra_6929 (d r s : ℝ) (h₀ : d = 15) (h₁ : r > 0) (h₂ : s > 0)
    (h₃ : d / (r + s) = d / (r - s) - 5) (h₄ : d / (2 * r + s) = d / (2 * r - s) - 1) :
    s = 2 := by
  rw [h₀] at h₃ h₄
  have eq1 : r - s ≠ 0 := by
    by_contra h
    have : s = r := by linarith
    rw [this] at h₃
    field_simp [(show r + r ≠ 0 by nlinarith)] at h₃
    all_goals nlinarith
  have eq2 : r + s ≠ 0 := by
    by_contra h
    have : r = -s := by linarith
    nlinarith
  have eq3 : 2 * r - s ≠ 0 := by
    by_contra h
    have h5 : s = 2 * r := by linarith
    rw [h5] at h₄
    field_simp [(show 2 * r + 2 * r ≠ 0 by nlinarith)] at h₄
    all_goals nlinarith
  have eq4 : 2 * r + s ≠ 0 := by
    by_contra h
    have : s = -2 * r := by linarith
    nlinarith
  have eq5 : 15 * (r - s) = 15 * (r + s) - 5 * (r + s) * (r - s) := by
    have h5 : r - s ≠ 0 := eq1
    have h6 : r + s ≠ 0 := eq2
    field_simp [h5, h6] at h₃ ⊢
    nlinarith
  have eq6 : 15 * (2 * r - s) = 15 * (2 * r + s) - (2 * r + s) * (2 * r - s) := by
    have h5 : 2 * r - s ≠ 0 := eq3
    have h6 : 2 * r + s ≠ 0 := eq4
    field_simp [h5, h6] at h₄ ⊢
    nlinarith
  have eq7 : r^2 - s^2 - 6 * s = 0 := by
    nlinarith [eq5]
  have eq8 : 4 * r^2 - s^2 - 30 * s = 0 := by
    nlinarith [eq6]
  -- Subtract eq7 from eq8
  have eq9 : 3 * r^2 - 24 * s = 0 := by
    nlinarith [eq7, eq8]
  -- Simplify eq9 to get r² = 8 * s
  have eq10 : r^2 = 8 * s := by
    nlinarith [eq9]
  -- From eq7: r² = s² + 6 * s
  have eq11 : r^2 = s^2 + 6 * s := by
    nlinarith [eq7]
  -- Now set s² + 6 * s = 8 * s
  -- s² - 2 * s = 0
  have eq12 : s^2 - 2 * s = 0 := by
    nlinarith [eq10, eq11]
  -- s * (s - 2) = 0
  have eq13 : s * (s - 2) = 0 := by
    nlinarith [eq12]
  cases' (mul_eq_zero.mp eq13) with h14 h15
  · -- s = 0 is impossible because s > 0
    linarith
  · -- s - 2 = 0 so s = 2
    linarith