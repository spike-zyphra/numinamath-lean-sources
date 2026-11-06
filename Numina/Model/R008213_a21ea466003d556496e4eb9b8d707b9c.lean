import Mathlib

  theorem algebra_209457 {a r : ℚ} (ha : a > 0) (hr : r > 0) (h5 : a * r^4 - a * r^3 = 576) (h2 : a * r - a = 9) : a + a * r + a * r^2 + a * r^3 + a * r^4 = 1023 := by
  have eq2 : a * (r - 1) = 9 := by
    linarith
  have eq1 : a * r^4 - a * r^3 = a * r^3 * (r - 1) := by
    ring
  rw [eq1] at h5
  have eq3 : a * r^3 * (r - 1) = 9 * r^3 := by
    calc
      a * r^3 * (r - 1) = (a * (r - 1)) * r^3 := by ring
      _ = 9 * r^3 := by rw [eq2]
  have hr3 : r^3 = 64 := by
    nlinarith [eq3, h5]
  have hr_eq : r = 4 := by
    have h1 : r^3 - 64 = 0 := by
      nlinarith [hr3]
    have h2 : r^3 - 64 = (r - 4) * (r^2 + 4 * r + 16) := by ring
    rw [h2] at h1
    cases' (mul_eq_zero.1 h1) with h4 h5
    · -- Case r - 4 = 0, so r = 4
      linarith
    · -- Case r^2 + 4 r + 16 = 0
      have h6 : r^2 + 4 * r + 16 > 0 := by
        nlinarith [sq_nonneg (r + 2)]
      nlinarith [h6]
  have ha_eq : a = 3 := by
    rw [hr_eq] at h2
    nlinarith
  rw [ha_eq, hr_eq]
  norm_num