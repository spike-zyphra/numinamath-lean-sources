import Mathlib

theorem algebra_5409 (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (h : a = 3) (h1 : b = a * r) (h2 : c = b * r) (h3 : d = c * r) (h4 : 9 = d * r):
    c ^ 2 / (3 * b * d * 9) = 1 / 27 := by

  have ha' : a = 3 := h

  have hb : b = 3 * r := by
    rw [h1, ha']
    all_goals nlinarith

  have hc : c = 3 * r^2 := by
    rw [h2, hb]
    all_goals ring

  have hd : d = 3 * r^3 := by
    rw [h3, hc]
    all_goals ring

  have hr4 : r^4 = 3 := by
    rw [hd] at h4
    nlinarith [sq_nonneg (r^2), sq_nonneg (r), mul_pos ha hr]

  have eq1 : c ^ 2 = 9 * r^4 := by
    rw [hc]
    ring_nf

  have eq2 : 3 * b * d * 9 = 243 * r^4 := by
    rw [hb, hd]
    ring_nf

  rw [eq1, eq2]

  have hr4_ne_zero : r^4 ≠ 0 := by
    nlinarith [pow_pos hr 4]

  field_simp [hr4_ne_zero]
  <;> nlinarith [hr4]