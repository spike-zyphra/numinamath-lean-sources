import Mathlib

theorem algebra_1559 {x : ℝ} (hx : x ≠ 0) (h : 0.5 * x / 3 + 0.5 * x / 2 = x / y) :
    y = 2.4 := by
  have eq1 : 0.5 * x / 3 + 0.5 * x / 2 = (5 / 12) * x := by
    ring_nf
  rw [eq1] at h
  have eq2 : y ≠ 0 := by
    by_contra h1
    rw [h1] at h
    field_simp [hx] at h
    all_goals linarith
  have eq3 : (5 / 12) * x * y = x := by
    have h1 : y ≠ 0 := eq2
    field_simp [h1] at h
    linarith
  have eq4 : x * ((5 / 12) * y - 1) = 0 := by
    linarith
  cases' (mul_eq_zero.mp eq4) with h5 h6
  · -- x = 0
    exfalso
    apply hx
    exact h5
  · -- (5 / 12) * y - 1 = 0
    have eq7 : (5 / 12) * y = 1 := by linarith
    have eq8 : y = (12 / 5 : ℝ) := by
      linarith
    rw [eq8]
    all_goals norm_num