import Mathlib

theorem algebra_304382 {a b c p1 p2 m1 m2 : ℝ} (ha : a > b) (hb : b > c)
    (h : a * 2 ^ 2 + b * 2 + c = 0) (h' : a * m1 ^ 2 + b * m1 + c = p1)
    (h'' : a * m2 ^ 2 + b * m2 + c = p2) (h''' : p1 * p2 - c * p1 + a * p2 - a * c = 0) :
    ∃ x, x = m1 + 5 ∨ x = m2 + 5 ∧ a * x ^ 2 + b * x + c > 0 := by
  have hc : c = -4 * a - 2 * b := by
    linarith
  have h4 : (p1 + a) * (p2 + 4 * a + 2 * b) = 0 := by
    have eq1 : p1 * p2 - c * p1 + a * p2 - a * c = 0 := by
      linarith
    rw [hc] at eq1
    nlinarith
  have h5 : (p1 + a) * (p2 - c) = 0 := by
    have eq1 : (p1 + a) * (p2 + 4 * a + 2 * b) = 0 := h4
    have eq2 : p2 + 4 * a + 2 * b = p2 - c := by
      linarith [hc]
    rw [eq2] at eq1
    linarith
  cases' (mul_eq_zero.1 h5) with h51 h52
  · -- Case where p1 + a = 0, so p1 = -a
    have hp1 : p1 = -a := by linarith
    use m1 + 5
    left
    all_goals
      nlinarith [sq_nonneg (m1 + 5), sq_nonneg (a - b), sq_nonneg (b - c), sq_pos_of_pos (sub_pos.mpr ha), sq_pos_of_pos (sub_pos.mpr hb), sq_nonneg (a), sq_nonneg (b - c)]
  · -- Case where p2 - c = 0, so p2 = c
    have hp2 : p2 = c := by linarith
    use m2 + 5
    right
    constructor
    · -- Show that x = m2 + 5
      norm_num
    · -- Show that the polynomial is positive
      nlinarith [sq_nonneg (m2 + 5), sq_nonneg (a - b), sq_nonneg (b - c), sq_pos_of_pos (sub_pos.mpr ha), sq_pos_of_pos (sub_pos.mpr hb), sq_nonneg (a), sq_nonneg (b - c)]