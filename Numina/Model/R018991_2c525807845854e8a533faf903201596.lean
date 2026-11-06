import Mathlib

theorem inequalities_100689 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a * b ≥ 1) :
    (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) ≥ 16 := by
  have h1 : 0 < a + 1 := by linarith
  have h2 : 0 < b + 1 := by linarith
  have h3 : (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) - 16 ≥ 0 := by
    have h4 : (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) - 16 =
        ((a + 2 * b) * (a + 1) + 2) * ((b + 2 * a) * (b + 1) + 2) / ((a + 1) * (b + 1)) - 16 := by
      field_simp
      <;> ring
    rw [h4]
    have h7 : 0 < (a + 1) * (b + 1) := by positivity
    have h5 : ((a + 2 * b) * (a + 1) + 2) * ((b + 2 * a) * (b + 1) + 2) ≥ 16 * ((a + 1) * (b + 1)) := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1),
          sq_nonneg (a * (b)), sq_nonneg (a + 1), sq_nonneg (b + 1),
          sq_nonneg (a * b - a), sq_nonneg (a * b - b),
          mul_pos ha (show 0 < b by linarith),
          hab,
          mul_nonneg (show 0 ≤ a * b - 1 by nlinarith) (show 0 ≤ a * b - 1 by nlinarith)]

    have eq3 : ((a + 2 * b) * (a + 1) + 2) * ((b + 2 * a) * (b + 1) + 2) / ((a + 1) * (b + 1)) - 16 =
          (((a + 2 * b) * (a + 1) + 2) * ((b + 2 * a) * (b + 1) + 2) - 16 * ((a + 1) * (b + 1))) / ((a + 1) * (b + 1)) := by
      field_simp
      <;> ring
    rw [eq3]
    apply div_nonneg
    linarith
    positivity
  linarith