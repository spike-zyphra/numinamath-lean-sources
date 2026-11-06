import Mathlib

theorem algebra_296795 (a b : ℝ) (ha : 0 < b) (hb : b < a) :
    a ^ 4 + 32 / (b * (a - b)) ≥ 16 := by
  have h1 : 0 < a - b := by linarith
  have h2 : 0 < b * (a - b) := by positivity
  have h3 : a ^ 4 + 32 / (b * (a - b)) - 16 ≥ 0 := by 
    have h4 : a^4 * (b * (a - b)) + 32 - 16 * (b * (a - b)) ≥ 0 := by
      nlinarith [sq_nonneg (a^2 - 2), sq_nonneg (a^2 - 4), sq_nonneg (a - 2), sq_nonneg (b - 1), sq_nonneg (a - 2*b), sq_nonneg (b*(a - b) - 1), sq_nonneg (a^2), sq_nonneg ((a - b)^2), sq_nonneg ((a - 2)), sq_nonneg ((b - 1)), sq_nonneg ((a - b) - 1), mul_pos (show 0 < b by linarith) (show 0 < a - b by linarith)]
    have h5 : a ^ 4 + 32 / (b * (a - b)) - 16 = (a ^ 4 * (b * (a - b)) + 32 - 16 * (b * (a - b)) ) / (b * (a - b)) := by
      field_simp
      <;> ring_nf
      <;> field_simp [h1, ha]
      <;> ring_nf
    rw [h5]
    apply div_nonneg
    linarith [h4]
    positivity
  linarith [h3]