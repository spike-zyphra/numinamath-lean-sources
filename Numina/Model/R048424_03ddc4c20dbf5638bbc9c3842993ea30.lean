import Mathlib

open Real

theorem algebra_302396 {x : ℝ} (hx : x = 1 / (sqrt 3 - 2)) :
    x^3 + 4 * x^2 - 2 * x - 6 = 3 * sqrt 3 := by
  have h1 : x = -sqrt 3 - 2 := by
    rw [hx]
    have h2 : sqrt 3 - 2 ≠ 0 := by
      have h3 : sqrt 3 < 2 := by
        rw [Real.sqrt_lt] <;> norm_num
        <;> linarith
      have h4 : sqrt 3 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)
      have h5 : sqrt 3 - 2 < 0 := by linarith
      have h6 : sqrt 3 - 2 ≠ 0 := by
        intro h
        have : sqrt 3 - 2 = 0 := by linarith
        have : sqrt 3 = 2 := by linarith
        have h7 : (sqrt 3) ^ 2 = (2 : ℝ) ^ 2 := by rw [this]
        norm_num at h7
        all_goals linarith [Real.sqrt_nonneg 3]
      exact h6
    field_simp [h2]
    <;> ring_nf <;> norm_num
    <;> ring
  rw [h1]
  ring_nf
  <;> simp [pow_two, pow_three, mul_add, add_mul, mul_comm, mul_assoc, Real.sqrt_mul_self]
  <;> ring_nf <;> norm_num
  <;> ring