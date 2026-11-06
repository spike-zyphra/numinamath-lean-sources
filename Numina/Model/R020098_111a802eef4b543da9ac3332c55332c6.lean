import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12409 :
  IsLeast {d | ∃ x y, d = sqrt ((x - (1 + y^2))^2 + (y + x^2 + 1)^2)} (3 * sqrt 2 / 4) := by
  constructor
  · -- Show that 3 * sqrt 2 / 4 is in the set
    use (1 / 2)
    use (-1 / 2)
    have h1 : Real.sqrt ((1 / 2 - (1 + (-1 / 2) ^ 2)) ^ 2 + (-1 / 2 + (1 / 2) ^ 2 + 1) ^ 2) = 3 * Real.sqrt 2 / 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
      <;> ring
      <;> norm_num
    linarith [h1]
  · -- Show that 3 * sqrt 2 / 4 is the least element in the set
    intro d hd
    rcases hd with ⟨x, y, h_eq⟩
    have h2 : Real.sqrt ((x - (1 + y ^ 2)) ^ 2 + (y + x ^ 2 + 1) ^ 2) ≥ 3 * Real.sqrt 2 / 4 := by
      have h3 : (x - (1 + y ^ 2)) ^ 2 + (y + x ^ 2 + 1) ^ 2 ≥ 9 / 8 := by
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (y ^ 2 - 1 / 4), sq_nonneg (x + 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x + y), sq_nonneg (x - y)]
      have h4 : Real.sqrt ((x - (1 + y ^ 2)) ^ 2 + (y + x ^ 2 + 1) ^ 2) ≥ Real.sqrt (9 / 8) := Real.sqrt_le_sqrt (by linarith)
      have h5 : Real.sqrt (9 / 8) = 3 * Real.sqrt 2 / 4 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
        <;> ring
        <;> norm_num
      nlinarith [h4, h5]
    linarith [h2, h_eq]