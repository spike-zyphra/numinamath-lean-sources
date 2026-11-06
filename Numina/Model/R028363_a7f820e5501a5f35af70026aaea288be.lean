import Mathlib

open BigOperators Real Set

theorem algebra_210647 :
  IsLeast {n : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 5 ∧ n = x^2 + y^2 + 2 * z^2 - x^2 * y^2 * z} (-6) := by
  constructor
  · -- Show -6 in the set
    use 2, 2, 1
    norm_num
  · -- Show -6 is the least element in the set
    intro n hn 
    rcases hn with ⟨x, y, z, hx, hy, hz, h_eq1, hn⟩
    have h_eq2 : x ^ 2 + y ^ 2 + 2 * z ^ 2 - x^2 * y^2 * z ≥ -6 := by
      have h_eq3 : x ^ 2 + y ^ 2 + 2 * z ^ 2 + 6 ≥ x ^ 2 * y ^ 2 * z := by
        have h1 : z = 5 - x - y := by linarith
        rw [h1]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg ((5 - x - y) - 1),
                sq_nonneg (x * y - 4), sq_nonneg ((5 - x - y) * x - 2), sq_nonneg ((5 - x - y) * y - 2),
                mul_pos hx hy, mul_pos hx (show 0 < 5 - x - y by nlinarith), mul_pos hy (show 0 < 5 - x - y by nlinarith),
                mul_pos (mul_pos hx hy) (show 0 < 5 - x - y by nlinarith)]
      linarith
    linarith [hn, h_eq2]