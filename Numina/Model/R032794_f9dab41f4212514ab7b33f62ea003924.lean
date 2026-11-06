import Mathlib

theorem algebra_135789 :
    IsLeast {n | ∃ x y z : ℝ, n = x^2 + y^2 + z^2 ∧ x^3 + y^3 + z^3 - 3 * x * y * z = 1} 1 := by
  constructor 
  · -- Show that 1 is in the set. We pick (1, 0, 0) which satisfies the constraint and value 1.
    use 1, 0, 0
    norm_num
  · -- Let n be an element in the set. We need to show 1 ≤ n.
    intro n hn
    rcases hn with ⟨x, y, z, hn, h_eq⟩
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 0), sq_nonneg (z - 0), 
          sq_nonneg (y - 0), sq_nonneg (z - 0), 
          sq_nonneg (x + y + z - 1), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
          sq_nonneg (x * y + y * z + z * x - 0)]