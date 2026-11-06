import Mathlib

open Real Set

theorem algebra_299315 :
    IsLeast {s : ℝ | ∃ x y z w : ℝ, s = x^2 + y^2 + z^2 + w^2 + (x + y + z + w)^2 ∧ x + 2 * y + 3 * z + 4 * w = 1} (1 / 10) := by 
  constructor
  · -- First part: show that 1/10 is in the set.
    use -1 / 10, 0, 1 / 10, 1 / 5
    constructor 
    · -- Compute s
      norm_num 
    · -- Verify the constraint
      norm_num 
  · -- Second part: show minimality of 1/10.
    intro s hs 
    rcases hs with ⟨x, y, z, w, h1, h2⟩ 
    have h3 : x^2 + y^2 + z^2 + w^2 + (x + y + z + w)^2 ≥ 1 / 10 := by 
      nlinarith [sq_nonneg (x + 1 / 10), sq_nonneg (y - 0), sq_nonneg (z - 1 / 10), sq_nonneg (w - 1 / 5), 
          sq_nonneg (x + y + z + w - 1 / 5), 
          mul_self_nonneg (x + 2 * y + 3 * z + 4 * w - 1)]
    linarith