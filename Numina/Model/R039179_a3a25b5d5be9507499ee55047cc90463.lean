import Mathlib

open Int

theorem number_theory_4660 (x : ℝ) : x - 1 < floor x ∧ floor x ≤ x := by
  constructor
  · -- Prove x - 1 < floor x
    -- By the definition of floor, we have x < floor x + 1
    -- Subtracting 1 from both sides gives x - 1 < floor x
    have h2 : x < (floor x + 1 : ℝ) := by exact_mod_cast Int.lt_floor_add_one x
    linarith
  · -- Prove floor x ≤ x
    exact_mod_cast Int.floor_le x