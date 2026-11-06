import Mathlib

open Complex ComplexConjugate

/-Determine the complex number $z$ satisfying the equation $2z-3i\bar{z}=-7+3i$.  Note that $\bar{z}$ denotes the conjugate of $z$.-/
theorem algebra_15454 {z : ℂ} : 2 * z - 3 * I * conj z = - 7 + 3 * I ↔ z = 1 + 3 * I := by
-- Break "iff"
  constructor
-- Use Complex.ext_iff to rewrite both the assumption and goal, then use "linarith" to finish the goal
  · intro h; rw [Complex.ext_iff] at h; norm_num at h
    rcases h with ⟨h1, h2⟩; rw [Complex.ext_iff]; norm_num
    constructor; any_goals linarith
-- Conversely, check that $z=1+3I$ satisfies the assumption
  intro h; rw [h]; rw [Complex.ext_iff]; norm_num