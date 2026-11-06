import Mathlib

open scoped BigOperators

theorem algebra_5872 {u v : ℝ × ℝ} :
  (u.1 * v.2 - u.2 * v.1 ≠ 0) ↔ (u.1 + v.1) * (u.2 - v.2) - (u.2 + v.2) * (u.1 - v.1) ≠ 0 := by
  constructor
  · -- Forward implication: original determinant non-zero implies transformed is non-zero
    intro h
    have h1 : (u.1 + v.1) * (u.2 - v.2) - (u.2 + v.2) * (u.1 - v.1) = -2 * (u.1 * v.2 - u.2 * v.1) := by
      ring
    have h2 : -2 * (u.1 * v.2 - u.2 * v.1) ≠ 0 := by
      intro h3
      -- Assume h3: -2 * (u.1 * v.2 - u.2 * v.1) = 0
      have h4 : u.1 * v.2 - u.2 * v.1 = 0 := by
        linarith
      contradiction
    -- Now rewrite using h1 to express the transformed determinant
    rw [h1] at *
    -- Since h2 shows that -2 * (u.1 * v.2 - u.2 * v.1) ≠ 0, we're done
    simpa using h2
  · -- Backward implication: transformed determinant non-zero implies original is non-zero
    intro h
    have h1 : (u.1 + v.1) * (u.2 - v.2) - (u.2 + v.2) * (u.1 - v.1) = -2 * (u.1 * v.2 - u.2 * v.1) := by
      ring
    have h2 : -2 * (u.1 * v.2 - u.2 * v.1) ≠ 0 := by
      rw [← h1] at *
      simpa using h
    -- Now use h2 to derive that the original determinant is non-zero
    have h3 : u.1 * v.2 - u.2 * v.1 ≠ 0 := by
      by_contra h4
      -- Assume h4: u.1 * v.2 - u.2 * v.1 = 0
      have h5 : -2 * (u.1 * v.2 - u.2 * v.1) = 0 := by
        rw [h4]
        norm_num
      contradiction
    exact h3