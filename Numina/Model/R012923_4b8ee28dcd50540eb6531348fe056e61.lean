import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_152698 (x y : ℝ) (hx : x ≠ y) :
  (cos x - cos y)^2 + (sin x - sin y)^2 < (x - y)^2 := by
  have h1 : (cos x - cos y) ^ 2 + (sin x - sin y) ^ 2 = 2 - 2 * cos (x - y) := by
    have h2 : (cos x - cos y) ^ 2 + (sin x - sin y) ^ 2 = (cos x ^ 2 + sin x ^ 2) + (cos y ^ 2 + sin y ^ 2) - 2 * (cos x * cos y + sin x * sin y) := by
      nlinarith
    have h3 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    have h4 : cos y ^ 2 + sin y ^ 2 = 1 := Real.cos_sq_add_sin_sq y
    have h5 : cos x * cos y + sin x * sin y = cos (x - y) := by
      rw [Real.cos_sub]
      all_goals ring
    rw [h2, h3, h4, h5]
    all_goals nlinarith
  rw [h1]
  have h2 : x - y ≠ 0 := by
    intro h
    apply hx
    linarith
  have h3 : 2 - 2 * cos (x - y) < (x - y) ^ 2 := by
    have h4 : sin ((x - y) / 2) ^ 2 < ((x - y) / 2) ^ 2 := by
      have h14 : |sin ((x - y) / 2)| < |(x - y) / 2| := by
        apply abs_sin_lt_abs
        have h7 : (x - y) / 2 ≠ 0 := by
          intro h
          have h14 : x - y = 0 := by linarith
          tauto
        exact h7
      have h15 : (sin ((x - y) / 2)) ^ 2 < ((x - y) / 2) ^ 2 := by
        have h17 : |sin ((x - y) / 2)| < |(x - y) / 2| := h14
        have h20 : (sin ((x - y) / 2)) ^ 2 = (|sin ((x - y) / 2)|) ^ 2 := by
          rw [sq_abs (sin ((x - y) / 2))]
        have h21 : ((x - y) / 2) ^ 2 = (|(x - y) / 2|) ^ 2 := by
          rw [sq_abs ((x - y) / 2)]
        nlinarith [abs_nonneg (sin ((x - y) / 2)), abs_nonneg ((x - y) / 2)]
      exact h15
    have h8 : 2 - 2 * cos (x - y) = 4 * sin ((x - y) / 2) ^ 2 := by
      have h9 : 2 - 2 * cos (x - y) = 4 * sin ((x - y) / 2) ^ 2 := by
        have h7 : 1 - cos (x - y) = 2 * sin ((x - y) / 2) ^ 2 := by
          have h8 : 1 - cos (x - y) = 2 * sin ((x - y) / 2) ^ 2 := by
            rw [Real.sin_sq_eq_half_sub]
            ring_nf
          exact h8
        linarith
      exact h9
    have h9 : (x - y) ^ 2 = 4 * ((x - y) / 2) ^ 2 := by
      nlinarith
    rw [h8, h9]
    have h10 : 4 * sin ((x - y) / 2) ^ 2 < 4 * ((x - y) / 2) ^ 2 := by
      have h11 : sin ((x - y) / 2) ^ 2 < ((x - y) / 2) ^ 2 := h4
      nlinarith [show sin ((x - y) / 2) ^ 2 ≥ 0 by positivity, show ((x - y) / 2) ^ 2 ≥ 0 by positivity]
    exact h10
  exact h3