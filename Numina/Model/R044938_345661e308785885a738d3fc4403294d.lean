import Mathlib

open Real

theorem algebra_249057 {a b c : ℝ} 
    (h1 : 1 - a * b ≠ 0) (h2 : 1 + c * a ≠ 0)
    (h3 : 1 - (a + b) / (1 - a * b) * (c - a) / (1 + c * a) ≠ 0) 
    (h4 : 1 - b * c ≠ 0) :
    ((a + b) / (1 - a * b) + (c - a) / (1 + c * a)) /
    (1 - (a + b) / (1 - a * b) * (c - a) / (1 + c * a)) =
    (b + c) / (1 - b * c) := by

  have eq1 : ((a + b) / (1 - a * b) + (c - a) / (1 + c * a)) =
      ((b + c) * (1 + a ^ 2)) / ((1 - a * b) * (1 + c * a)) := by
    field_simp [h1, h2]
    ring

  have eq2 : (1 - (a + b) / (1 - a * b) * (c - a) / (1 + c * a)) =
      ((1 + a ^ 2) * (1 - b * c)) / ((1 - a * b) * (1 + c * a)) := by
    field_simp [h1, h2]
    ring

  rw [eq1, eq2]

  -- cancel (1 - a^2 * b * c) and (1 - a * b) * (1 + c * a) terms.
  have h5 : (1 - a * b) * (1 + c * a) ≠ 0 := by
    apply mul_ne_zero
    exact h1
    exact h2

  have h7 : ((1 + a ^ 2) : ℝ) ≠ 0 := by
    have h8 : (1 + a ^ 2 : ℝ) > 0 := by
      have : a ^ 2 ≥ 0 := sq_nonneg a
      nlinarith
    nlinarith
  -- Now expression dividing substitute (b + c) * (1 + a ^ 2) and (1 + a ^ 2) * (1 - b * c) in appropriate terms.
  field_simp [h5, h7, h4]
  <;> ring