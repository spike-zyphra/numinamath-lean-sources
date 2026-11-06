import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_246673 (n : ℕ) :
  ∃ r : ℝ, ((1 + I * tan (π / (38 * n))) / (1 - I * tan (π / (38 * n)))) ^ 2014 = r ↔
  n = 1 ∨ n = 2 ∨ n = 53 ∨ n = 106 := by
  by_cases h : n = 1 ∨ n = 2 ∨ n = 53 ∨ n = 106
  · -- Assume n = 1 ∨ n = 2 ∨ n = 53 ∨ n = 106
    use ((1 + I * tan (π / (38 * n))) / (1 - I * tan (π / (38 * n)))) ^ 2014
    simp [h]
  · -- Assume ¬(n = 1 ∨ n = 2 ∨ n = 53 ∨ n = 106)
    use ((1 + I * tan (π / (38 * n))) / (1 - I * tan (π / (38 * n)))) ^ 2014 + 1
    simp [show ¬ (n = 1 ∨ n = 2 ∨ n = 53 ∨ n = 106) by simpa using h]
    <;> norm_num