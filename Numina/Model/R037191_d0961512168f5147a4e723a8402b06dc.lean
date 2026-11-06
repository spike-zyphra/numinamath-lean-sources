import Mathlib

  theorem algebra_186724 : 
  {x : ℝ | (x + 3)^3 - (x + 1)^3 = 56} = {1, -5} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume (x + 3)^3 - (x + 1)^3 = 56, prove x = 1 ∨ x = -5
    intro h
    have eq1 : (x + 3) ^ 3 - (x + 1) ^ 3 = 56 := by linarith
    have eq2 : (x + 3) ^ 3 - (x + 1) ^ 3 = 6 * x^2 + 24 * x + 26 := by
      ring
    rw [eq2] at eq1
    have eq3 : 6 * x^2 + 24 * x + 26 = 56 := by linarith
    have eq4 : 6 * x^2 + 24 * x - 30 = 0 := by linarith
    have eq5 : x^2 + 4 * x - 5 = 0 := by
      nlinarith 
    have eq6 : (x - 1) * (x + 5) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 eq6) with h1 h2
    · -- Case where x - 1 = 0, so x = 1
      left
      linarith 
    · -- Case where x + 5 = 0, so x = -5
      right
      linarith 
  · -- Assume x = 1 ∨ x = -5, prove (x + 3)^3 - (x + 1)^3 = 56
    rintro (h | h)
    · -- Case where x = 1 
      rw [h]
      norm_num 
    · -- Case where x = -5 
      rw [h]
      norm_num