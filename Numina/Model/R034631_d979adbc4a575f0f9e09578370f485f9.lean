import Mathlib

theorem algebra_281449 (a b : ℝ) :
    {x : ℝ | x^2 - 2*(a^2+b^2)*x + (a^2-b^2)^2 = 0} = {(a+b)^2, (a-b)^2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x^2 - 2*(a^2+b^2)*x + (a^2-b^2)^2 = 0, prove x ∈ {(a+b)^2, (a-b)^2}
    intro h
    have h1 : (x - (a + b)^2) * (x - (a - b)^2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h1) with h2 h3
    · -- Assume h2: x - (a+b)^2 = 0
      left
      linarith
    · -- Assume h3: x - (a-b)^2 = 0 
      right
      linarith 
  · -- Assume x ∈ {(a+b)^2, (a-b)^2}, prove x^2 - 2*(a^2+b^2)*x + (a^2-b^2)^2 = 0 
    rintro (h | h)
    · -- Assume x = (a+b)^2 
      rw [h]
      nlinarith
    · -- Assume x = (a-b)^2 
      rw [h]
      nlinarith