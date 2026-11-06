import Mathlib

theorem number_theory_275269 :
    Set.Infinite {(a, b, c, x, y) : ℤ × ℤ × ℤ × ℤ × ℤ | a + b + c = x + y ∧ a^3 + b^3 + c^3 = x^3 + y^3 ∧ ∃ d, b = a + d ∧ c = b + d} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (k : ℕ) => ((k : ℤ), (0 : ℤ), (-k : ℤ), (k : ℤ), (-k : ℤ)))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    <;> omega
  · -- Show all elements in the image of f are solutions
    intro n
    simp [Prod.ext_iff] at *
    all_goals
      use (-(n : ℤ))
      all_goals
        ring_nf