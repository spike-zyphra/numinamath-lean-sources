import Mathlib

theorem algebra_192021 : Set.Infinite {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x^2 + y^2 = x^3} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => ( (n + 1) ^ 2 + 1, (n + 1) * ((n + 1) ^ 2 + 1) ) )
  · -- Show the function is injective.
    intro n m h
    simp [Prod.ext_iff] at h 
    omega 
  · -- Show that for all n, f(n) is in the set.
    intro n 
    simp [Prod.ext_iff] 
    all_goals
      ring_nf