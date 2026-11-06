import Mathlib

theorem number_theory_71086 : {(x, y, z) : ℤ × ℤ × ℤ | x * y * z ≠ 0 ∧ x ^ 2 + y ^ 5 = z ^ 3}.Infinite := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (2 ^ (5 * (3 * t + 2) : ℕ), 2 ^ (6 * t + 4 : ℕ), 2 ^ (10 * t + 7 : ℕ)))
  · -- Show f is injective
    intro t s h
    simp [Prod.ext_iff] at h 
    all_goals omega
  · -- Show that all elements of f are in the set
    intro t 
    simp [Prod.ext_iff] 
    all_goals ring_nf