import Mathlib

theorem number_theory_154423 : Set.Infinite {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x ^ 7 + y ^ 8 = z ^ 9} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (2 ^ (32 + 72 * t), 2 ^ (28 + 63 * t), 2 ^ (25 + 56 * t)))
  · -- Show that the function f is injective.
    intro t1 t2 h
    simp [Prod.ext_iff] at h 
    omega
  · -- Show that all elements of the function f are in the set.
    intro t
    simp [Prod.ext_iff]
    all_goals
      ring_nf