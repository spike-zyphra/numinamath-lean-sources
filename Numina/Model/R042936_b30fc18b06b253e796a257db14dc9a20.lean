import Mathlib

theorem number_theory_267857 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x ^ 2 + y ^ 5 = z ^ 3 ∧ x * y * z ≠ 0} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (2^(10 + 15 * t), 2^(4 + 6 * t), 2^(7 + 10 * t)))
  · -- Show f is injective
    intro t s h 
    simp [Prod.ext_iff] at h 
    all_goals 
      omega 
  · -- Show that all elements produced by f are in the set
    intro t
    simp [Prod.ext_iff]
    all_goals 
      ring_nf
      <;> norm_num