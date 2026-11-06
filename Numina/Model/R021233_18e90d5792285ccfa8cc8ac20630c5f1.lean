import Mathlib

theorem number_theory_7793 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x^2 + y^5 = z^3 ∧ x * y * z ≠ 0} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (2 ^ (15 * t + 10), 2 ^ (6 * t + 4), 2 ^ (10 * t + 7)))
  · -- Show f is injective 
    intro t s h 
    simp [Prod.ext_iff] at h 
    omega 
  · -- Show all elements in the image of f satisfy the condition 
    intro t 
    simp [Prod.ext_iff] 
    all_goals
      ring_nf
      <;> norm_num