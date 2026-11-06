import Mathlib

theorem number_theory_151243 : Set.Infinite {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ 1 + x ^ 2 + y ^ 2 = z ^ 2} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (2 * ((t + 1) : ℕ) ^ 2, 2 * ((t + 1) : ℕ), 2 * ((t + 1) : ℕ) ^ 2 + 1))
  · -- Show f is injective
    intro t1 t2 h
    simp [Prod.ext_iff] at h 
    omega
  · -- Show that all elements of the image are in the set
    intro t 
    simp [Prod.ext_iff]
    all_goals
      ring_nf
      <;> omega