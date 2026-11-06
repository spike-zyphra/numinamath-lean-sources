import Mathlib

theorem number_theory_283330 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x ^ 2 + y ^ 5 = z ^ 3 ∧ x * y * z ≠ 0} := by

  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => ( (2 : ℤ)^(15 * t + 10), (2 : ℤ)^(6 * t + 4), (2 : ℤ)^(10 * t + 7) ) )
  · -- Show f is injective
    intro t s h
    simp [Prod.ext_iff] at h
    linarith
  · -- Show that all elements produced by f are in the set
    intro t
    simp [Prod.ext_iff]
    all_goals
      ring_nf