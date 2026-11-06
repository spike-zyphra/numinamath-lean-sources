import Mathlib

theorem number_theory_108589 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x ^ 2 + y ^ 2 - z ^ 2 = 1997} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (2 * (t : ℤ) ^ 2 - 999, 2 * (t : ℤ), 2 * (t : ℤ) ^ 2 - 998))
  · -- Show f is injective
    intro t s h
    simp [Prod.ext_iff] at h 
    omega
  · -- Show that all elements of f are in the set
    intro t 
    simp [Prod.ext_iff]
    all_goals
    ring_nf