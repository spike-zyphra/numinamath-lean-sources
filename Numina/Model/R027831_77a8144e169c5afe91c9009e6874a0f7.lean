import Mathlib

theorem number_theory_207390 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x ^ 3 + y ^ 3 + z ^ 3 = 2} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (1 + 6 * (n : ℤ) ^ 3, 1 - 6 * (n : ℤ) ^ 3, -6 * (n : ℤ) ^ 2))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    omega
  · -- Show all elements of f are in the set
    intro n
    simp [Prod.ext_iff]
    ring_nf