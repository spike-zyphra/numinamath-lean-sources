import Mathlib

theorem algebra_239319 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x^2 + y^2 + z^2 = x^3 + y^3 + z^3} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (1 + 2 * ((n : ℤ) : ℤ)^2, (n : ℤ) * (1 + 2 * ((n : ℤ) : ℤ)^2), - (n : ℤ) * (1 + 2 * ((n : ℤ) : ℤ)^2)))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that all elements of f belong to the set
    intro n
    simp [Prod.ext_iff]
    ring_nf