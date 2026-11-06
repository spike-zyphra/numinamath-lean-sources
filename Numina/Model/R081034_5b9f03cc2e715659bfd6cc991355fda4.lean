import Mathlib

theorem number_theory_300115 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x^2 + y^2 - z^2 = 1997} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (999 - 2 * (n : ℤ) ^ 2, 2 * (n : ℤ), 998 - 2 * (n : ℤ) ^ 2))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that all elements of the image are in the set
    intro n
    simp [Prod.ext_iff]
    ring_nf