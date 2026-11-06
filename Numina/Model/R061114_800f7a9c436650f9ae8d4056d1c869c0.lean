import Mathlib

theorem algebra_280009 : {(x, y, z) : ℤ × ℤ × ℤ | x^2 + y^2 + z^2 = x^3 + y^3 + z^3}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => ( (n : ℤ) * (2 * (n : ℤ)^2 + 1), - (n : ℤ) * (2 * (n : ℤ)^2 + 1), 2 * (n : ℤ)^2 + 1))
  · -- Show that f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    linarith
  · -- Show that for all n, f(n) is in the set
    intro n
    simp [Prod.ext_iff]
    ring_nf
    <;> nlinarith