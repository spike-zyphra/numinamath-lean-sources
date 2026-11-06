import Mathlib

theorem number_theory_1689 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x ^ 2 + y ^ 2 = z ^ 2 + 3} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (2 * (n : ℤ), 2 * (n : ℤ)^2 - 2, 2 * (n : ℤ)^2 - 1))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    linarith
  · -- Show that for all n, f(n) is in the set
    intro n
    simp [Prod.ext_iff]
    ring_nf
    <;> norm_num
    <;> ring_nf <;> norm_num