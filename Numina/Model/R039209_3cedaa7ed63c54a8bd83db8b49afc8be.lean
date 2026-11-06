import Mathlib

theorem algebra_3956 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x^5+y^5+z^5=x^4+y^4+z^4} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (1 + 2 * (n : ℤ)^4, (n : ℤ) * (1 + 2 * (n : ℤ)^4), - (n : ℤ) * (1 + 2 * (n : ℤ)^4)))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    norm_cast at h ⊢
    all_goals linarith
  · -- Show that for all n, f(n) is indeed a solution
    intro n
    simp [Prod.ext_iff]
    ring_nf
    <;> norm_num
    <;> ring_nf
    <;> norm_num