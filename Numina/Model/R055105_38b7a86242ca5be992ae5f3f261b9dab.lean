import Mathlib

theorem number_theory_236300 : ¬Set.Finite {(x, y, z) : ℕ × ℕ × ℕ | x^3 + y^4 = z^5} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ n => (2 ^ (8 + 20 * n), 2 ^ (6 + 15 * n), 2 ^ (5 + 12 * n)))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    linarith
  · -- Show that ∀ n, f(n) is in the set
    intro n
    simp [Prod.ext_iff]
    ring_nf
    <;> ring_nf
    <;> omega