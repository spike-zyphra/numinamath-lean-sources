import Mathlib

theorem number_theory_116916 :
    Set.Infinite {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x^3 + y^3 = z^2} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => ( (n + 1)^2, 2 * (n + 1)^2, 3 * (n + 1)^3))
  · -- Show f is injective
    intro n m h_eq
    simp [Prod.ext_iff] at h_eq 
    omega
  · -- Show that for all n, f(n) is in the set
    intro n 
    simp [Prod.ext_iff]
    all_goals
      norm_num
      <;> ring_nf
      <;> omega