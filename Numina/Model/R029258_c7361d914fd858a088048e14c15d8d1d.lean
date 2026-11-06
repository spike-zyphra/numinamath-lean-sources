import Mathlib

theorem number_theory_88566 : Set.Infinite {(a, b, c) : ℤ × ℤ × ℤ | a^2 + b^2 = c^2 + 3} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (2 * (n : ℤ), 2 * ((n : ℤ)^2) - 2, 2 * ((n : ℤ)^2) - 1))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that for all n, f n is in the set
    intro n
    simp [Prod.ext_iff]
    all_goals
    ring_nf
    <;> omega