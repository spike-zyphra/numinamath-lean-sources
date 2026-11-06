import Mathlib

theorem number_theory_158811 :
    {(x, y, z) : ℕ × ℕ × ℕ | 0 < x ∧ 0 < y ∧ 0 < z ∧ (x^2 + x + 1) * (y^2 + y + 1) = (z^2 + z + 1)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (n + 1, n + 2, (n + 2 : ℕ) ^ 2))
  · -- Show that the function f is injective.
    intro n m h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that all elements in the image of f are in the set.
    intro n
    simp [Prod.ext_iff]
    all_goals
    ring_nf