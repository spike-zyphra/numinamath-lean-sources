import Mathlib

theorem number_theory_115481 : Set.Infinite {(x, y, z, t) : ℕ × ℕ × ℕ × ℕ | x^2 + y^2 = 5 * (z^2 + t^2)} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (n + 1, 2 * (n + 1), n + 1, (0 : ℕ)))
  · -- Show that the function is injective
    intro n m
    simp [Prod.ext_iff] at *
    all_goals omega
  · -- Show that all elements produced by f are in the set
    intro n
    simp [Prod.ext_iff]
    all_goals
      ring_nf
      <;> norm_num