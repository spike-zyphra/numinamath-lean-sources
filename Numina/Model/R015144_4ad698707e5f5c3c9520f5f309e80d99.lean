import Mathlib

theorem number_theory_186575 : Set.Infinite {(x, y, z) : ℕ × ℕ × ℕ | x^2 + y^3 = z^2} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (0, (t : ℕ) ^ 2, (t : ℕ) ^ 3))
  · -- Show f is injective
    intro t s h
    simp [Prod.ext_iff] at h ⊢
    all_goals
      omega
  · -- Show that for all t, f(t) is in the set
    intro t
    simp [Prod.ext_iff]
    all_goals
      ring