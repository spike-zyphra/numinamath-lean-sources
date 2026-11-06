import Mathlib

theorem number_theory_293672 :
    Set.Infinite {(a, b, c, d, e) : ℕ × ℕ × ℕ × ℕ × ℕ |
      a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ e > 0 ∧
      a^3 + b^5 + c^7 + d^11 = e^13} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (2 ^ (5005 * t + 385), 2 ^ (3003 * t + 231), 2 ^ (2145 * t + 165), 2 ^ (1365 * t + 105), 2 ^ (1155 * t + 89)))
  · -- Show f is injective
    intro t1 t2 h
    simp [Prod.ext_iff] at h
    all_goals
    omega
  · -- Show all elements in the image of f satisfy the property
    intro t
    simp [Prod.ext_iff]
    all_goals
    ring_nf