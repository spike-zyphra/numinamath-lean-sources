import Mathlib

theorem number_theory_39553 :
    Set.Infinite {(n, x, y, z) : ℕ × ℕ × ℕ × ℕ | 0 < n ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 / n : ℚ) = 1 / x + 1 / y + 1 / z} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (k : ℕ) => (2 * k + 2, 2 * k + 2, 2 * k + 2, k + 1))
  · -- Show f is injective
    intro k l h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that all elements produced by f are in the set
    intro k
    simp [Prod.ext_iff]
    all_goals
    field_simp
    <;> ring_nf <;> field_simp
    <;> ring_nf